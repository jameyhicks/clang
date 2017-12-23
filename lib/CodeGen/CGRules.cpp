//===--- CGBlocks.cpp - Emit LLVM Code for declarations ---------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This contains code to emit blocks.
//
//===----------------------------------------------------------------------===//

#include "CGBlocks.h"
#include "CGDebugInfo.h"
#include "CGObjCRuntime.h"
#include "CodeGenFunction.h"
#include "CodeGenModule.h"
#include "clang/CodeGen/ConstantInitBuilder.h"
#include "clang/AST/DeclObjC.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Module.h"
#include <algorithm>
#include <cstdio>

using namespace clang;
using namespace CodeGen;

CGBlockInfo::CGBlockInfo(const BlockDecl *block, StringRef name)
  : Name(name), CXXThisIndex(0), CanBeGlobal(false), NeedsCopyDispose(false),
    HasCXXObject(false), UsesStret(false), HasCapturedVariableLayout(false),
    LocalAddress(Address::invalid()), StructureType(nullptr), Block(block),
    DominatingIP(nullptr) {

  // Skip asm prefix, if any.  'name' is usually taken directly from
  // the mangled name of the enclosing function.
  if (!name.empty() && name[0] == '\01')
    name = name.substr(1);
}

/// buildBlockDescriptor - Build the block descriptor meta-data for a block.
/// buildBlockDescriptor is accessed from 5th field of the Block_literal
/// meta-data and contains stationary information about the block literal.
/// Its definition will have 4 (or optinally 6) words.
/// \code
/// struct Block_descriptor {
///   unsigned long reserved;
///   unsigned long size;  // size of Block_literal metadata in bytes.
///   void *copy_func_helper_decl;  // optional copy helper.
///   void *destroy_func_decl; // optioanl destructor helper.
///   void *block_method_encoding_address; // @encode for block literal signature.
///   void *block_layout_info; // encoding of captured block variables.
/// };
/// \endcode
static llvm::Constant *buildBlockDescriptor(CodeGenModule &CGM,
                                            const CGBlockInfo &blockInfo) {
  ASTContext &C = CGM.getContext(); 
  llvm::IntegerType *ulong = cast<llvm::IntegerType>(CGM.getTypes().ConvertType(C.UnsignedLongTy));
  llvm::PointerType *i8p = CGM.VoidPtrTy; 
  ConstantInitBuilder builder(CGM);
  auto elements = builder.beginStruct(); 
  // reserved
  elements.addInt(ulong, 0); 
  // Size
  // FIXME: What is the right way to say this doesn't fit?  We should give
  // a user diagnostic in that case.  Better fix would be to change the
  // API to size_t.
  elements.addInt(ulong, blockInfo.BlockSize.getQuantity()); 
  // Signature.  Mandatory ObjC-style method descriptor @encode sequence.
  std::string typeAtEncoding = CGM.getContext().getObjCEncodingForBlock(blockInfo.getBlockExpr());
  elements.add(llvm::ConstantExpr::getBitCast( CGM.GetAddrOfConstantCString(typeAtEncoding).getPointer(), i8p));
  elements.addNullPointer(i8p);
  unsigned AddrSpace = 0;
  llvm::GlobalVariable *global = elements.finishAndCreateGlobal("__block_descriptor_tmp",
          CGM.getPointerAlign(), /*constant*/ true, llvm::GlobalValue::InternalLinkage, AddrSpace); 
  return llvm::ConstantExpr::getBitCast(global, CGM.getBlockDescriptorType());
}

/*
  Purely notional variadic template describing the layout of a block.

  template <class _ResultType, class... _ParamTypes, class... _CaptureTypes>
  struct Block_literal {
    /// Initialized to one of:
    ///   extern void *_NSConcreteStackBlock[];
    ///   extern void *_NSConcreteGlobalBlock[];
    ///
    /// In theory, we could start one off malloc'ed by setting
    /// BLOCK_NEEDS_FREE, giving it a refcount of 1, and using
    /// this isa:
    ///   extern void *_NSConcreteMallocBlock[];
    struct objc_class *isa;

    /// These are the flags (with corresponding bit number) that the
    /// compiler is actually supposed to know about.
    ///  25. BLOCK_HAS_COPY_DISPOSE - indicates that the block
    ///   descriptor provides copy and dispose helper functions
    ///  26. BLOCK_HAS_CXX_OBJ - indicates that there's a captured
    ///   object with a nontrivial destructor or copy constructor
    ///  28. BLOCK_IS_GLOBAL - indicates that the block is allocated
    ///   as global memory
    ///  29. BLOCK_USE_STRET - indicates that the block function
    ///   uses stret, which objc_msgSend needs to know about
    ///  30. BLOCK_HAS_SIGNATURE - indicates that the block has an
    ///   @encoded signature string
    /// And we're not supposed to manipulate these:
    ///  24. BLOCK_NEEDS_FREE - indicates that the block has been moved
    ///   to malloc'ed memory
    ///  27. BLOCK_IS_GC - indicates that the block has been moved to
    ///   to GC-allocated memory
    /// Additionally, the bottom 16 bits are a reference count which
    /// should be zero on the stack.
    int flags;

    /// Reserved;  should be zero-initialized.
    int reserved;

    /// Function pointer generated from block literal.
    _ResultType (*invoke)(Block_literal *, _ParamTypes...);

    /// Block description metadata generated from block literal.
    struct Block_descriptor *block_descriptor;

    /// Captured values follow.
    _CapturesTypes captures...;
  };
 */

namespace {
  /// A chunk of data that we actually have to capture in the block.
  struct BlockLayoutChunk {
    CharUnits Alignment;
    CharUnits Size;
    Qualifiers::ObjCLifetime Lifetime;
    const BlockDecl::Capture *Capture; // null for 'this'
    llvm::Type *Type;
    QualType FieldType;

    BlockLayoutChunk(CharUnits align, CharUnits size,
                     Qualifiers::ObjCLifetime lifetime,
                     const BlockDecl::Capture *capture,
                     llvm::Type *type, QualType fieldType)
      : Alignment(align), Size(size), Lifetime(lifetime),
        Capture(capture), Type(type), FieldType(fieldType) {}

    /// Tell the block info that this chunk has the given field index.
    void setIndex(CGBlockInfo &info, unsigned index, CharUnits offset) {
      if (!Capture) {
        info.CXXThisIndex = index;
        info.CXXThisOffset = offset;
      } else {
        auto C = CGBlockInfo::Capture::makeIndex(index, offset, FieldType);
        info.Captures.insert({Capture->getVariable(), C});
      }
    }
  };

  /// Order by 1) all __strong together 2) next, all byfref together 3) next,
  /// all __weak together. Preserve descending alignment in all situations.
  bool operator<(const BlockLayoutChunk &left, const BlockLayoutChunk &right) {
    if (left.Alignment != right.Alignment)
      return left.Alignment > right.Alignment;

    auto getPrefOrder = [](const BlockLayoutChunk &chunk) {
      if (chunk.Capture && chunk.Capture->isByRef())
        return 1;
      if (chunk.Lifetime == Qualifiers::OCL_Strong)
        return 0;
      if (chunk.Lifetime == Qualifiers::OCL_Weak)
        return 2;
      return 3;
    };

    return getPrefOrder(left) < getPrefOrder(right);
  }
} // end anonymous namespace

/// Determines if the given type is safe for constant capture in C++.
static bool isSafeForCXXConstantCapture(QualType type) {
  const RecordType *recordType = type->getBaseElementTypeUnsafe()->getAs<RecordType>();

  // Only records can be unsafe.
  if (!recordType) return true;

  const auto *record = cast<CXXRecordDecl>(recordType->getDecl());

  // Maintain semantics for classes with non-trivial dtors or copy ctors.
  if (!record->hasTrivialDestructor()) return false;
  if (record->hasNonTrivialCopyConstructor()) return false;

  // Otherwise, we just have to make sure there aren't any mutable
  // fields that might have changed since initialization.
  return !record->hasMutableFields();
}

/// It is illegal to modify a const object after initialization.
/// Therefore, if a const object has a constant initializer, we don't
/// actually need to keep storage for it in the block; we'll just
/// rematerialize it at the start of the block function.  This is
/// acceptable because we make no promises about address stability of
/// captured variables.
static llvm::Constant *tryCaptureAsConstant(CodeGenModule &CGM,
                                            CodeGenFunction *CGF,
                                            const VarDecl *var) {
  // Return if this is a function parameter. We shouldn't try to
  // rematerialize default arguments of function parameters.
  if (isa<ParmVarDecl>(var))
    return nullptr;

  QualType type = var->getType();

  // We can only do this if the variable is const.
  if (!type.isConstQualified()) return nullptr;

  // Furthermore, in C++ we have to worry about mutable fields:
  // C++ [dcl.type.cv]p4:
  //   Except that any class member declared mutable can be
  //   modified, any attempt to modify a const object during its
  //   lifetime results in undefined behavior.
  if (CGM.getLangOpts().CPlusPlus && !isSafeForCXXConstantCapture(type))
    return nullptr;

  // If the variable doesn't have any initializer (shouldn't this be
  // invalid?), it's not clear what we should do.  Maybe capture as
  // zero?
  const Expr *init = var->getInit();
  if (!init) return nullptr;

  return CGM.EmitConstantInit(*var, CGF);
}

/// Get the low bit of a nonzero character count.  This is the
/// alignment of the nth byte if the 0th byte is universally aligned.
static CharUnits getLowBit(CharUnits v) {
  return CharUnits::fromQuantity(v.getQuantity() & (~v.getQuantity() + 1));
}

static void initializeForBlockHeader(CodeGenModule &CGM, CGBlockInfo &info,
                             SmallVectorImpl<llvm::Type*> &elementTypes) {
  // The header is basically 'struct { void *; int; int; void *; void *; }'.
  // Assert that that struct is packed.
  assert(CGM.getIntSize() <= CGM.getPointerSize());
  assert(CGM.getIntAlign() <= CGM.getPointerAlign());
  assert((2 * CGM.getIntSize()).isMultipleOf(CGM.getPointerAlign()));

  info.BlockAlign = CGM.getPointerAlign();
  info.BlockSize = 3 * CGM.getPointerSize() + 2 * CGM.getIntSize();

  assert(elementTypes.empty());
  elementTypes.push_back(CGM.VoidPtrTy);
  elementTypes.push_back(CGM.IntTy);
  elementTypes.push_back(CGM.IntTy);
  elementTypes.push_back(CGM.VoidPtrTy);
  elementTypes.push_back(CGM.getBlockDescriptorType());
}

static QualType getCaptureFieldType(const CodeGenFunction &CGF,
                                    const BlockDecl::Capture &CI) {
  const VarDecl *VD = CI.getVariable();

  // If the variable is captured by an enclosing block or lambda expression,
  // use the type of the capture field.
  if (CGF.BlockInfo && CI.isNested())
    return CGF.BlockInfo->getCapture(VD).fieldType();
  if (auto *FD = CGF.LambdaCaptureFields.lookup(VD))
    return FD->getType();
  return VD->getType();
}

/// Compute the layout of the given block.  Attempts to lay the block
/// out with minimal space requirements.
static void computeBlockInfo(CodeGenModule &CGM, CodeGenFunction *CGF,
                             CGBlockInfo &info) {
  ASTContext &C = CGM.getContext();
  const BlockDecl *block = info.getBlockDecl();

  SmallVector<llvm::Type*, 8> elementTypes;
  initializeForBlockHeader(CGM, info, elementTypes);

  if (!block->hasCaptures()) {
    info.StructureType = llvm::StructType::get(CGM.getLLVMContext(), elementTypes, true);
    info.CanBeGlobal = true;
    return;
  }
  
  // Collect the layout chunks.
  SmallVector<BlockLayoutChunk, 16> layout;
  layout.reserve(block->capturesCXXThis() +
                 (block->capture_end() - block->capture_begin()));

  CharUnits maxFieldAlign;

  // First, 'this'.
  if (block->capturesCXXThis()) {
    assert(CGF && CGF->CurFuncDecl && isa<CXXMethodDecl>(CGF->CurFuncDecl) &&
           "Can't capture 'this' outside a method");
    QualType thisType = cast<CXXMethodDecl>(CGF->CurFuncDecl)->getThisType(C);

    // Theoretically, this could be in a different address space, so
    // don't assume standard pointer size/align.
    llvm::Type *llvmType = CGM.getTypes().ConvertType(thisType);
    std::pair<CharUnits,CharUnits> tinfo = CGM.getContext().getTypeInfoInChars(thisType);
    maxFieldAlign = std::max(maxFieldAlign, tinfo.second); 
    layout.push_back(BlockLayoutChunk(tinfo.second, tinfo.first, Qualifiers::OCL_None, nullptr, llvmType, thisType));
  }

  // Next, all the block captures.
  for (const auto &CI : block->captures()) {
    const VarDecl *variable = CI.getVariable();

    if (CI.isByRef()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    }

    // Otherwise, build a layout chunk with the size and alignment of
    // the declaration.
    if (llvm::Constant *constant = tryCaptureAsConstant(CGM, CGF, variable)) {
      info.Captures[variable] = CGBlockInfo::Capture::makeConstant(constant);
      continue;
    }

    // If we have a lifetime qualifier, honor it for capture purposes.
    // That includes *not* copying it if it's __unsafe_unretained.
    Qualifiers::ObjCLifetime lifetime = variable->getType().getObjCLifetime();
    if (lifetime) {
      switch (lifetime) {
      case Qualifiers::OCL_None: llvm_unreachable("impossible");
      case Qualifiers::OCL_ExplicitNone:
      case Qualifiers::OCL_Autoreleasing:
        break;

      case Qualifiers::OCL_Strong:
      case Qualifiers::OCL_Weak:
        info.NeedsCopyDispose = true;
      }

    // Block pointers require copy/dispose.  So do Objective-C pointers.
    } else if (variable->getType()->isObjCRetainableType()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    } else if (CI.hasCopyExpr()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    } else if (CGM.getLangOpts().CPlusPlus) {
      if (const CXXRecordDecl *record = variable->getType()->getAsCXXRecordDecl()) {
        if (!record->hasTrivialDestructor()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
        }
      }
    }

    QualType VT = getCaptureFieldType(*CGF, CI);
    CharUnits size = C.getTypeSizeInChars(VT);
    CharUnits align = C.getDeclAlign(variable);
    
    maxFieldAlign = std::max(maxFieldAlign, align);

    llvm::Type *llvmType = CGM.getTypes().ConvertTypeForMem(VT); 
    layout.push_back( BlockLayoutChunk(align, size, lifetime, &CI, llvmType, VT));
  }

  // If that was everything, we're done here.
  if (layout.empty()) {
    info.StructureType = llvm::StructType::get(CGM.getLLVMContext(), elementTypes, true);
    info.CanBeGlobal = true;
    return;
  }

  // Sort the layout by alignment.  We have to use a stable sort here
  // to get reproducible results.  There should probably be an
  // llvm::array_pod_stable_sort.
  std::stable_sort(layout.begin(), layout.end());
  
  // Needed for blocks layout info.
  info.BlockHeaderForcedGapOffset = info.BlockSize;
  info.BlockHeaderForcedGapSize = CharUnits::Zero();
  
  CharUnits &blockSize = info.BlockSize;
  info.BlockAlign = std::max(maxFieldAlign, info.BlockAlign);

  // Assuming that the first byte in the header is maximally aligned,
  // get the alignment of the first byte following the header.
  CharUnits endAlign = getLowBit(blockSize);

  // If the end of the header isn't satisfactorily aligned for the
  // maximum thing, look for things that are okay with the header-end
  // alignment, and keep appending them until we get something that's
  // aligned right.  This algorithm is only guaranteed optimal if
  // that condition is satisfied at some point; otherwise we can get
  // things like:
  //   header                 // next byte has alignment 4
  //   something_with_size_5; // next byte has alignment 1
  //   something_with_alignment_8;
  // which has 7 bytes of padding, as opposed to the naive solution
  // which might have less (?).
  if (endAlign < maxFieldAlign) {
    SmallVectorImpl<BlockLayoutChunk>::iterator li = layout.begin() + 1, le = layout.end(); 
    // Look for something that the header end is already
    // satisfactorily aligned for.
    for (; li != le && endAlign < li->Alignment; ++li)
      ;

    // If we found something that's naturally aligned for the end of
    // the header, keep adding things...
    if (li != le) {
      SmallVectorImpl<BlockLayoutChunk>::iterator first = li;
      for (; li != le; ++li) {
        assert(endAlign >= li->Alignment);

        li->setIndex(info, elementTypes.size(), blockSize);
        elementTypes.push_back(li->Type);
        blockSize += li->Size;
        endAlign = getLowBit(blockSize);

        // ...until we get to the alignment of the maximum field.
        if (endAlign >= maxFieldAlign) {
          break;
        }
      }
      // Don't re-append everything we just appended.
      layout.erase(first, li);
    }
  }

  assert(endAlign == getLowBit(blockSize));
  
  // At this point, we just have to add padding if the end align still
  // isn't aligned right.
  if (endAlign < maxFieldAlign) {
    CharUnits newBlockSize = blockSize.alignTo(maxFieldAlign);
    CharUnits padding = newBlockSize - blockSize;

    // If we haven't yet added any fields, remember that there was an
    // initial gap; this need to go into the block layout bit map.
    if (blockSize == info.BlockHeaderForcedGapOffset) {
      info.BlockHeaderForcedGapSize = padding;
    } 
    elementTypes.push_back(llvm::ArrayType::get(CGM.Int8Ty, padding.getQuantity()));
    blockSize = newBlockSize;
    endAlign = getLowBit(blockSize); // might be > maxFieldAlign
  }

  assert(endAlign >= maxFieldAlign);
  assert(endAlign == getLowBit(blockSize));
  // Slam everything else on now.  This works because they have
  // strictly decreasing alignment and we expect that size is always a
  // multiple of alignment.
  for (SmallVectorImpl<BlockLayoutChunk>::iterator
         li = layout.begin(), le = layout.end(); li != le; ++li) {
    if (endAlign < li->Alignment) {
      // size may not be multiple of alignment. This can only happen with
      // an over-aligned variable. We will be adding a padding field to
      // make the size be multiple of alignment.
      CharUnits padding = li->Alignment - endAlign;
      elementTypes.push_back(llvm::ArrayType::get(CGM.Int8Ty,
                                                  padding.getQuantity()));
      blockSize += padding;
      endAlign = getLowBit(blockSize);
    }
    assert(endAlign >= li->Alignment);
    li->setIndex(info, elementTypes.size(), blockSize);
    elementTypes.push_back(li->Type);
    blockSize += li->Size;
    endAlign = getLowBit(blockSize);
  }

  info.StructureType = llvm::StructType::get(CGM.getLLVMContext(), elementTypes, true);
printf("[%s:%d] STRUCTURETYPE count %d\n", __FUNCTION__, __LINE__,block->capturesCXXThis() + (block->capture_end() - block->capture_begin()));
info.StructureType->dump();
}

/// Enter the scope of a block.  This should be run at the entrance to
/// a full-expression so that the block's cleanups are pushed at the
/// right place in the stack.
static void enterBlockScope(CodeGenFunction &CGF, BlockDecl *block) {
  assert(CGF.HaveInsertPoint()); 
  // Allocate the block info and place it at the head of the list.
  CGBlockInfo &blockInfo = *new CGBlockInfo(block, CGF.CurFn->getName());
  blockInfo.NextBlockInfo = CGF.FirstBlockInfo;
  CGF.FirstBlockInfo = &blockInfo; 
  // Compute information about the layout, etc., of this block, // pushing cleanups as necessary.
  computeBlockInfo(CGF.CGM, &CGF, blockInfo); 
  // Nothing else to do if it can be global.
  if (blockInfo.CanBeGlobal) return; 
  // Make the allocation for the block.
  blockInfo.LocalAddress = CGF.CreateTempAlloca(blockInfo.StructureType, blockInfo.BlockAlign, "block"); 
  // If there are cleanups to emit, enter them (but inactive).
  if (!blockInfo.NeedsCopyDispose) return;
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
}

/// Enter a full-expression with a non-trivial number of objects to
/// clean up.  This is in this file because, at the moment, the only
/// kind of cleanup object is a BlockDecl*.
void CodeGenFunction::enterNonTrivialFullExpression(const ExprWithCleanups *E) {
  assert(E->getNumObjects() != 0);
  ArrayRef<ExprWithCleanups::CleanupObject> cleanups = E->getObjects();
  for (ArrayRef<ExprWithCleanups::CleanupObject>::iterator
         i = cleanups.begin(), e = cleanups.end(); i != e; ++i) {
    enterBlockScope(*this, *i);
  }
}

/// Find the layout for the given block in a linked list and remove it.
static CGBlockInfo *findAndRemoveBlockInfo(CGBlockInfo **head,
                                           const BlockDecl *block) {
  while (true) {
    assert(head && *head);
    CGBlockInfo *cur = *head;

    // If this is the block we're looking for, splice it out of the list.
    if (cur->getBlockDecl() == block) {
      *head = cur->NextBlockInfo;
      return cur;
    }

    head = &cur->NextBlockInfo;
  }
}

Address CodeGenFunction::GetAddrOfBlockDecl(const VarDecl *variable, bool isByRef) {
  assert(BlockInfo && "evaluating block ref without block information?");
  const CGBlockInfo::Capture &capture = BlockInfo->getCapture(variable); 
  // Handle constant captures.
  if (capture.isConstant()) return LocalDeclMap.find(variable)->second; 
  Address addr = Builder.CreateStructGEP(LoadBlockStruct(), capture.getIndex(), capture.getOffset(), "block.capture.addr"); 
  if (isByRef) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
  } 
  if (capture.fieldType()->getAs<ReferenceType>())
{
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
} 
  return addr;
}

void CodeGenFunction::setBlockContextParameter(const ImplicitParamDecl *D,
                                               unsigned argNum,
                                               llvm::Value *arg) {
  assert(BlockInfo && "not emitting prologue of block invocation function?!");
  SourceLocation StartLoc = BlockInfo->getBlockExpr()->getBody()->getLocStart();
  ApplyDebugLocation Scope(*this, StartLoc);
  // Instead of messing around with LocalDeclMap, just set the value
  // directly as BlockPointer.
  BlockPointer = Builder.CreatePointerCast( arg, BlockInfo->StructureType->getPointerTo( 0), "block");
}

/// Emit a block literal expression in the current function.
llvm::Value *CodeGenFunction::EmitBlockLiteral(const BlockExpr *blockExpr) {
  // If the block has no captures, we won't have a pre-computed
  // layout for it.
  if (!blockExpr->getBlockDecl()->hasCaptures()) {
    if (llvm::Constant *Block = CGM.getAddrOfGlobalBlockIfEmitted(blockExpr))
      return Block;
    CGBlockInfo blockInfo(blockExpr->getBlockDecl(), CurFn->getName());
    computeBlockInfo(CGM, this, blockInfo);
    blockInfo.BlockExpression = blockExpr;
    return EmitBlockLiteral(blockInfo);
  }

  // Find the block info for this block and take ownership of it.
  std::unique_ptr<CGBlockInfo> blockInfo;
  blockInfo.reset(findAndRemoveBlockInfo(&FirstBlockInfo, blockExpr->getBlockDecl())); 
  blockInfo->BlockExpression = blockExpr;
  return EmitBlockLiteral(*blockInfo);
}

llvm::Value *CodeGenFunction::EmitBlockLiteral(const CGBlockInfo &blockInfo) {
  // Using the computed layout, generate the actual block function.
  bool isLambdaConv = blockInfo.getBlockDecl()->isConversionFromLambda();
  llvm::Constant *blockFn = CodeGenFunction(CGM, true).GenerateBlockFunction(CurGD, blockInfo, LocalDeclMap, isLambdaConv);
  blockFn = llvm::ConstantExpr::getBitCast(blockFn, VoidPtrTy);
  // If there is nothing to capture, we can emit this as a global block.
  if (blockInfo.CanBeGlobal)
{
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
}
  llvm::Constant *isa = CGM.getNSConcreteStackBlock();
  isa = llvm::ConstantExpr::getBitCast(isa, VoidPtrTy);
  // Build the block descriptor.
  llvm::Constant *descriptor = buildBlockDescriptor(CGM, blockInfo);
printf("[%s:%d]BLOCKDESCRIPTOR\n", __FUNCTION__, __LINE__);
descriptor->dump();

  Address blockAddr = blockInfo.LocalAddress;
  assert(blockAddr.isValid() && "block has no address!");

  // Compute the initial on-stack block flags.
  BlockFlags flags = BLOCK_HAS_SIGNATURE;
  if (blockInfo.HasCapturedVariableLayout) flags |= BLOCK_HAS_EXTENDED_LAYOUT;
  if (blockInfo.NeedsCopyDispose) flags |= BLOCK_HAS_COPY_DISPOSE;
  if (blockInfo.HasCXXObject) flags |= BLOCK_HAS_CXX_OBJ;
  if (blockInfo.UsesStret) flags |= BLOCK_USE_STRET;

  auto projectField = [&](unsigned index, CharUnits offset, const Twine &name) -> Address {
      return Builder.CreateStructGEP(blockAddr, index, offset, name);
    };
  auto storeField = [&](llvm::Value *value, unsigned index, CharUnits offset, const Twine &name) {
      Builder.CreateStore(value, projectField(index, offset, name));
    };

  // Initialize the block header.
  {
    // We assume all the header fields are densely packed.
    unsigned index = 0;
    CharUnits offset;
    auto addHeaderField = [&](llvm::Value *value, CharUnits size, const Twine &name) {
        storeField(value, index, offset, name);
        offset += size;
        index++;
      };

    addHeaderField(isa, getPointerSize(), "block.isa");
    addHeaderField(llvm::ConstantInt::get(IntTy, flags.getBitMask()),
                   getIntSize(), "block.flags");
    addHeaderField(llvm::ConstantInt::get(IntTy, 0),
                   getIntSize(), "block.reserved");
    addHeaderField(blockFn, getPointerSize(), "block.invoke");
    addHeaderField(descriptor, getPointerSize(), "block.descriptor");
  }

  // Finally, capture all the values into the block.
  const BlockDecl *blockDecl = blockInfo.getBlockDecl();

  // First, 'this'.
  if (blockDecl->capturesCXXThis()) {
    Address addr = projectField(blockInfo.CXXThisIndex, blockInfo.CXXThisOffset,
                                "block.captured-this.addr");
    Builder.CreateStore(LoadCXXThis(), addr);
  }

  // Next, captured variables.
  for (const auto &CI : blockDecl->captures()) {
    const VarDecl *variable = CI.getVariable();
    const CGBlockInfo::Capture &capture = blockInfo.getCapture(variable);

    // Ignore constant captures.
    if (capture.isConstant()) continue;

    QualType type = capture.fieldType();

    // This will be a [[type]]*, except that a byref entry will just be
    // an i8**.
    Address blockField = projectField(capture.getIndex(), capture.getOffset(), "block.captured");

    // Compute the address of the thing we're going to move into the
    // block literal.
    Address src = Address::invalid();

    if (blockDecl->isConversionFromLambda()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    } else if (CI.isByRef()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    } else {
      DeclRefExpr declRef(const_cast<VarDecl *>(variable),
                          /*RefersToEnclosingVariableOrCapture*/ CI.isNested(),
                          type.getNonReferenceType(), VK_LValue,
                          SourceLocation());
      src = EmitDeclRefLValue(&declRef).getAddress();
printf("[%s:%d]NOTBYREF\n", __FUNCTION__, __LINE__);
declRef.dump();
    };

    // For byrefs, we just write the pointer to the byref struct into
    // the block field.  There's no need to chase the forwarding
    // pointer at this point, since we're building something that will
    // live a shorter life than the stack byref anyway.
    if (CI.isByRef()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    } else if (CI.getCopyExpr()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    } else if (type->isReferenceType()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    } else if (type.isConstQualified() &&
               type.getObjCLifetime() == Qualifiers::OCL_Strong //&&
               /*CGM.getCodeGenOpts().OptimizationLevel != 0*/) {
      llvm::Value *value = Builder.CreateLoad(src, "captured");
      Builder.CreateStore(value, blockField);

    // If this is an ARC __strong block-pointer variable, don't do a
    // block copy.
    //
    // TODO: this can be generalized into the normal initialization logic:
    // we should never need to do a block-copy when initializing a local
    // variable, because the local variable's lifetime should be strictly
    // contained within the stack block's.
    } else if (type.getObjCLifetime() == Qualifiers::OCL_Strong && type->isBlockPointerType()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    } else {
      // Fake up a new variable so that EmitScalarInit doesn't think
      // we're referring to the variable in its own initializer.
      ImplicitParamDecl BlockFieldPseudoVar(getContext(), type, ImplicitParamDecl::Other); 
      // We use one of these or the other depending on whether the // reference is nested.
      DeclRefExpr declRef(const_cast<VarDecl *>(variable),
                          /*RefersToEnclosingVariableOrCapture*/ CI.isNested(),
                          type, VK_LValue, SourceLocation()); 
      ImplicitCastExpr l2r(ImplicitCastExpr::OnStack, type, CK_LValueToRValue, &declRef, VK_RValue);
      // FIXME: Pass a specific location for the expr init so that the store is
      // attributed to a reasonable location - otherwise it may be attributed to
      // locations of subexpressions in the initialization.
      LValueBaseInfo BaseInfo(AlignmentSource::Decl, false);
      EmitExprAsInit(&l2r, &BlockFieldPseudoVar, MakeAddrLValue(blockField, type, BaseInfo), /*captured by init*/ false);
    } 
    // Activate the cleanup if layout pushed one.
    if (!CI.isByRef()) {
      EHScopeStack::stable_iterator cleanup = capture.getCleanup();
      if (cleanup.isValid())
        ActivateCleanupBlock(cleanup, blockInfo.DominatingIP);
    }
  }

  // Cast to the converted block-pointer type, which happens (somewhat
  // unfortunately) to be a pointer to function type.
  llvm::Value *result = Builder.CreatePointerCast( blockAddr.getPointer(), ConvertType(blockInfo.getBlockExpr()->getType()));

  return result;
}


llvm::Type *CodeGenModule::getBlockDescriptorType() {
  if (BlockDescriptorType)
    return BlockDescriptorType;

  llvm::Type *UnsignedLongTy = getTypes().ConvertType(getContext().UnsignedLongTy);

  // struct __block_descriptor {
  //   unsigned long reserved;
  //   unsigned long block_size;
  //
  //   // later, the following will be added
  //
  //   struct {
  //     void (*copyHelper)();
  //     void (*copyHelper)();
  //   } helpers;                // !!! optional
  //
  //   const char *signature;   // the block signature
  //   const char *layout;      // reserved
  // };
  BlockDescriptorType = llvm::StructType::create( "struct.__block_descriptor", UnsignedLongTy, UnsignedLongTy);

  // Now form a pointer to that.
  unsigned AddrSpace = 0;
  BlockDescriptorType = llvm::PointerType::get(BlockDescriptorType, AddrSpace);
  return BlockDescriptorType;
}

llvm::Type *CodeGenModule::getGenericBlockLiteralType() {
  if (GenericBlockLiteralType)
    return GenericBlockLiteralType; 
  llvm::Type *BlockDescPtrTy = getBlockDescriptorType(); 
  // struct __block_literal_generic {
  //   void *__isa;
  //   int __flags;
  //   int __reserved;
  //   void (*__invoke)(void *);
  //   struct __block_descriptor *__descriptor;
  // };
  GenericBlockLiteralType = llvm::StructType::create("struct.__block_literal_generic", VoidPtrTy, IntTy, IntTy, VoidPtrTy, BlockDescPtrTy); 
  return GenericBlockLiteralType;
}

RValue CodeGenFunction::EmitBlockCallExpr(const CallExpr *E, 
                                          ReturnValueSlot ReturnValue) {
  const BlockPointerType *BPT = E->getCallee()->getType()->getAs<BlockPointerType>(); 
  llvm::Value *BlockPtr = EmitScalarExpr(E->getCallee()); 
  unsigned AddrSpace = 0; 
  llvm::Type *BlockLiteralTy = llvm::PointerType::get(CGM.getGenericBlockLiteralType(), AddrSpace); 
  // Bitcast the callee to a block literal.
  BlockPtr = Builder.CreatePointerCast(BlockPtr, BlockLiteralTy, "block.literal"); 
  // Get the function pointer from the literal.
  llvm::Value *FuncPtr = Builder.CreateStructGEP(CGM.getGenericBlockLiteralType(), BlockPtr, 3); 
  // Add the block literal.
  CallArgList Args; 
  QualType VoidPtrQualTy = getContext().VoidPtrTy;
  llvm::Type *GenericVoidPtrTy = VoidPtrTy; 
  BlockPtr = Builder.CreatePointerCast(BlockPtr, GenericVoidPtrTy);
  Args.add(RValue::get(BlockPtr), VoidPtrQualTy); 
  QualType FnType = BPT->getPointeeType(); 
  // And the rest of the arguments.
  EmitCallArgs(Args, FnType->getAs<FunctionProtoType>(), E->arguments()); 
  // Load the function.
  llvm::Value *Func = Builder.CreateAlignedLoad(FuncPtr, getPointerAlign()); 
  const FunctionType *FuncTy = FnType->castAs<FunctionType>();
  const CGFunctionInfo &FnInfo = CGM.getTypes().arrangeBlockFunctionCall(Args, FuncTy); 
  // Cast the function pointer to the right type.
  llvm::Type *BlockFTy = CGM.getTypes().GetFunctionType(FnInfo); 
  llvm::Type *BlockFTyPtr = llvm::PointerType::getUnqual(BlockFTy);
  Func = Builder.CreateBitCast(Func, BlockFTyPtr); 
  // Prepare the callee.
  CGCallee Callee(CGCalleeInfo(), Func); 
  // And call the block.
  return EmitCall(FnInfo, Callee, ReturnValue, Args);
}

Address CodeGenFunction::LoadBlockStruct() {
  assert(BlockInfo && "not in a block invocation function!");
  assert(BlockPointer && "no block pointer set!");
  return Address(BlockPointer, BlockInfo->BlockAlign);
}

llvm::Function *
CodeGenFunction::GenerateBlockFunction(GlobalDecl GD,
                                       const CGBlockInfo &blockInfo,
                                       const DeclMapTy &ldm,
                                       bool IsLambdaConversionToBlock) {
  const BlockDecl *blockDecl = blockInfo.getBlockDecl(); 
  CurGD = GD; 
  CurEHLocation = blockInfo.getBlockExpr()->getLocEnd(); 
  BlockInfo = &blockInfo; 
  // Arrange for local static and local extern declarations to appear
  // to be local to this function as well, in case they're directly
  // referenced in a block.
  for (DeclMapTy::const_iterator i = ldm.begin(), e = ldm.end(); i != e; ++i) {
    const auto *var = dyn_cast<VarDecl>(i->first);
    if (var && !var->hasLocalStorage())
      setAddrOfLocalVar(var, i->second);
printf("[%s:%d]LDMMMMMM var %p\n", __FUNCTION__, __LINE__, var);
  } 
  // Begin building the function declaration.  
  // Build the argument list.
  FunctionArgList args; 
  // The first argument is the block pointer.  Just take it as a void* // and cast it later.
  QualType selfTy = getContext().VoidPtrTy; 
  IdentifierInfo *II = &CGM.getContext().Idents.get(".block_descriptor"); 
  ImplicitParamDecl SelfDecl(getContext(), const_cast<BlockDecl *>(blockDecl),
                             SourceLocation(), II, selfTy, ImplicitParamDecl::ObjCSelf);
  args.push_back(&SelfDecl); 
  // Now add the rest of the parameters.
  args.append(blockDecl->param_begin(), blockDecl->param_end()); 
  // Create the function declaration.
  const FunctionProtoType *fnType = blockInfo.getBlockExpr()->getFunctionType();
  const CGFunctionInfo &fnInfo = CGM.getTypes().arrangeBlockFunctionDeclaration(fnType, args);
  if (CGM.ReturnSlotInterferesWithArgs(fnInfo))
    blockInfo.UsesStret = true; 
  llvm::FunctionType *fnLLVMType = CGM.getTypes().GetFunctionType(fnInfo); 
  StringRef name = CGM.getBlockMangledName(GD, blockDecl);
  llvm::Function *fn = llvm::Function::Create( fnLLVMType, llvm::GlobalValue::InternalLinkage, name, &CGM.getModule());
  CGM.SetInternalFunctionAttributes(blockDecl, fn, fnInfo); 
  // Begin generating the function.
  StartFunction(blockDecl, fnType->getReturnType(), fn, fnInfo, args,
                blockDecl->getLocation(), blockInfo.getBlockExpr()->getBody()->getLocStart()); 
  // Okay.  Undo some of what StartFunction did.  
  // At -O0 we generate an explicit alloca for the BlockPointer, so the RA
  // won't delete the dbg.declare intrinsics for captured variables.
  llvm::Value *BlockPointerDbgLoc = BlockPointer; 
  // If we have a C++ 'this' reference, go ahead and force it into
  // existence now.
  if (blockDecl->capturesCXXThis()) {
    Address addr = Builder.CreateStructGEP(LoadBlockStruct(), blockInfo.CXXThisIndex,
                              blockInfo.CXXThisOffset, "block.captured-this");
    CXXThisValue = Builder.CreateLoad(addr, "this");
  }

  // Also force all the constant captures.
  for (const auto &CI : blockDecl->captures()) {
    const VarDecl *variable = CI.getVariable();
    const CGBlockInfo::Capture &capture = blockInfo.getCapture(variable);
    if (!capture.isConstant()) continue; 
    CharUnits align = getContext().getDeclAlign(variable);
    Address alloca = CreateMemTemp(variable->getType(), align, "block.captured-const"); 
    Builder.CreateStore(capture.getConstant(), alloca); 
    setAddrOfLocalVar(variable, alloca);
  } 
  // Save a spot to insert the debug information for all the DeclRefExprs.
  llvm::BasicBlock *entry = Builder.GetInsertBlock();
  llvm::BasicBlock::iterator entry_ptr = Builder.GetInsertPoint();
  --entry_ptr; 
  if (IsLambdaConversionToBlock)
{
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
}
  else {
    PGO.assignRegionCounters(GlobalDecl(blockDecl), fn);
    incrementProfileCounter(blockDecl->getBody());
    EmitStmt(blockDecl->getBody());
  } 
  // Remember where we were...
  llvm::BasicBlock *resume = Builder.GetInsertBlock(); 
  // Go back to the entry.
  ++entry_ptr;
  Builder.SetInsertPoint(entry, entry_ptr); 
  // And resume where we left off.
  if (resume == nullptr)
    Builder.ClearInsertionPoint();
  else
    Builder.SetInsertPoint(resume); 
  FinishFunction(cast<CompoundStmt>(blockDecl->getBody())->getRBracLoc()); 
  return fn;
}

/// Adjust the declaration of something from the blocks API.
static void configureBlocksRuntimeObject(CodeGenModule &CGM,
                                         llvm::Constant *C) {
  auto *GV = cast<llvm::GlobalValue>(C->stripPointerCasts());

  if (CGM.getTarget().getTriple().isOSBinFormatCOFF()) {
    IdentifierInfo &II = CGM.getContext().Idents.get(C->getName());
    TranslationUnitDecl *TUDecl = CGM.getContext().getTranslationUnitDecl();
    DeclContext *DC = TranslationUnitDecl::castToDeclContext(TUDecl);

    assert((isa<llvm::Function>(C->stripPointerCasts()) ||
            isa<llvm::GlobalVariable>(C->stripPointerCasts())) &&
           "expected Function or GlobalVariable");

    const NamedDecl *ND = nullptr;
    for (const auto &Result : DC->lookup(&II))
      if ((ND = dyn_cast<FunctionDecl>(Result)) ||
          (ND = dyn_cast<VarDecl>(Result)))
        break;

    // TODO: support static blocks runtime
    if (GV->isDeclaration() && (!ND || !ND->hasAttr<DLLExportAttr>())) {
      GV->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);
      GV->setLinkage(llvm::GlobalValue::ExternalLinkage);
    } else {
      GV->setDLLStorageClass(llvm::GlobalValue::DLLExportStorageClass);
      GV->setLinkage(llvm::GlobalValue::ExternalLinkage);
    }
  }

  if (!CGM.getLangOpts().BlocksRuntimeOptional)
    return;

  if (GV->isDeclaration() && GV->hasExternalLinkage())
    GV->setLinkage(llvm::GlobalValue::ExternalWeakLinkage);
}

llvm::Constant *CodeGenModule::getNSConcreteStackBlock() {
  if (NSConcreteStackBlock)
    return NSConcreteStackBlock; 
  NSConcreteStackBlock = GetOrCreateLLVMGlobal("_NSConcreteStackBlock", Int8PtrTy->getPointerTo(), nullptr);
  configureBlocksRuntimeObject(*this, NSConcreteStackBlock);
  return NSConcreteStackBlock;
}

// Anchor the vtable to this translation unit.
BlockByrefHelpers::~BlockByrefHelpers() {}

llvm::Constant *
CodeGenModule::GetAddrOfGlobalBlock(const BlockExpr *BE,
                                    StringRef Name) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
}
