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

/// Get the low bit of a nonzero character count.  This is the
/// alignment of the nth byte if the 0th byte is universally aligned.
static CharUnits getLowBit(CharUnits v) {
  return CharUnits::fromQuantity(v.getQuantity() & (~v.getQuantity() + 1));
}

llvm::Constant *CodeGenModule::getNSConcreteStackBlock() {
  if (NSConcreteStackBlock)
    return NSConcreteStackBlock; 
  NSConcreteStackBlock = GetOrCreateLLVMGlobal("_NSConcreteStackBlock", Int8PtrTy->getPointerTo(), nullptr);
  return NSConcreteStackBlock;
}

llvm::Type *CodeGenModule::getBlockDescriptorType() {
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
  if (BlockDescriptorType)
    return BlockDescriptorType; 
  llvm::Type *UnsignedLongTy = getTypes().ConvertType(getContext().UnsignedLongTy); 
  BlockDescriptorType = llvm::StructType::create( "struct.__block_descriptor", UnsignedLongTy, UnsignedLongTy); 
  // Now form a pointer to that.
  unsigned AddrSpace = 0;
  BlockDescriptorType = llvm::PointerType::get(BlockDescriptorType, AddrSpace);
  return BlockDescriptorType;
}

/*
  Purely notional variadic template describing the layout of a block.

  template <class _ResultType, class... _ParamTypes, class... _CaptureTypes>
  struct Block_literal {
    struct objc_class *isa;
    /// These are the flags (with corresponding bit number) that the
    /// compiler is actually supposed to know about.
    ///  30. BLOCK_HAS_SIGNATURE - indicates that the block has an
    ///   @encoded signature string
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
    const BlockDecl::Capture *Capture; // null for 'this'
    QualType FieldType;
    BlockLayoutChunk(CodeGenModule &CGM, const BlockDecl::Capture *capture, QualType fieldType)
      : Capture(capture), FieldType(fieldType) {}
  };
} // end anonymous namespace

/// Enter a full-expression with a non-trivial number of objects to
/// clean up.  This is in this file because, at the moment, the only
/// kind of cleanup object is a BlockDecl*.
void CodeGenFunction::enterNonTrivialFullExpression(const ExprWithCleanups *E) {
  assert(E->getNumObjects() != 0);
  ArrayRef<ExprWithCleanups::CleanupObject> cleanups = E->getObjects();
  for (ArrayRef<ExprWithCleanups::CleanupObject>::iterator
         i = cleanups.begin(), e = cleanups.end(); i != e; ++i) {
  /// Enter the scope of a block.  This should be run at the entrance to
  /// a full-expression so that the block's cleanups are pushed at the
  /// right place in the stack.
  assert(HaveInsertPoint()); 
  // Allocate the block info and place it at the head of the list.
  CGBlockInfo &blockInfo = *new CGBlockInfo(*i, CurFn->getName());
  blockInfo.NextBlockInfo = FirstBlockInfo;
  FirstBlockInfo = &blockInfo; 
  /// Compute the layout of the given block.
  const BlockDecl *block = blockInfo.getBlockDecl();
  SmallVector<llvm::Type*, 8> elementTypes;
  // The header is basically 'struct { void *; int; int; void *; void *; }'.
  assert(CGM.getIntSize() <= CGM.getPointerSize());
  assert(CGM.getIntAlign() <= CGM.getPointerAlign());
  assert((2 * CGM.getIntSize()).isMultipleOf(CGM.getPointerAlign())); 
  blockInfo.BlockAlign = CGM.getPointerAlign();
  blockInfo.BlockSize = 3 * CGM.getPointerSize() + 2 * CGM.getIntSize(); 
  blockInfo.BlockHeaderForcedGapOffset = blockInfo.BlockSize;
  blockInfo.BlockHeaderForcedGapSize = CharUnits::Zero(); 
  CharUnits endAlign = getLowBit(blockInfo.BlockSize); 
  elementTypes.push_back(CGM.VoidPtrTy);
  elementTypes.push_back(CGM.IntTy);
  elementTypes.push_back(CGM.IntTy);
  elementTypes.push_back(CGM.VoidPtrTy);
  elementTypes.push_back(CGM.getBlockDescriptorType());
  // Collect the layout chunks.
  // First, 'this'.
  QualType thisType = cast<CXXMethodDecl>(CurFuncDecl)->getThisType(CGM.getContext());
  blockInfo.CXXThisIndex = elementTypes.size();
  blockInfo.CXXThisOffset = blockInfo.BlockSize;
  elementTypes.push_back(CGM.getTypes().ConvertTypeForMem(thisType));
  blockInfo.BlockSize += CGM.getContext().getTypeSizeInChars(thisType);
  endAlign = getLowBit(blockInfo.BlockSize);

  // Next, all the block captures.
  for (const auto &CI : block->captures()) {
    const VarDecl *variable = CI.getVariable(); 
    QualType VT = variable->getType();
    if (CI.isByRef() || VT->getAsCXXRecordDecl() || VT->isObjCRetainableType() || CI.hasCopyExpr()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    } 
    if (endAlign < blockInfo.BlockAlign) {
      CharUnits padding = blockInfo.BlockAlign - endAlign;
      elementTypes.push_back(llvm::ArrayType::get(CGM.Int8Ty, padding.getQuantity()));
      blockInfo.BlockSize += padding;
      endAlign = getLowBit(blockInfo.BlockSize);
    }
    assert(endAlign >= blockInfo.BlockAlign);
    auto C = CGBlockInfo::Capture::makeIndex(elementTypes.size(), blockInfo.BlockSize, VT);
    blockInfo.Captures.insert({CI.getVariable(), C});
    elementTypes.push_back(CGM.getTypes().ConvertTypeForMem(VT));
    blockInfo.BlockSize += CGM.getContext().getTypeSizeInChars(VT);
    endAlign = getLowBit(blockInfo.BlockSize);
  } 
  blockInfo.StructureType = llvm::StructType::get(CGM.getLLVMContext(), elementTypes, true);
printf("[%s:%d] STRUCTURETYPE \n", __FUNCTION__, __LINE__);
blockInfo.StructureType->dump();
  // Make the allocation for the block.
  blockInfo.LocalAddress = CreateTempAlloca(blockInfo.StructureType, blockInfo.BlockAlign, "block"); 
  }
}

Address CodeGenFunction::GetAddrOfBlockDecl(const VarDecl *variable, bool isByRef) {
  const CGBlockInfo::Capture &capture = BlockInfo->getCapture(variable); 
  if (capture.isConstant() || isByRef || capture.fieldType()->getAs<ReferenceType>()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
} 
  return Builder.CreateStructGEP(LoadBlockStruct(), capture.getIndex(), capture.getOffset(), "block.capture.addr"); 
}

/// Emit a block literal expression in the current function.
llvm::Value *CodeGenFunction::EmitBlockLiteral(const BlockExpr *blockExpr) {
  if (!blockExpr->getBlockDecl()->hasCaptures()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
  }
  // Find the block info for this block and take ownership of it.
  std::unique_ptr<CGBlockInfo> blockInfo;
  CGBlockInfo **head = &FirstBlockInfo;
  const BlockDecl *blockDecl = blockExpr->getBlockDecl(); 
  while (1) {
    assert(head && *head);
    CGBlockInfo *cur = *head; 
    // If this is the block we're looking for, splice it out of the list.
    if (cur->getBlockDecl() == blockDecl) {
      *head = cur->NextBlockInfo;
      blockInfo.reset(cur);
      break;
    } 
    head = &cur->NextBlockInfo;
  }
  blockInfo->BlockExpression = blockExpr;
  if (blockInfo->CanBeGlobal || blockInfo->HasCapturedVariableLayout || blockInfo->HasCXXObject) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
}
  // Using the computed layout, generate the actual block function.
  llvm::Constant *blockFn = CodeGenFunction(CGM, true).GenerateBlockFunction(CurGD, *blockInfo, LocalDeclMap, false);
  blockFn = llvm::ConstantExpr::getBitCast(blockFn, VoidPtrTy);
  // If there is nothing to capture, we can emit this as a global block.
  // Build the block descriptor.
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
  llvm::IntegerType *ulong = cast<llvm::IntegerType>(CGM.getTypes().ConvertType(CGM.getContext().UnsignedLongTy));
  ConstantInitBuilder builder(CGM);
  auto elements = builder.beginStruct(); 
  elements.addInt(ulong, 0); 
  elements.addInt(ulong, blockInfo->BlockSize.getQuantity()); 
  // Signature.  Mandatory ObjC-style method descriptor @encode sequence.
  std::string typeAtEncoding = CGM.getContext().getObjCEncodingForBlock(blockInfo->getBlockExpr());
  elements.add(llvm::ConstantExpr::getBitCast( CGM.GetAddrOfConstantCString(typeAtEncoding).getPointer(), CGM.VoidPtrTy));
  elements.addNullPointer(CGM.VoidPtrTy);
  unsigned AddrSpace = 0;
  llvm::Constant *descriptor = llvm::ConstantExpr::getBitCast(
       elements.finishAndCreateGlobal("__block_descriptor_tmp",
          CGM.getPointerAlign(), /*constant*/ true, llvm::GlobalValue::InternalLinkage, AddrSpace),
       CGM.getBlockDescriptorType());
printf("[%s:%d]BLOCKDESCRIPTOR\n", __FUNCTION__, __LINE__);
descriptor->dump();

  Address blockAddr = blockInfo->LocalAddress;
  assert(blockAddr.isValid() && "block has no address!");

  auto projectField = [&](unsigned index, CharUnits offset, const Twine &name) -> Address {
      return Builder.CreateStructGEP(blockAddr, index, offset, name);
    };
  auto storeField = [&](llvm::Value *value, unsigned index, CharUnits offset, const Twine &name) {
      Builder.CreateStore(value, projectField(index, offset, name));
    };

  // Initialize the block header.
  // We assume all the header fields are densely packed.
  unsigned blockIndex = 0;
  CharUnits blockOffset;
  auto addHeaderField = [&](llvm::Value *value, CharUnits size, const Twine &name) {
      storeField(value, blockIndex, blockOffset, name);
      blockOffset += size;
      blockIndex++;
    }; 
  addHeaderField(llvm::ConstantExpr::getBitCast(CGM.getNSConcreteStackBlock(), VoidPtrTy), getPointerSize(), "block.isa");
  BlockFlags flags = BLOCK_HAS_SIGNATURE;
  addHeaderField(llvm::ConstantInt::get(IntTy, flags.getBitMask()), getIntSize(), "block.flags");
  addHeaderField(llvm::ConstantInt::get(IntTy, 0), getIntSize(), "block.reserved");
  addHeaderField(blockFn, getPointerSize(), "block.invoke");
  addHeaderField(descriptor, getPointerSize(), "block.descriptor");

  // Finally, capture all the values into the block.
  // First, 'this'.
  Builder.CreateStore(LoadCXXThis(),
    projectField(blockInfo->CXXThisIndex, blockInfo->CXXThisOffset, "block.captured-this.addr"));

  // Next, captured variables.
  for (const auto &CI : blockDecl->captures()) {
    const VarDecl *variable = CI.getVariable();
    const CGBlockInfo::Capture &capture = blockInfo->getCapture(variable); 
    QualType type = capture.fieldType(); 
    if (CI.isNested() || capture.isConstant() || blockDecl->isConversionFromLambda() || CI.isByRef() || CI.getCopyExpr() || type->isReferenceType()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    }
    // This will be a [[type]]*, except that a byref entry will just be an i8**.
    Address blockField = projectField(capture.getIndex(), capture.getOffset(), "block.captured"); 
    // Fake up a new variable so that EmitScalarInit doesn't think
    // we're referring to the variable in its own initializer.
    ImplicitParamDecl BlockFieldPseudoVar(getContext(), type, ImplicitParamDecl::Other); 
    DeclRefExpr declRef2(const_cast<VarDecl *>(variable), /*RefersToEnclosingVariableOrCapture*/ false,
                        type, VK_LValue, SourceLocation()); 
    ImplicitCastExpr l2r(ImplicitCastExpr::OnStack, type, CK_LValueToRValue, &declRef2, VK_RValue);
    LValueBaseInfo BaseInfo(AlignmentSource::Decl, false);
    EmitExprAsInit(&l2r, &BlockFieldPseudoVar, MakeAddrLValue(blockField, type, BaseInfo), /*captured by init*/ false);
    // Activate the cleanup if layout pushed one.
    EHScopeStack::stable_iterator cleanup = capture.getCleanup();
    if (cleanup.isValid())
      ActivateCleanupBlock(cleanup, blockInfo->DominatingIP);
  } 
  // Cast to the converted block-pointer type, which happens (somewhat
  // unfortunately) to be a pointer to function type.
  return Builder.CreatePointerCast( blockAddr.getPointer(), ConvertType(blockInfo->getBlockExpr()->getType()));
} 

void CodeGenFunction::setBlockContextParameter(const ImplicitParamDecl *D,
                                               unsigned argNum,
                                               llvm::Value *arg) {
  BlockPointer = Builder.CreatePointerCast( arg, BlockInfo->StructureType->getPointerTo( 0), "block");
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
  BlockInfo = &blockInfo; 
  const BlockDecl *FD = blockInfo.getBlockDecl(); 
  CurGD = GD; 

  FunctionArgList Args; 
  const FunctionProtoType *FnType = blockInfo.getBlockExpr()->getFunctionType();
  CurEHLocation = blockInfo.getBlockExpr()->getLocEnd(); 
  Stmt *Body = FD->getBody();
  if (FD->getNumParams() || IsLambdaConversionToBlock) {
    printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
  }
  // Begin building the function declaration.  
  // The first argument is the block pointer.  Just take it as a void* and cast it later.
  IdentifierInfo *II = &CGM.getContext().Idents.get(".block_descriptor"); 
  ImplicitParamDecl SelfDecl(getContext(), const_cast<BlockDecl *>(FD),
       SourceLocation(), II, getContext().VoidPtrTy, ImplicitParamDecl::ObjCSelf);
  Args.push_back(&SelfDecl); 
  const CGFunctionInfo &FnInfo = CGM.getTypes().arrangeBlockFunctionDeclaration(FnType, Args);
  llvm::Function *Fn = llvm::Function::Create(CGM.getTypes().GetFunctionType(FnInfo),
      llvm::GlobalValue::InternalLinkage, CGM.getBlockMangledName(GD, FD), &CGM.getModule());

  // Emit the standard function prologue.
  StartFunction(FD, FnType->getReturnType(), Fn, FnInfo, Args, FD->getLocation(), Body->getLocStart()); 

  // Generate the body of the function.
  // If we have a C++ 'this' reference, go ahead and force it into existence now.
  CXXThisValue = Builder.CreateLoad( Builder.CreateStructGEP(LoadBlockStruct(),
      blockInfo.CXXThisIndex, blockInfo.CXXThisOffset, "block.captured-this"), "this"); 
  // Save a spot to insert the debug information for all the DeclRefExprs.
  llvm::BasicBlock *entry = Builder.GetInsertBlock();
  llvm::BasicBlock::iterator entry_ptr = Builder.GetInsertPoint();
  --entry_ptr; 
  PGO.assignRegionCounters(GlobalDecl(FD), Fn);
  incrementProfileCounter(Body);
  EmitStmt(Body);
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
  FinishFunction(CurEHLocation);
  return Fn;
}

// Anchor the vtable to this translation unit.
BlockByrefHelpers::~BlockByrefHelpers() {}

llvm::Constant *
CodeGenModule::GetAddrOfGlobalBlock(const BlockExpr *BE, StringRef Name) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
}

RValue CodeGenFunction::EmitBlockCallExpr(const CallExpr *E, 
                                          ReturnValueSlot ReturnValue) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
}
