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

/*
  Purely notional variadic template describing the layout of a block.

  template <class _ResultType, class... _ParamTypes, class... _CaptureTypes>
  struct Block_literal {
    /// Function pointer generated from block literal.
    _ResultType (*invoke)(Block_literal *, _ParamTypes...);
    /// Captured values follow.
    _CapturesTypes captures...;
  };
 */

/// Enter a full-expression with a non-trivial number of objects to
/// clean up.  This is in this file because, at the moment, the only
/// kind of cleanup object is a BlockDecl*.
void CodeGenFunction::enterNonTrivialFullExpression(const ExprWithCleanups *E) {
  assert(E->getNumObjects() != 0);
  ArrayRef<ExprWithCleanups::CleanupObject> cleanups = E->getObjects();
  for (auto i = cleanups.begin(), e = cleanups.end(); i != e; ++i) {
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
  // The header is basically 'struct { void *invoke; }'.
  blockInfo.BlockAlign = CGM.getPointerAlign();
  blockInfo.BlockSize = 1 * CGM.getPointerSize();
  blockInfo.BlockHeaderForcedGapOffset = blockInfo.BlockSize;
  blockInfo.BlockHeaderForcedGapSize = CharUnits::Zero(); 
  CharUnits endAlign = getLowBit(blockInfo.BlockSize); 
  elementTypes.push_back(CGM.VoidPtrTy);
  // Collect the layout chunks.
  // First, 'this'.
  QualType thisType = cast<CXXMethodDecl>(CurFuncDecl)->getThisType(CGM.getContext());
  blockInfo.CXXThisIndex = elementTypes.size();
  blockInfo.CXXThisOffset = blockInfo.BlockSize;
  elementTypes.push_back(CGM.getTypes().ConvertType(thisType));
  blockInfo.BlockSize += CGM.getContext().getTypeSizeInChars(thisType);
  endAlign = getLowBit(blockInfo.BlockSize);
  // save 'thisType', so that we can use it in Generate()
  blockInfo.Captures.insert({nullptr, CGBlockInfo::Capture::makeIndex(0, CharUnits(), thisType)});

  // Next, all the block captures.
  for (const auto &CI : block->captures()) {
    const VarDecl *variable = CI.getVariable(); 
    QualType VT = variable->getType();
    if (CI.isByRef() || VT->getAsCXXRecordDecl() || VT->isObjCRetainableType() || CI.hasCopyExpr()
     || CI.isNested() || VT->isReferenceType()) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
    }
    if (endAlign < blockInfo.BlockAlign) {
      CharUnits padding = blockInfo.BlockAlign - endAlign;
      elementTypes.push_back(llvm::ArrayType::get(CGM.Int8Ty, padding.getQuantity()));
      blockInfo.BlockSize += padding;
      endAlign = getLowBit(blockInfo.BlockSize);
    }
    assert(endAlign >= blockInfo.BlockAlign);
    blockInfo.Captures.insert({CI.getVariable(),
        CGBlockInfo::Capture::makeIndex(elementTypes.size(), blockInfo.BlockSize, VT)});
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
  if (!blockExpr->getBlockDecl()->hasCaptures()
   || blockInfo->CanBeGlobal || blockInfo->HasCapturedVariableLayout || blockInfo->HasCXXObject) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
}
  // Using the computed layout, generate the actual block function.
  llvm::Constant *blockFn = llvm::ConstantExpr::getBitCast(
      CodeGenFunction(CGM, true).GenerateBlockFunction(CurGD, *blockInfo, LocalDeclMap, false),
      VoidPtrTy);
  Address blockAddr = blockInfo->LocalAddress;
  assert(blockAddr.isValid() && "block has no address!");

  auto projectField = [&](unsigned index, CharUnits offset, const Twine &name) -> Address {
      return Builder.CreateStructGEP(blockAddr, index, offset, name);
    };
  auto storeField = [&](llvm::Value *value, unsigned index, CharUnits offset, const Twine &name) {
      Builder.CreateStore(value, projectField(index, offset, name));
    };

  // Initialize the block header.
  storeField(blockFn, 0, CharUnits(), "block.invoke"); // Function *invoke

  // Finally, capture all the values into the block.
  // First, 'this'.
  Builder.CreateStore(LoadCXXThis(),
    projectField(blockInfo->CXXThisIndex, blockInfo->CXXThisOffset, "block.captured-this.addr"));

  // Next, captured variables.
  for (const auto &CI : blockDecl->captures()) {
    const VarDecl *variable = CI.getVariable();
    const CGBlockInfo::Capture &capture = blockInfo->getCapture(variable); 
    QualType VT = capture.fieldType(); 
    // This will be a [[type]]*, except that a byref entry will just be an i8**.
    Address blockField = projectField(capture.getIndex(), capture.getOffset(), "block.captured"); 
    // Fake up a new variable so that EmitScalarInit doesn't think
    // we're referring to the variable in its own initializer.
    ImplicitParamDecl BlockFieldPseudoVar(getContext(), VT, ImplicitParamDecl::Other); 
    DeclRefExpr declRef2(const_cast<VarDecl *>(variable), /*RefersToEnclosingVariableOrCapture*/ false,
                        VT, VK_LValue, SourceLocation()); 
    ImplicitCastExpr l2r(ImplicitCastExpr::OnStack, VT, CK_LValueToRValue, &declRef2, VK_RValue);
    LValueBaseInfo BaseInfo(AlignmentSource::Decl, false);
    EmitExprAsInit(&l2r, &BlockFieldPseudoVar, MakeAddrLValue(blockField, VT, BaseInfo), /*captured by init*/ false);
    // Activate the cleanup if layout pushed one.
    EHScopeStack::stable_iterator cleanup = capture.getCleanup();
    if (cleanup.isValid())
      ActivateCleanupBlock(cleanup, blockInfo->DominatingIP);
  } 
  // Cast to the converted block-pointer type, which happens (somewhat
  // unfortunately) to be a pointer to function type.
  return Builder.CreatePointerCast( blockAddr.getPointer(),
      ConvertType(blockInfo->getBlockExpr()->getType()));
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
  const CGBlockInfo::Capture &tcap = BlockInfo->getCapture(nullptr); 
  QualType thisType = tcap.fieldType();
  Args.push_back(ParmVarDecl::Create(getContext(), const_cast<BlockDecl *>(FD), SourceLocation(),
      SourceLocation(), nullptr, thisType, /*TInfo=*/nullptr, SC_None, nullptr));

  const CGFunctionInfo &FnInfo = CGM.getTypes().arrangeBlockFunctionDeclaration(FnType, Args);
  llvm::Function *Fn = llvm::Function::Create(CGM.getTypes().GetFunctionType(FnInfo),
      llvm::GlobalValue::InternalLinkage, CGM.getBlockMangledName(GD, FD), &CGM.getModule());


  // Emit the standard function prologue.
  StartFunction(FD, FnType->getReturnType(), Fn, FnInfo, Args, FD->getLocation(), Body->getLocStart()); 

  // Generate the body of the function.
  // Force a C++ 'this' reference into existence now.
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
