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
  const BlockDecl *block = blockInfo.getBlockDecl();
  blockInfo.BlockAlign = CGM.getPointerAlign();

  /// Compute the layout of the given block.
  // The header is basically
  //     'struct { void *invoke; void *STy; ... data for captures ...}'.
  SmallVector<llvm::Type*, 8> elementTypes;
  elementTypes.push_back(CGM.VoidPtrTy); // void *invoke;
  elementTypes.push_back(CGM.Int64Ty);   // void *STy;
  blockInfo.BlockSize = 2 * CGM.getPointerSize();
  CharUnits endAlign = getLowBit(blockInfo.BlockSize); 

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
    blockInfo.Captures.insert({variable,
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

  // save 'thisType', so that we can use it in Generate()
  QualType thisType = cast<CXXMethodDecl>(CurFuncDecl)->getThisType(CGM.getContext());
  blockInfo.Captures.insert({nullptr, CGBlockInfo::Capture::makeIndex(0, CharUnits(), thisType)});
  }
}

/// Emit a block literal expression in the current function.
llvm::Value *CodeGenFunction::EmitBlockLiteral(const BlockExpr *blockExpr) {
printf("[%s:%d]\n", __FUNCTION__, __LINE__);
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
  storeField(blockFn, 0, CharUnits(), "block.invoke"); // Function *invoke;
  storeField(llvm::Constant::getIntegerValue(CGM.Int64Ty,
    llvm::APInt(64, (uint64_t) blockInfo->StructureType)), 1, CharUnits(), "block.STy"); // Int64Ty STy;

  // Finally, capture all the values into the block.
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

llvm::DenseMap<int, llvm::Value *> paramMap;
Address CodeGenFunction::GetAddrOfBlockDecl(const VarDecl *variable, bool isByRef) {
  const CGBlockInfo::Capture &capture = BlockInfo->getCapture(variable); 
  if (isByRef) {
      printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
  } 
  return Address(paramMap[capture.getIndex()], BlockInfo->BlockAlign);
}

llvm::Function *
CodeGenFunction::GenerateBlockFunction(GlobalDecl GD,
                                       const CGBlockInfo &blockInfo,
                                       const DeclMapTy &ldm,
                                       bool IsLambdaConversionToBlock) {
printf("[%s:%d]\n", __FUNCTION__, __LINE__);
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
  Args.push_back(ParmVarDecl::Create(getContext(), const_cast<BlockDecl *>(FD), SourceLocation(),
      SourceLocation(), II, getContext().VoidPtrTy, /*TInfo=*/nullptr, SC_None, nullptr));
  const CGBlockInfo::Capture &tcap = BlockInfo->getCapture(nullptr); 
  QualType thisType = tcap.fieldType();
  IdentifierInfo *IThis = &CGM.getContext().Idents.get("this"); 
  Args.push_back(ParmVarDecl::Create(getContext(), const_cast<BlockDecl *>(FD), SourceLocation(),
      SourceLocation(), IThis, thisType, /*TInfo=*/nullptr, SC_None, nullptr));
  llvm::DenseMap<int, const VarDecl *> capIndex;
  for (auto capture: BlockInfo->Captures) {
      if (capture.first)  // no need to look at 'this' param
          capIndex[capture.second.getIndex()] = capture.first;
  }
  for (auto item: capIndex) {
      const CGBlockInfo::Capture &capture = BlockInfo->getCapture(item.second); 
      std::string name = item.second->getName();
      QualType paramType = capture.fieldType();
      IdentifierInfo *II = &CGM.getContext().Idents.get(name); 
      Args.push_back(ParmVarDecl::Create(getContext(), const_cast<BlockDecl *>(FD), SourceLocation(),
          SourceLocation(), II, getContext().getPointerType(paramType), /*TInfo=*/nullptr, SC_None, nullptr));
  }
  const CGFunctionInfo &FnInfo = CGM.getTypes().arrangeBlockFunctionDeclaration(FnType, Args);
  llvm::Function *Fn = llvm::Function::Create(CGM.getTypes().GetFunctionType(FnInfo),
      llvm::GlobalValue::InternalLinkage, CGM.getBlockMangledName(GD, FD), &CGM.getModule());
  auto AI = Fn->arg_begin(), AE = Fn->arg_end();
  AI++;
  CXXThisValue = AI;
  int paramIndex = 1;
  for (; AI != AE; AI++, paramIndex++)
      paramMap[paramIndex] = AI;

  // Emit the standard function prologue.
  StartFunction(FD, FnType->getReturnType(), Fn, FnInfo, Args, FD->getLocation(), Body->getLocStart()); 

  // Generate the body of the function.
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

RValue CodeGenFunction::EmitBlockCallExpr(const CallExpr *E, ReturnValueSlot ReturnValue) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
}

void CodeGenFunction::setBlockContextParameter(const ImplicitParamDecl *D, unsigned argNum, llvm::Value *arg) {
printf("[%s:%d]ZZZZZ\n", __FUNCTION__, __LINE__); exit(-1);
}
