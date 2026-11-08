#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct ImportMimicPass : llvm::PassInfoMixin<ImportMimicPass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunImportMimic(llvm::Module& m);

extern llvm::cl::opt<bool> MimicEnable;