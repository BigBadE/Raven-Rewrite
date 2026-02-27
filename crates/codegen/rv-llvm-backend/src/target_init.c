/**
 * LLVM Target Initialization Wrapper
 *
 * This file exposes the inline LLVMInitializeAll* functions from Target.h
 * as actual exported symbols with the LLVM_InitializeAll* names that inkwell expects.
 *
 * The LLVM C API defines LLVMInitializeAll* functions as `static inline` in the header.
 * Inkwell expects LLVM_InitializeAll* symbols (with underscore instead of CamelCase).
 * This wrapper provides those symbols.
 */

#include "llvm-c/Target.h"

#ifdef __cplusplus
extern "C" {
#endif

/* inkwell expects these exact symbol names */
void LLVM_InitializeAllTargetInfos(void) {
    LLVMInitializeAllTargetInfos();
}

void LLVM_InitializeAllTargets(void) {
    LLVMInitializeAllTargets();
}

void LLVM_InitializeAllTargetMCs(void) {
    LLVMInitializeAllTargetMCs();
}

void LLVM_InitializeAllAsmPrinters(void) {
    LLVMInitializeAllAsmPrinters();
}

void LLVM_InitializeAllAsmParsers(void) {
    LLVMInitializeAllAsmParsers();
}

void LLVM_InitializeAllDisassemblers(void) {
    LLVMInitializeAllDisassemblers();
}

#ifdef __cplusplus
}
#endif
