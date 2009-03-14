#include <llvm-c/Core.h>
#include <llvm-c/Analysis.h>
#include <llvm-c/ExecutionEngine.h>
#include <llvm-c/Target.h>
#include <llvm-c/Transforms/Scalar.h>


/* ------ CLISP GC harness ------ */
struct jitc_object {
  int jo_gc_mark;
  struct jitc_object* jo_next;
};
/* all JITC objects as a linked list */
static struct jitc_object *all_jitc_objects = NULL;
bool gc_drop_jitc = false;
/* mark object as used */
void gc_mark_jitc_object (void *ptr) {
  struct jitc_object *jo = (struct jitc_object*)ptr;
  jo->jo_gc_mark = 1;
}
/* scan all JITC objects and release unused objects */
void gc_scan_jitc_objects (void) {
  struct jitc_object **next = &all_jitc_objects;
  while (*next) {
    if ((*next)->jo_gc_mark) {  /* keep */
      (*next)->jo_gc_mark = 0;  /* unmark for the next GC */
      next = &((*next)->jo_next);
    } else {                      /* release */
      struct jitc_object *jo_next = (*next)->jo_next;
      free(*next);
      *next = jo_next;
    }
  }
}

/* ------ JITC Globals and init functions ------ */
#define JITC_OBJECT_TYPE LLVMPointerType(LLVMInt32Type(), 0)
#ifdef STACK_DOWN
  #define JITC_STACK_NEXT  -1
#else
  #define JITC_STACK_NEXT  1
#endif

/* C Interface to LLVM objects */
static LLVMExecutionEngineRef JITC_ENGINE = NULL;
static LLVMBuilderRef JITC_BUILDER = NULL;
static LLVMPassManagerRef JITC_PASS_MANAGER = NULL;
static LLVMModuleRef JITC_GLOBAL_MODULE = NULL;

/* Global data used by the JIT compiler */
static LLVMValueRef JITC_VALUES = NULL;
static LLVMValueRef JITC_VALUES_COUNT = NULL;
static LLVMValueRef JITC_STACK = NULL;
static LLVMValueRef JITC_NIL = NULL;
static LLVMValueRef JITC_TRUE = NULL;
static LLVMValueRef JITC_UNBOUND = NULL;
static LLVMValueRef JITC_PRINTF = NULL;
static LLVMValueRef JITC_ERROR = NULL;


/* Create the builder and initialize global variables. */
static void jitc_init_compiler () {
	// TODO: Declare as many globals as possible as constant
  char* error = NULL;
  
  JITC_GLOBAL_MODULE = LLVMModuleCreateWithName("Global Module");
  LLVMModuleProviderRef MP =
    LLVMCreateModuleProviderForExistingModule(JITC_GLOBAL_MODULE);
  if(LLVMCreateJITCompiler(&JITC_ENGINE, MP, &error)) {
    fprintf(stderr, "%s\n", error);
    LLVMDisposeMessage(error);
    abort();
  }
  JITC_BUILDER = LLVMCreateBuilder();
  JITC_PASS_MANAGER = LLVMCreateFunctionPassManager(MP);
  LLVMAddTargetData(LLVMGetExecutionEngineTargetData(JITC_ENGINE),
                    JITC_PASS_MANAGER);
  LLVMAddConstantPropagationPass(JITC_PASS_MANAGER);
  LLVMAddInstructionCombiningPass(JITC_PASS_MANAGER);
  LLVMAddPromoteMemoryToRegisterPass(JITC_PASS_MANAGER);
  LLVMAddGVNPass(JITC_PASS_MANAGER);
  LLVMAddCFGSimplificationPass(JITC_PASS_MANAGER);
  
  JITC_VALUES_COUNT = LLVMAddGlobal(JITC_GLOBAL_MODULE,
    LLVMInt32Type(), "VALUES_COUNT");
  LLVMAddGlobalMapping(JITC_ENGINE, JITC_VALUES_COUNT, &mv_count);
  JITC_VALUES = LLVMAddGlobal(JITC_GLOBAL_MODULE,
    LLVMArrayType(JITC_OBJECT_TYPE, mv_limit-1), "VALUES");
  LLVMAddGlobalMapping(JITC_ENGINE, JITC_VALUES, &mv_space);
  JITC_STACK = LLVMAddGlobal(JITC_GLOBAL_MODULE,
    LLVMPointerType(JITC_OBJECT_TYPE, 0), "STACK");
  LLVMAddGlobalMapping(JITC_ENGINE, JITC_STACK, &STACK);
  JITC_NIL = LLVMAddGlobal(JITC_GLOBAL_MODULE, LLVMInt32Type(), "NIL");
  LLVMAddGlobalMapping(JITC_ENGINE, JITC_NIL, NIL);
  LLVMSetGlobalConstant(JITC_NIL, 1);
  JITC_TRUE = LLVMAddGlobal(JITC_GLOBAL_MODULE, LLVMInt32Type(), "T");
  LLVMAddGlobalMapping(JITC_ENGINE, JITC_TRUE, T);
  LLVMSetGlobalConstant(JITC_TRUE, 1);
  JITC_UNBOUND = LLVMAddGlobal(JITC_GLOBAL_MODULE, LLVMInt32Type(), "UNBOUND");
  LLVMAddGlobalMapping(JITC_ENGINE, JITC_UNBOUND, unbound);
  LLVMSetGlobalConstant(JITC_TRUE, 1);
  LLVMTypeRef printf_args[] = {LLVMPointerType(LLVMInt8Type(), 0)};
  JITC_PRINTF = LLVMAddFunction(JITC_GLOBAL_MODULE, "printf",
                                LLVMFunctionType(LLVMInt32Type(),
                                                  printf_args, 1, 1));
  LLVMAddGlobalMapping(JITC_ENGINE, JITC_PRINTF, printf);
  LLVMTypeRef error_args[] = {LLVMInt32Type(), LLVMPointerType(LLVMInt8Type(), 0)};
  JITC_ERROR = LLVMAddFunction(JITC_GLOBAL_MODULE, "error",
                                LLVMFunctionType(LLVMInt32Type(),
                                                  error_args, 2, 1));
  LLVMAddGlobalMapping(JITC_ENGINE, JITC_ERROR, error);
  // LLVMDumpModule(JITC_GLOBAL_MODULE);
  // abort();
}

/* ------ JITC Common Operations ------ */
/* Get the offset of a field in a struct */
#define _jitc_get_offset(struc_p, f) ( ((long) (&((struc_p) 8)->f) ) - 8)
#define jitc_get_offset(struc, f) LLVMConstInt(LLVMInt64Type(), (int)The##struc(as_object(_jitc_get_offset(struc, f))), 1);

#define jitc_begin() {\
    LLVMValueRef fun = LLVMAddFunction(JITC_GLOBAL_MODULE, "fun", \
      LLVMFunctionType(LLVMVoidType(), NULL, 0, 0));\
    LLVMValueRef jitc_closure = LLVMConstIntToPtr(LLVMConstInt(LLVMInt64Type(), (int)&closure, 1), LLVMPointerType(JITC_OBJECT_TYPE, 0));\
    LLVMValueRef jitc_sp = LLVMConstIntToPtr(LLVMConstInt(LLVMInt64Type(), (int)&private_SP, 1), LLVMPointerType(LLVMPointerType(JITC_OBJECT_TYPE, 0), 0));
#define jitc_end()\
    LLVMBuildRetVoid(JITC_BUILDER);\
    LLVMRunFunction(JITC_ENGINE, fun, 0, NULL);\
    LLVMFreeMachineCodeForFunction(JITC_ENGINE, fun);\
    LLVMDeleteFunction(fun);\
  }
#define jitc_end2()\
    LLVMBuildRetVoid(JITC_BUILDER);\
    /*jitc_optimize(fun);*/\
    LLVMDumpModule(JITC_GLOBAL_MODULE);\
    abort();\
  }

/* Run the pass manager to optimize the code of a given function. */
static void jitc_optimize (LLVMValueRef fun) {
  LLVMRunFunctionPassManager(JITC_PASS_MANAGER, fun);
}

/* Add instructions that prints the given value */
static void jitc_print_value (const char *mes, LLVMValueRef val) {
  LLVMValueRef str = LLVMAddGlobal(JITC_GLOBAL_MODULE,
                                    LLVMArrayType(LLVMInt8Type(), strlen(mes)),
                                    "");
  LLVMSetInitializer(str, LLVMConstString(mes, strlen(mes), 0));
  LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), 0, 0),
                        LLVMConstInt(LLVMInt32Type(), 0, 0)};
  LLVMValueRef strptr = LLVMBuildGEP(JITC_BUILDER, str, idx, 2, "");
  LLVMValueRef printf_args[] = { strptr, val };
  LLVMBuildCall(JITC_BUILDER, JITC_PRINTF, printf_args, 2, "");
}

/* Add instructions that call clisp's error function */
static void jitc_error (condition_t type, const char *msg) {
  LLVMValueRef str = LLVMGetNamedGlobal(JITC_GLOBAL_MODULE, msg);
  if(!str) {
    str = LLVMAddGlobal(JITC_GLOBAL_MODULE,
                        LLVMArrayType(LLVMInt8Type(), strlen(msg)), msg);
    LLVMSetInitializer(str, LLVMConstString(msg, strlen(msg), 0));
  }
  
  LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), 0, 0),
                        LLVMConstInt(LLVMInt32Type(), 0, 0)};
  LLVMValueRef strptr = LLVMBuildGEP(JITC_BUILDER, str, idx, 2, "");
  LLVMValueRef error_args[] = { LLVMConstInt(LLVMInt32Type(), type, 0), strptr };
  LLVMBuildCall(JITC_BUILDER, JITC_ERROR, error_args, 2, "");
  LLVMBuildUnreachable(JITC_BUILDER);
}

/* Add intrusctions that get the address of the n-th element of the "values" table. */
static LLVMValueRef jitc_getptr_values (int n) {
  LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), 0, 0),
                        LLVMConstInt(LLVMInt32Type(), n, 0)};
  return LLVMConstGEP(JITC_VALUES, idx, 2);
}

/* Add intrusctions that get the n-th element of the "values" table. */
static LLVMValueRef jitc_get_values (int n) {
  return LLVMBuildLoad(JITC_BUILDER, jitc_getptr_values(n), "");
}

/* Add instructions that set mvcount to the given value */
static void jitc_set_mvcount (int n) {
  LLVMBuildStore(JITC_BUILDER, LLVMConstInt(LLVMInt32Type(), n, 0), JITC_VALUES_COUNT);
}

/* Add instructions that set the first element of the values table to the given value. */
static void jitc_set_values_1 (LLVMValueRef val) {
  LLVMBuildStore(JITC_BUILDER, LLVMConstInt(LLVMInt32Type(), 1, 0), JITC_VALUES_COUNT);
  LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), 0, 0),
                        LLVMConstInt(LLVMInt32Type(), 0, 0)};
  LLVMBuildStore(JITC_BUILDER, val, LLVMConstGEP(JITC_VALUES, idx, 2));
}

/* Add instructions to skip one element on the stack given the stack's pointer. */
static LLVMValueRef jitc_skip_stack (LLVMValueRef stackptr, int n) {
  LLVMValueRef stack = LLVMBuildPtrToInt(JITC_BUILDER, stackptr, LLVMInt64Type(), "");
  LLVMValueRef skips = LLVMConstInt(LLVMInt64Type(), n * sizeof(gcv_object_t), 0);
  #ifdef STACK_DOWN
    LLVMValueRef tmp = LLVMBuildAdd(JITC_BUILDER, stack, skips, "");
  #else
    LLVMValueRef tmp = LLVMBuildSub(JITC_BUILDER, stack, skips, "");
  #endif
  return LLVMBuildIntToPtr(JITC_BUILDER, tmp, LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
}

/* Add instructions to set the top of the stack to a given address. */
static void jitc_set_stack (LLVMValueRef new_stak) {
  return LLVMBuildStore(JITC_BUILDER, new_stak, JITC_STACK);
}

/* Add instructions to get an address that can traverse through the Stack. */
static LLVMValueRef jitc_getpointable_stackptr (LLVMValueRef stackptr) {
  #ifdef STACK_DOWN
    return stackptr;
  #else
    LLVMValueRef stack = LLVMBuildPtrToInt(JITC_BUILDER, stackptr, LLVMInt64Type(), "");
    LLVMValueRef skips = LLVMConstInt(LLVMInt64Type(), sizeof(gcv_object_t), 0);
    LLVMValueRef tmp = LLVMBuildSub(JITC_BUILDER, stack, skips, "");
    return LLVMBuildIntToPtr(JITC_BUILDER, tmp, LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
  #endif
}

/* Add instructions to get the address of the n-th element of the stack. */
static LLVMValueRef jitc_getptr_stack (int n) {
  LLVMValueRef top = LLVMBuildLoad(JITC_BUILDER, JITC_STACK, "TOP");
  #ifdef STACK_DOWN
    LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), n, 1)};
  #else
    LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), -1 - n, 1)};
  #endif
  return LLVMBuildGEP(JITC_BUILDER, top, idx, 1, "");
}

/* Add instructions that get the n-th element of the stack. */
static LLVMValueRef jitc_get_stack (int n) {
  return LLVMBuildLoad(JITC_BUILDER, jitc_getptr_stack(n), "");
}

/* Add instructions to get the address of the n-th element of the stack using a prefetched top. */
static LLVMValueRef jitc_getptr_stack_with (int n, LLVMValueRef top) {
  #ifdef STACK_DOWN
    LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), n, 1)};
  #else
    LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), -1 - n, 1)};
  #endif
  return LLVMBuildGEP(JITC_BUILDER, top, idx, 1, "");
}

/* Add instructions to get the n-th element of the stack using a prefetched top. */
static LLVMValueRef jitc_get_stack_with (int n, LLVMValueRef top) {
  return LLVMBuildLoad(JITC_BUILDER, jitc_getptr_stack_with(n, top), "");
}

/* Add instructions that get the address of the n-th element of a given frame. */
static LLVMValueRef jitc_getptr_frame (LLVMValueRef top, int n) {
  #ifdef STACK_DOWN
    LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), n, 1)};
  #else
    LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), -1 - n, 1)};
  #endif
  LLVMValueRef conv = LLVMBuildBitCast(JITC_BUILDER, top,
                        LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
  return LLVMBuildGEP(JITC_BUILDER, conv, idx, 1, "");
}

/* Add instructions that get the n-th element of a given frame. */
static LLVMValueRef jitc_get_frame (LLVMValueRef top, int n) {
  return LLVMBuildLoad(JITC_BUILDER, jitc_getptr_frame(top, n), "");
}

/* Add instruction that perform a pop of the stack */
static LLVMValueRef jitc_pop_stack () {
  LLVMValueRef top = LLVMBuildLoad(JITC_BUILDER, JITC_STACK, "TOP");
  LLVMBuildStore(JITC_BUILDER, jitc_getptr_stack_with(0, top), JITC_STACK);
  LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), -JITC_STACK_NEXT, 1)};
  return LLVMBuildLoad(JITC_BUILDER, LLVMBuildGEP(JITC_BUILDER, top, idx, 1, ""), "");
}

/* Add instructions that perform a push of the given value on the stack. */
static void jitc_push_stack (LLVMValueRef val) {
  LLVMValueRef top = LLVMBuildLoad(JITC_BUILDER, JITC_STACK, "TOP");
  LLVMBuildStore(JITC_BUILDER, val, jitc_getptr_stack_with(-1, top));
  LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), JITC_STACK_NEXT, 1)};
  LLVMValueRef ptr = LLVMBuildGEP(JITC_BUILDER, top, idx, 1, "NEW_TOP");
  LLVMBuildStore(JITC_BUILDER, ptr, JITC_STACK);
}

/* Add instructions that perform a push of the given value on the stack using a prefetched top. */
static void jitc_push_stack_with (LLVMValueRef val, LLVMValueRef top) {
  LLVMBuildStore(JITC_BUILDER, val, jitc_getptr_stack_with(-1, top));
  LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), JITC_STACK_NEXT, 1)};
  LLVMValueRef ptr = LLVMBuildGEP(JITC_BUILDER, top, idx, 1, "NEW_TOP");
  LLVMBuildStore(JITC_BUILDER, ptr, JITC_STACK);
}

/* Add instructions that repeat a given basic block n times. */
static void jitc_repeat (int n, LLVMBasicBlockRef repeat, LLVMBasicBlockRef prev, LLVMBasicBlockRef next) {
  LLVMBasicBlockRef bb = LLVMGetInsertBlock(JITC_BUILDER);
  LLVMBasicBlockRef cond = LLVMAppendBasicBlock(LLVMGetBasicBlockParent(prev), "cond");
  LLVMPositionBuilderAtEnd(JITC_BUILDER, prev);
  LLVMValueRef counter = LLVMBuildAlloca(JITC_BUILDER, LLVMInt32Type(), "counter");
  LLVMBuildStore(JITC_BUILDER, LLVMConstInt(LLVMInt32Type(), n, 1), counter);
  LLVMBuildBr(JITC_BUILDER, cond);
  
  LLVMPositionBuilderAtEnd(JITC_BUILDER, cond);
  LLVMValueRef i = LLVMBuildLoad(JITC_BUILDER, counter, "");
  LLVMValueRef If = LLVMBuildICmp(JITC_BUILDER, LLVMIntEQ, i,
                        LLVMConstInt(LLVMInt32Type(), 0, 1), "n == 0");
  LLVMBuildCondBr(JITC_BUILDER, If, next, repeat);
  
  LLVMPositionBuilderAtEnd(JITC_BUILDER, repeat);
  i = LLVMBuildLoad(JITC_BUILDER, counter, "");
  i = LLVMBuildSub(JITC_BUILDER, i, LLVMConstInt(LLVMInt32Type(), 1, 1), "");
  LLVMBuildStore(JITC_BUILDER, i, counter);
  LLVMBuildBr(JITC_BUILDER, cond);
  LLVMPositionBuilderAtEnd(JITC_BUILDER, bb);
}

/* Add instructions that get the address the n-th constant of a closure. */
static LLVMValueRef jitc_getptr_cconst (LLVMValueRef closure, int n) {
  LLVMValueRef converted = LLVMBuildPtrToInt(JITC_BUILDER, closure, LLVMInt64Type(), "");
  LLVMValueRef offset = jitc_get_offset(Cclosure, clos_consts);
  LLVMValueRef cconsts = LLVMBuildAdd(JITC_BUILDER, converted, offset, "");
  LLVMValueRef res = LLVMBuildIntToPtr(JITC_BUILDER, cconsts,
                                      LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
  LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), n, 1)};
  return LLVMBuildGEP(JITC_BUILDER, res, idx, 1, "");
}

/* Add instructions to get the n-th constant of a closure. */
static LLVMValueRef jitc_get_cconst (LLVMValueRef closure, int n) {
  return LLVMBuildLoad(JITC_BUILDER, jitc_getptr_cconst(closure, n), "");
}

/* Add instructions that return the name or class version of a closure. */
static LLVMValueRef jitc_getptr_clos_name_or_class_version (LLVMValueRef clos) {
  LLVMValueRef converted = LLVMBuildPtrToInt(JITC_BUILDER, clos, LLVMInt64Type(), "");
  LLVMValueRef offset = jitc_get_offset(Cclosure, clos_name_or_class_version);
  LLVMValueRef data = LLVMBuildAdd(JITC_BUILDER, converted, offset, "");
  LLVMValueRef res = LLVMBuildIntToPtr(JITC_BUILDER, data,
                                      LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
  return res;
}

/* Add instructions that get the address of the n-th element of the sp stack. */
static LLVMValueRef jitc_getptr_sp (LLVMValueRef topptr, int n) {
  LLVMValueRef top = LLVMBuildLoad(JITC_BUILDER, topptr, "");
  LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), n, 1)};
  return LLVMBuildGEP(JITC_BUILDER, top, idx, 1, "");
}

/* Add instructions that get the n-th element of the sp stack. */
static LLVMValueRef jitc_get_sp (LLVMValueRef topptr, int n) {
  return LLVMBuildLoad(JITC_BUILDER, jitc_getptr_sp(topptr, n), "");
}

/* Add instructions that get the address of the n-th element of a given svector. */
static LLVMValueRef jitc_getptr_svecdata (LLVMValueRef svec, int n) {
  LLVMValueRef converted = LLVMBuildPtrToInt(JITC_BUILDER,
                                    svec,
                                    LLVMInt64Type(), "");
  LLVMValueRef offset = jitc_get_offset(Svector, data);
  LLVMValueRef data = LLVMBuildAdd(JITC_BUILDER, converted, offset, "");
  LLVMValueRef res = LLVMBuildIntToPtr(JITC_BUILDER, data,
                                      LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
  LLVMValueRef idx[] = {LLVMConstInt(LLVMInt32Type(), n, 1)};
  return LLVMBuildGEP(JITC_BUILDER, res, idx, 1, "");
}

/* Add instructions that get the n-th element of a given svector. */
static LLVMValueRef jitc_get_svecdata (LLVMValueRef svec, int n) {
  return LLVMBuildLoad(JITC_BUILDER, jitc_getptr_svecdata(svec, n), "");
}

/* Add instructions that get the venv of a given closure. */
static LLVMValueRef jitc_getptr_venv (LLVMValueRef closure) {
  return jitc_getptr_cconst(closure, 0);
}

/* Add instructions that verify if a given symbol is bound. */
static LLVMValueRef jitc_is_symbound (LLVMValueRef sym) {
  LLVMValueRef If = LLVMBuildICmp(JITC_BUILDER, LLVMIntNE, sym, JITC_UNBOUND, "is_unbound");
  return If;
}

/* Add instructions that get the address of the value of a given symbol. */
static LLVMValueRef jitc_getptr_symvalue (LLVMValueRef sym) {
  LLVMValueRef converted = LLVMBuildPtrToInt(JITC_BUILDER, sym, LLVMInt64Type(), "");
  LLVMValueRef offset = jitc_get_offset(Symbol, symvalue);
  LLVMValueRef data = LLVMBuildAdd(JITC_BUILDER, converted, offset, "");
  LLVMValueRef res = LLVMBuildIntToPtr(JITC_BUILDER, data,
                                      LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
  return res;
}

/* Add instructions that get the value of a given symbol. */
static LLVMValueRef jitc_get_symvalue (LLVMValueRef sym) {
  return LLVMBuildLoad(JITC_BUILDER, jitc_getptr_symvalue(sym), "");
}

/* Add instructins that get the address of a given symbol's flags. */
static LLVMValueRef jitc_getptr_symflags (LLVMValueRef sym) {
  LLVMValueRef converted = LLVMBuildPtrToInt(JITC_BUILDER, sym, LLVMInt64Type(), "");
  LLVMValueRef offset = jitc_get_offset(Symbol, header_flags);
  LLVMValueRef data = LLVMBuildAdd(JITC_BUILDER, converted, offset, "");
  LLVMValueRef res = LLVMBuildIntToPtr(JITC_BUILDER, data,
                                      LLVMPointerType(LLVMInt32Type(), 0), "");
  return res;
}

/* Add instructions that get a given symbol's flags. */
static LLVMValueRef jitc_get_symflags (LLVMValueRef sym) {
  return LLVMBuildLoad(JITC_BUILDER, jitc_getptr_symflags(sym), "");
}

/* Add instructions that verify if a given symbol is constant. */
static LLVMValueRef jitc_is_symconst (LLVMValueRef sym) {
  LLVMValueRef mask = LLVMConstInt(LLVMInt32Type(), bit(var_bit0_hf)|bit(var_bit1_hf), 1);
  LLVMValueRef flags = LLVMBuildNot(JITC_BUILDER, jitc_get_symflags(sym), "");
  LLVMValueRef res = LLVMBuildAnd(JITC_BUILDER, mask, flags, "");
  return LLVMBuildICmp(JITC_BUILDER, LLVMIntEQ, res, LLVMConstInt(LLVMInt32Type(), 0, 1), "");
}

/* Add instruction that verify if the given object is a closure. */
static LLVMValueRef jitc_isclosure (LLVMValueRef obj) {
  LLVMValueRef converted = LLVMBuildPtrToInt(JITC_BUILDER, obj, LLVMInt64Type(), "");
  LLVMValueRef offset = jitc_get_offset(Cclosure, tfl);
  LLVMValueRef tmp = LLVMBuildAdd(JITC_BUILDER, converted, offset, "");
  tmp = LLVMBuildLShr(JITC_BUILDER, tmp, LLVMConstInt(LLVMInt64Type(), 8, 0), "");
  tmp = LLVMBuildAnd(JITC_BUILDER, tmp, LLVMConstInt(LLVMInt64Type(), 0xFF, 0), "");
  tmp = LLVMBuildAnd(JITC_BUILDER, tmp, LLVMConstInt(LLVMInt64Type(), closflags_instance_B, 0), "");
  tmp = LLVMBuildICmp(JITC_BUILDER, LLVMIntNE, tmp, LLVMConstInt(LLVMInt64Type(), 0, 1), "");
  tmp = LLVMBuildZExt(JITC_BUILDER, tmp, LLVMInt32Type(), "");
  return tmp;
}

/* Add instructions to get the address of a closure's name. */
static LLVMValueRef jitc_getptr_closname (LLVMValueRef clos) {
  LLVMBasicBlockRef prev = LLVMGetInsertBlock(JITC_BUILDER);
  LLVMBasicBlockRef bb_false = LLVMAppendBasicBlock(LLVMGetBasicBlockParent(prev), "");
  LLVMBasicBlockRef bb_true = LLVMAppendBasicBlock(LLVMGetBasicBlockParent(prev), "");
  LLVMBasicBlockRef bb_res = LLVMAppendBasicBlock(LLVMGetBasicBlockParent(prev), "");
  
  LLVMValueRef res = LLVMBuildAlloca(JITC_BUILDER, LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
  
  LLVMValueRef If = LLVMBuildICmp(JITC_BUILDER, LLVMIntEQ, jitc_isclosure(clos),
                        LLVMConstInt(LLVMInt32Type(), 1, 1), "");
  LLVMBuildCondBr(JITC_BUILDER, If, bb_true, bb_false);
  
  LLVMPositionBuilderAtEnd(JITC_BUILDER, bb_true);
  LLVMBuildStore(JITC_BUILDER, jitc_getptr_cconst(clos, 1), res);
  LLVMBuildBr(JITC_BUILDER, bb_res);
  
  LLVMPositionBuilderAtEnd(JITC_BUILDER, bb_false);
  LLVMBuildStore(JITC_BUILDER, jitc_getptr_clos_name_or_class_version(clos), res);
  LLVMBuildBr(JITC_BUILDER, bb_res);
  
  LLVMPositionBuilderAtEnd(JITC_BUILDER, bb_res);
  return LLVMBuildLoad(JITC_BUILDER, res, "");
}

 /* Add instructions to get a given closure's name. */
static LLVMValueRef jitc_get_closname (LLVMValueRef clos) {
  return LLVMBuildLoad(JITC_BUILDER, jitc_getptr_closname(clos), "");
}

/* Add instructions to push an element of the stack to finish a frame of the given type and size. */
static void jitc_finish_frame (int type, int size) {
  int w = makebottomword(type, size*sizeof(gcv_object_t));
  LLVMValueRef word = LLVMConstInt(LLVMInt64Type(), w, 0);
  jitc_push_stack(LLVMConstIntToPtr(word, JITC_OBJECT_TYPE));
}

/* Add instructions that return the size of a frame given a frame info word. */
static LLVMValueRef jitc_getsize_frame (LLVMValueRef frame_info) {
  LLVMValueRef frame_info_int = LLVMBuildPtrToInt(JITC_BUILDER, frame_info, LLVMInt64Type(), "");
  return LLVMBuildAnd(JITC_BUILDER, frame_info_int, LLVMConstInt(LLVMInt64Type(), wbit(FB1)-1, 0), "");
}

/* Add instructions that return the the address of the top of a frame given the address of a frame info word. */
static LLVMValueRef jitc_gettop_frame (LLVMValueRef frame_info_ptr) {
  LLVMValueRef frame_info = LLVMBuildLoad(JITC_BUILDER, frame_info_ptr, "");
  LLVMValueRef frame_size = jitc_getsize_frame(frame_info);
  LLVMValueRef frame_info_ptr_int = LLVMBuildPtrToInt(JITC_BUILDER, frame_info_ptr, LLVMInt64Type(), "");
  
  #ifdef STACK_UP
    LLVMValueRef obj_size = LLVMConstInt(LLVMInt64Type(), sizeof(gcv_object_t), 0);
    LLVMValueRef tmp = LLVMBuildAdd(JITC_BUILDER, frame_info_ptr_int, obj_size, "");
    tmp = LLVMBuildSub(JITC_BUILDER, tmp, frame_size, "");
    return LLVMBuildIntToPtr(JITC_BUILDER, tmp, LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
  #endif
  #ifdef STACK_DOWN
    LLVMValueRef tmp = LLVMBuildAdd(JITC_BUILDER, frame_info_ptr_int, frame_size, "");
    return LLVMBuildIntToPtr(JITC_BUILDER, tmp, LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
  #endif
}

/* ------ JITC Main functions ------ */
/* Compile a bytecode function into machine code */
static Values jitc_compile (object closure_in, Sbvector codeptr,
                        const uintB* byteptr_in) {
  GCTRIGGER_IF(true, {
    if (*byteptr_in == cod_handler_begin_push)
      GCTRIGGER3(closure,handler_args.condition,handler_args.spdepth);
    else
      GCTRIGGER1(closure);
  });
 #if STACKCHECKC || defined(DEBUG_BYTECODE)
  var const uintL byteptr_min = ((Codevec)codeptr)->ccv_flags & bit(7)
    ? CCV_START_KEY : CCV_START_NONKEY;
 #endif
 #ifdef DEBUG_BYTECODE
  var const uintL byteptr_max = sbvector_length(codeptr)-1;
  var sintL byteptr_bad_jump;
 #endif
  TRACE_CALL(closure,'B','C');
  /* situate closure in STACK, below the arguments: */
  var gcv_object_t* closureptr = (pushSTACK(closure), &STACK_0);
  
  /* If there is no fast SP-Access, one has to introduce
   an extra pointer: */
  var uintL private_SP_length =
    (uintL)(((Codevec)codeptr)->ccv_spdepth_1)
    + jmpbufsize * (uintL)(((Codevec)codeptr)->ccv_spdepth_jmpbufsize);
  var DYNAMIC_ARRAY(private_SP_space,SPint,private_SP_length);
  SPint* private_SP = &private_SP_space[private_SP_length];
  
  // if (!TheFpointer(cclosure_jitc(closure_in))->fp_pointer) {
  //   struct jitc_object *jo = malloc(sizeof(struct jitc_object));
  //   jo->jo_gc_mark = 0;
  //   jo->module = LLVMModuleCreateWithName("");
  //   jo->jo_next = all_jitc_objects;
  //   all_jitc_objects = jo;
  //   TheFpointer(cclosure_jitc(closure_in))->fp_pointer = jo;
  // }
  // struct jitc_object *jo = TheFpointer(cclosure_jitc(closure_in))->fp_pointer;
  if (!JITC_GLOBAL_MODULE)
    jitc_init_compiler();
  
  #undef SP_
  #undef _SP_
  #undef skipSP
  #undef pushSP
  #undef popSP
  #define SP_(n)  (private_SP[n])
  #define _SP_(n)  &SP_(n)
  #define skipSP(n)  (private_SP += (n))
  #define pushSP(item)  (*--private_SP = (item))
  #define popSP(item_assignment)  (item_assignment *private_SP++)

  /* var JMPBUF_on_SP(name);  allocates a sp_jmp_buf in SP.
   FREE_JMPBUF_on_SP();  deallocates it.
   finish_entry_frame_1(frametype,returner,reentry_statement);  is like
   finish_entry_frame(frametype,returner,,reentry_statement);  but
   also private_SP is saved. */
  #define JMPBUF_on_SP(name)  \
    sp_jmp_buf* name = (sp_jmp_buf*)(private_SP -= jmpbufsize);
  #define FREE_JMPBUF_on_SP()  \
    private_SP += jmpbufsize;
  #define finish_entry_frame_1(frametype,returner,reentry_statement)  \
    finish_entry_frame(frametype,*returner, /* On entry: returner = private_SP */ \
                       returner = (sp_jmp_buf*) , /* returner is set again on return */ \
        { private_SP = (SPint*)returner; reentry_statement }) /* and private_SP is reconstructed */
  /* next Byte to be interpreted
   > mv_count/mv_space: current values
   > closureptr: pointer to the compiled closure on Stack
   > closure: compiled closure
   > codeptr: its codevector, a Simple-Bit-Vektor, pointable
              (no LISP-object, but nevertheless endangered by GC!)
   > byteptr_in: pointer to the next byte in code
              (no LISP-object, but nevertheless endangered by GC!) */
 next_byte:
  /* definition by cases, according to byte to be interpreted byte */
  switch (*byteptr_in++)
  #define CASE  case (uintB)
  {
    /* Operand-Fetch:
       next Byte:
         Bit 7 = 0 --> Bits 6..0 are the Operand (7 Bits).
         Bit 7 = 1 --> Bits 6..0 and next Byte form the
                       Operand (15 Bits).
                       For jump-distances: Should this be =0, the next
                       4 Bytes form the Operand
                       (32 Bits).

       Macro B_operand(where);
       moves the next Operand (a Byte as Unsigned Integer)
       to (uintL)where and advances  bytecodepointer. */
      #define B_operand(where)  \
        { where = *byteptr_in++; }

    /* Macro U_operand(where);
     moves the next Operand (an Unsigned Integer)
     to (uintL)where or (uintC)where
     and advances the Bytecodepointer. */
      #define U_operand(where)  \
        { where = *byteptr_in++;           /* read first Byte */ \
          if ((uintB)where & bit(7))    /* Bit 7 set? */ \
            { where &= ~bit(7);         /* yes -> delete */ \
              where = where << 8;                            \
              where |= *byteptr_in++;          /* and read next Byte */ \
        }   }
    /* Macro S_operand(where);
     moves the next Operand (a Signed Integer)
     to (uintL)where and advances the bytecodepointer. */
      #define S_operand(where)                                          \
        { where = *byteptr_in++;                    /* read first byte */  \
          if ((uintB)where & bit(7))                                    \
            /* Bit 7 was set */                                         \
            { where = where << 8;                                       \
              where |= *byteptr_in++;             /* subjoin next Byte */  \
              /* Sign-Extend from 15 to 32 Bits: */                     \
              where = (sintL)((sintL)(sintWL)((sintWL)where << (intWLsize-15)) >> (intWLsize-15)); \
              if (where == 0)                                           \
                /* special case: 2-Byte-Operand = 0 -> 6-Byte-Operand */ \
                { where = (uintL)( ((uintWL)(byteptr_in[0]) << 8)          \
                                  | (uintWL)(byteptr_in[1])                \
                                 ) << 16                                \
                        | (uintL)( ((uintWL)(byteptr_in[2]) << 8)          \
                                  | (uintWL)(byteptr_in[3])                \
                                 );                                     \
                  byteptr_in += 4;                                         \
            }   }                                                       \
            else                                                        \
            /* Bit 7 was deleted */                                     \
            {                     /* Sign-Extend from 7 to 32 Bits: */  \
              where = (sintL)((sintL)(sintBWL)((sintBWL)where << (intBWLsize-7)) >> (intBWLsize-7)); \
            }                                                           \
        }
    /* Macro S_operand_ignore();
     skips the next Operand (a Signed Integer)
     and advances the bytecodepointer. */
      #define S_operand_ignore()                                        \
        { var uintB where = *byteptr_in++;          /* read first byte */  \
          if ((uintB)where & bit(7))                                    \
            /* Bit 7 was set */                                         \
            { if ((uintB)((where<<1) | *byteptr_in++) == 0) /* next Byte */ \
                /* special case: 2-Byte-Operand = 0 -> 6-Byte-Operand */ \
                { byteptr_in += 4; }                                       \
        }   }
    /* Macro L_operand(where);
     moves the next Operand (a Label)
     to (uintB*)where and advances the bytecodepointer. */
      #define L_operand(Lwhere)                                         \
        { var uintL where;         /* variable for the displacement */  \
          S_operand(where);        /* Displacement */                   \
          Lwhere = byteptr_in + (sintL)where;             /* add */        \
        }

    /* Macro L_operand_ignore();
     skips the next Operand (a Label)
     and advances the Bytecodepointer. */
      #define L_operand_ignore()  S_operand_ignore()
    /* Each of the bytecodes is interpreted:
     for the most part: mv_count/mv_space = values,
     closureptr = pointer to the compiled closure in Stack,
     closure = compiled closure,
     codeptr = pointer to its codevector,
     byteptr_in = pointer to the next Byte in code.
     (byteptr_in is no LISP-object, but nevertheless endangered by GC!
      To make it GC-invariant, substract CODEPTR from it.
      If one then adds Fixnum_0 to it,
      one receives the bytenumber as Fixnum.) */
    #if 0
      #define CODEPTR  (&codeptr->data[0])
    #else  /* returns more efficient Code */
      #define CODEPTR  (uintB*)(codeptr)
    #endif

    /* store context-information:
     If sth. is called, that can trigger a GC, this must be framed within
     with_saved_context( ... ) . */
      #define with_saved_context(statement)  \
        { var uintL index = byteptr_in - CODEPTR;                       \
          statement;                                                 \
          closure = *closureptr;       /* fetch Closure from Stack */\
          codeptr = TheSbvector(TheCclosure(closure)->clos_codevec); \
          byteptr_in = CODEPTR + index;                                 \
        }

    /* ------------------- (1) Constants ----------------------- */
    CASE cod_nil: code_nil: {   /* (NIL) */
      VALUES1(NIL);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(NIL)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // jitc_set_values_1(JITC_NIL);
      // jitc_end();
    } goto next_byte;
    CASE cod_nil_push: {        /* (NIL&PUSH) */
      pushSTACK(NIL);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(NIL&PUSH)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // jitc_push_stack(JITC_NIL);
      // jitc_end();
    } goto next_byte;
    CASE cod_push_nil: {        /* (PUSH-NIL n) */
      var uintC n;
      U_operand(n);
      dotimesC(n,n, { pushSTACK(NIL); } );
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(PUSH-NIL n)");
      // LLVMBasicBlockRef repeat = LLVMAppendBasicBlock(fun, "");
      // LLVMBasicBlockRef end = LLVMAppendBasicBlock(fun, "");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, repeat);
      // jitc_push_stack(JITC_NIL);
      // jitc_repeat(n, repeat, entry, end);
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, end);
      // jitc_end();
    } goto next_byte;
    CASE cod_t: code_t: {       /* (T) */
      VALUES1(T);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(T)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // jitc_set_values_1(JITC_TRUE);
      // jitc_end();
    } goto next_byte;
    CASE cod_t_push: {          /* (T&PUSH) */
      pushSTACK(T);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(T&PUSH)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // jitc_push_stack(JITC_TRUE);
      // jitc_end();
    } goto next_byte;
    CASE cod_const: {           /* (CONST n) */
      var uintL n;
      U_operand(n);
      VALUES1(TheCclosure(closure)->clos_consts[n]);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(CONST n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef obj = LLVMBuildLoad(JITC_BUILDER, jitc_closure, "");
      // LLVMValueRef res = jitc_getptr_cconst(obj, n);
      // jitc_set_values_1(LLVMBuildLoad(JITC_BUILDER, res, ""));
      // jitc_end();
    } goto next_byte;
    CASE cod_const_push: {      /* (CONST&PUSH n) */
      var uintL n;
      U_operand(n);
      pushSTACK(TheCclosure(closure)->clos_consts[n]);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(CONST&PUSH n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef obj = LLVMBuildLoad(JITC_BUILDER, jitc_closure, "");
      // LLVMValueRef res = jitc_getptr_cconst(obj, n);
      // jitc_push_stack(LLVMBuildLoad(JITC_BUILDER, res, ""));
      // jitc_end();
    } goto next_byte;
    /* ------------------- (2) static Variables ----------------------- */
    CASE cod_load: {            /* (LOAD n) */
      var uintL n;
      U_operand(n);
      VALUES1(STACK_(n));
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(LOAD n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef res = jitc_getptr_stack(n);
      // jitc_set_values_1(LLVMBuildLoad(JITC_BUILDER, res, ""));
      // jitc_end();
    } goto next_byte;
    CASE cod_load_push: {       /* (LOAD&PUSH n) */
      var uintL n;
      U_operand(n);
      pushSTACK(STACK_(n));
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(LOAD&PUSH n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef top = LLVMBuildLoad(JITC_BUILDER, JITC_STACK, "TOP");
      // LLVMValueRef res = jitc_getptr_stack_with(n, top);
      // jitc_push_stack_with(LLVMBuildLoad(JITC_BUILDER, res, ""), top);
      // jitc_end();
    } goto next_byte;
    CASE cod_loadi: {           /* (LOADI k1 k2 n) */
      var uintL k1;
      var uintL k2;
      var uintL n;
      U_operand(k1);
      U_operand(k2);
      U_operand(n);
      var gcv_object_t* FRAME = (gcv_object_t*) SP_(k1+jmpbufsize*k2);
      VALUES1(FRAME_(n));
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(LOADI k1 k2 n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef res = LLVMBuildLoad(JITC_BUILDER,
      //                                 jitc_getptr_sp(jitc_sp, k1+jmpbufsize*k2),
      //                                 "");
      // LLVMValueRef obj = LLVMBuildLoad(JITC_BUILDER,
      //                                   jitc_getptr_frame(res, n), "");
      // jitc_set_values_1(obj);
      // jitc_end();
    } goto next_byte;
    CASE cod_loadi_push: {      /* (LOADI&PUSH k1 k2 n) */
      var uintL k1;
      var uintL k2;
      var uintL n;
      U_operand(k1);
      U_operand(k2);
      U_operand(n);
      var gcv_object_t* FRAME = (gcv_object_t*) SP_(k1+jmpbufsize*k2);
      pushSTACK(FRAME_(n));
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(LOADI&PUSH k1 k2 n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef res = LLVMBuildLoad(JITC_BUILDER,
      //                                 jitc_getptr_sp(jitc_sp, k1+jmpbufsize*k2),
      //                                 "");
      // LLVMValueRef obj = LLVMBuildLoad(JITC_BUILDER,
      //                                   jitc_getptr_frame(res, n), "");
      // jitc_push_stack(obj);
      // jitc_end();
    } goto next_byte;
    CASE cod_loadc: {           /* (LOADC n m) */
      var uintL n;
      var uintL m;
      U_operand(n);
      U_operand(m);
      VALUES1(TheSvector(STACK_(n))->data[1+m]);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(LOADC n m)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef obj = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_stack(n), "");
      // LLVMValueRef res = jitc_getptr_svecdata(obj, 1+m);
      // jitc_set_values_1(LLVMBuildLoad(JITC_BUILDER, res, ""));
      // jitc_end();
    } goto next_byte;
    CASE cod_loadc_push: {      /* (LOADC&PUSH n m) */
      var uintL n;
      var uintL m;
      U_operand(n);
      U_operand(m);
      pushSTACK(TheSvector(STACK_(n))->data[1+m]);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(LOADC&PUSH n m)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef obj = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_stack(n), "");
      // LLVMValueRef res = jitc_getptr_svecdata(obj, 1+m);
      // jitc_push_stack(LLVMBuildLoad(JITC_BUILDER, res, ""));
      // jitc_end();
    } goto next_byte;
    CASE cod_loadv: {           /* (LOADV k m) */
      var uintC k;
      var uintL m;
      U_operand(k);
      U_operand(m);
      var object venv = TheCclosure(closure)->clos_venv; /* VenvConst */
      /* take (svref ... 0) k times: */
      dotimesC(k,k, { venv = TheSvector(venv)->data[0]; } );
      /* fetch (svref ... m) : */
      VALUES1(TheSvector(venv)->data[m]);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(LOADV k m)");
      // LLVMBasicBlockRef repeat = LLVMAppendBasicBlock(fun, "");
      // LLVMBasicBlockRef end = LLVMAppendBasicBlock(fun, "");
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef venv = LLVMBuildAlloca(JITC_BUILDER, JITC_OBJECT_TYPE, "");
      // LLVMValueRef tmp = LLVMBuildLoad(JITC_BUILDER, jitc_closure, "");
      // LLVMBuildStore(JITC_BUILDER, LLVMBuildLoad(JITC_BUILDER, jitc_getptr_venv(tmp), NULL), venv);
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, repeat);
      // tmp = LLVMBuildLoad(JITC_BUILDER, venv, "");
      // tmp = jitc_getptr_svecdata(tmp, 0);
      // LLVMBuildStore(JITC_BUILDER, LLVMBuildLoad(JITC_BUILDER, tmp, ""), venv);
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, end);
      // tmp = LLVMBuildLoad(JITC_BUILDER, venv, "");
      // tmp = jitc_getptr_svecdata(tmp, m);
      // jitc_set_values_1(LLVMBuildLoad(JITC_BUILDER, tmp, ""));
      // 
      // jitc_repeat(k, repeat, entry, end);
      // jitc_end();
    } goto next_byte;
    CASE cod_loadv_push: {      /* (LOADV&PUSH k m) */
      var uintC k;
      var uintL m;
      U_operand(k);
      U_operand(m);
      var object venv = TheCclosure(closure)->clos_venv; /* VenvConst */
      /* take (svref ... 0) k times: */
      dotimesC(k,k, { venv = TheSvector(venv)->data[0]; } );
      /* fetch (svref ... m) : */
      pushSTACK(TheSvector(venv)->data[m]);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(LOADV&PUSH k m)");
      // LLVMBasicBlockRef repeat = LLVMAppendBasicBlock(fun, "");
      // LLVMBasicBlockRef end = LLVMAppendBasicBlock(fun, "");
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef venv = LLVMBuildAlloca(JITC_BUILDER, JITC_OBJECT_TYPE, "");
      // LLVMValueRef tmp = LLVMBuildLoad(JITC_BUILDER, jitc_closure, "");
      // LLVMBuildStore(JITC_BUILDER, LLVMBuildLoad(JITC_BUILDER, jitc_getptr_venv(tmp), NULL), venv);
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, repeat);
      // tmp = LLVMBuildLoad(JITC_BUILDER, venv, "");
      // tmp = jitc_getptr_svecdata(tmp, 0);
      // LLVMBuildStore(JITC_BUILDER, LLVMBuildLoad(JITC_BUILDER, tmp, ""), venv);
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, end);
      // tmp = LLVMBuildLoad(JITC_BUILDER, venv, "");
      // tmp = jitc_getptr_svecdata(tmp, m);
      // jitc_push_stack(LLVMBuildLoad(JITC_BUILDER, tmp, ""));
      // 
      // jitc_repeat(k, repeat, entry, end);
      // jitc_end();
    } goto next_byte;
    CASE cod_loadic: {          /* (LOADIC k1 k2 n m) */
      var uintL k1;
      var uintL k2;
      var uintL n;
      var uintL m;
      U_operand(k1);
      U_operand(k2);
      U_operand(n);
      U_operand(m);
      var gcv_object_t* FRAME = (gcv_object_t*) SP_(k1+jmpbufsize*k2);
      VALUES1(TheSvector(FRAME_(n))->data[1+m]);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(LOADIC k1 k2 n m)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef tmp = jitc_getptr_sp(jitc_sp, k1+jmpbufsize*k2);
      // tmp = LLVMBuildLoad(JITC_BUILDER, tmp, "");
      // tmp = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_frame(tmp, n), "");
      // tmp = jitc_getptr_svecdata(tmp, 1+m);
      // jitc_set_values_1(LLVMBuildLoad(JITC_BUILDER, tmp, ""));
      // jitc_end();
    } goto next_byte;
    CASE cod_store: store: {    /* (STORE n) */
      var uintL n;
      U_operand(n);
      VALUES1(STACK_(n) = value1);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(STORE n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef val = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_values(0), "");
      // jitc_set_mvcount(1);
      // LLVMBuildStore(JITC_BUILDER, val, jitc_getptr_stack(n));
      // jitc_end();
    } goto next_byte;
    CASE cod_pop_store: {       /* (POP&STORE n) */
      var uintL n;
      U_operand(n);
      var object obj = popSTACK();
      VALUES1(STACK_(n) = obj);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(POP&STORE n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef val = jitc_pop_stack();
      // jitc_set_values_1(val);
      // LLVMBuildStore(JITC_BUILDER, val, jitc_getptr_stack(n));
      // jitc_end();
    } goto next_byte;
    CASE cod_storei: {          /* (STOREI k1 k2 n) */
      var uintL k1;
      var uintL k2;
      var uintL n;
      U_operand(k1);
      U_operand(k2);
      U_operand(n);
      var gcv_object_t* FRAME = (gcv_object_t*) SP_(k1+jmpbufsize*k2);
      VALUES1(FRAME_(n) = value1);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(STOREI k1 k2 n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef val = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_values(0), "");
      // LLVMValueRef tmp = jitc_getptr_sp(jitc_sp, k1+jmpbufsize*k2);
      // tmp = LLVMBuildLoad(JITC_BUILDER, tmp, "");
      // tmp = jitc_getptr_frame(tmp, n);
      // LLVMBuildStore(JITC_BUILDER, val, tmp);
      // jitc_set_mvcount(1);
      // jitc_end();
    } goto next_byte;
    CASE cod_load_storec: {     /* (LOAD&STOREC k m n) */
      var uintL k;
      var uintL n;
      var uintL m;
      U_operand(k);
      U_operand(n);
      U_operand(m);
      value1 = STACK_(k);
      TheSvector(STACK_(n))->data[1+m] = value1; mv_count=1;
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(LOAD&STOREC k m n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef val = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_stack(k), "");
      // jitc_set_values_1(val);
      // LLVMValueRef tmp = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_stack(n), "");
      // tmp = jitc_getptr_svecdata(tmp, 1+m);
      // LLVMBuildStore(JITC_BUILDER, val, tmp);
      // jitc_end();
    } goto next_byte;
    CASE cod_storec: {          /* (STOREC n m) */
      var uintL n;
      var uintL m;
      U_operand(n);
      U_operand(m);
      TheSvector(STACK_(n))->data[1+m] = value1; mv_count=1;
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(STOREC n m)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef val = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_values(0), "");
      // LLVMValueRef tmp = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_stack(n), "");
      // tmp = jitc_getptr_svecdata(tmp, 1+m);
      // LLVMBuildStore(JITC_BUILDER, val, tmp);
      // jitc_set_mvcount(1);
      // jitc_end();
    } goto next_byte;
    CASE cod_storev: {          /* (STOREV k m) */
      var uintC k;
      var uintL m;
      U_operand(k);
      U_operand(m);
      var object venv = TheCclosure(closure)->clos_venv; /* VenvConst */
      /* take (svref ... 0) k times: */
      dotimesC(k,k, { venv = TheSvector(venv)->data[0]; } );
      /* save (svref ... m) : */
      TheSvector(venv)->data[m] = value1; mv_count=1;
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(STOREV k m)");
      // LLVMBasicBlockRef repeat = LLVMAppendBasicBlock(fun, "");
      // LLVMBasicBlockRef end = LLVMAppendBasicBlock(fun, "");
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef venv = LLVMBuildAlloca(JITC_BUILDER, JITC_OBJECT_TYPE, "");
      // LLVMValueRef tmp = LLVMBuildLoad(JITC_BUILDER, jitc_closure, "");
      // LLVMBuildStore(JITC_BUILDER, LLVMBuildLoad(JITC_BUILDER, jitc_getptr_venv(tmp), NULL), venv);
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, repeat);
      // tmp = LLVMBuildLoad(JITC_BUILDER, venv, "");
      // tmp = jitc_getptr_svecdata(tmp, 0);
      // LLVMBuildStore(JITC_BUILDER, LLVMBuildLoad(JITC_BUILDER, tmp, ""), venv);
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, end);
      // LLVMValueRef val = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_values(0), "");
      // tmp = LLVMBuildLoad(JITC_BUILDER, venv, "");
      // tmp = jitc_getptr_svecdata(tmp, m);
      // LLVMBuildStore(JITC_BUILDER, val, tmp);
      // jitc_set_mvcount(1);
      // 
      // jitc_repeat(k, repeat, entry, end);
      // jitc_end();
    } goto next_byte;
    CASE cod_storeic: {         /* (STOREIC k1 k2 n m) */
      var uintL k1;
      var uintL k2;
      var uintL n;
      var uintL m;
      U_operand(k1);
      U_operand(k2);
      U_operand(n);
      U_operand(m);
      var gcv_object_t* FRAME = (gcv_object_t*) SP_(k1+jmpbufsize*k2);
      TheSvector(FRAME_(n))->data[1+m] = value1; mv_count=1;
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(STOREIC k1 k2 n m)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef val = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_values(0), "");
      // LLVMValueRef tmp = jitc_getptr_sp(jitc_sp, k1+jmpbufsize*k2);
      // tmp = LLVMBuildLoad(JITC_BUILDER, tmp, "");
      // tmp = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_frame(tmp, n), "");
      // tmp = jitc_getptr_svecdata(tmp, 1+m);
      // LLVMBuildStore(JITC_BUILDER, val, tmp);
      // jitc_set_mvcount(1);
      // jitc_end();
    } goto next_byte;
    /* ------------------- (3) dynamic Variables ----------------------- */
    CASE cod_getvalue: {        /* (GETVALUE n) */
      var uintL n;
      U_operand(n);
      var object symbol = TheCclosure(closure)->clos_consts[n];
      /* The Compiler has already checked, that it's a Symbol. */
      if (!boundp(Symbol_value(symbol))) {
        pushSTACK(symbol);      /* CELL-ERROR slot NAME */
        pushSTACK(symbol); pushSTACK(Closure_name(closure));
        error(unbound_variable,GETTEXT("~S: symbol ~S has no value"));
      }
      VALUES1(Symbol_value(symbol));
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(GETVALUE n)");
      // LLVMBasicBlockRef iferror = LLVMAppendBasicBlock(fun, "");
      // LLVMBasicBlockRef end = LLVMAppendBasicBlock(fun, "");
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef sym = LLVMBuildLoad(JITC_BUILDER, jitc_closure, "");
      // sym = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_cconst(sym, n), "");
      // LLVMValueRef val = jitc_get_symvalue(sym);
      // LLVMValueRef If = LLVMBuildNot(JITC_BUILDER, jitc_is_symbound(val), "");
      // LLVMBuildCondBr(JITC_BUILDER, If, iferror, end);
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, iferror);
      // jitc_push_stack(sym);
      // jitc_push_stack(sym);
      // jitc_error(unbound_variable, GETTEXT("~S: symbol ~S has no value"));
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, end);
      // jitc_set_values_1(val);
      // 
      // jitc_end();
    } goto next_byte;
    CASE cod_getvalue_push: {   /* (GETVALUE&PUSH n) */
      var uintL n;
      U_operand(n);
      var object symbol = TheCclosure(closure)->clos_consts[n];
      /* The Compiler has already checked, that it's a Symbol. */
      if (!boundp(Symbol_value(symbol))) {
        pushSTACK(symbol);    /* CELL-ERROR slot NAME */
        pushSTACK(symbol); pushSTACK(Closure_name(closure));
        error(unbound_variable,GETTEXT("~S: symbol ~S has no value"));
      }
      pushSTACK(Symbol_value(symbol));
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(GETVALUE&PUSH n)");
      // LLVMBasicBlockRef iferror = LLVMAppendBasicBlock(fun, "");
      // LLVMBasicBlockRef end = LLVMAppendBasicBlock(fun, "");
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef sym = LLVMBuildLoad(JITC_BUILDER, jitc_closure, "");
      // sym = LLVMBuildLoad(JITC_BUILDER, jitc_getptr_cconst(sym, n), "");
      // LLVMValueRef val = jitc_get_symvalue(sym);
      // LLVMValueRef If = LLVMBuildNot(JITC_BUILDER, jitc_is_symbound(val), "");
      // LLVMBuildCondBr(JITC_BUILDER, If, iferror, end);
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, iferror);
      // jitc_push_stack(sym);
      // jitc_push_stack(sym);
      // jitc_error(unbound_variable, GETTEXT("~S: symbol ~S has no value"));
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, end);
      // jitc_push_stack(val);
      // 
      // jitc_end();
    } goto next_byte;
    CASE cod_setvalue: {        /* (SETVALUE n) */
      var uintL n;
      U_operand(n);
      var object symbol = TheCclosure(closure)->clos_consts[n];
      /* The Compiler has already checked, that it's a Symbol. */
      if (constant_var_p(TheSymbol(symbol))) {
        pushSTACK(symbol); pushSTACK(Closure_name(closure));
        error(error_condition,GETTEXT("~S: assignment to constant symbol ~S is impossible"));
      }
      Symbol_value(symbol) = value1; mv_count=1;
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(SETVALUE n)");
      // LLVMBasicBlockRef iferror = LLVMAppendBasicBlock(fun, "");
      // LLVMBasicBlockRef end = LLVMAppendBasicBlock(fun, "");
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef sym = LLVMBuildLoad(JITC_BUILDER, jitc_closure, "");
      // sym = jitc_get_cconst(sym, n);
      // LLVMBuildCondBr(JITC_BUILDER, jitc_is_symconst(sym), iferror, end);
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, iferror);
      // jitc_push_stack(sym);
      // jitc_push_stack(jitc_get_closname(sym));
      // jitc_error(error_condition, GETTEXT("~S: assignment to constant symbol ~S is impossible"));
      // 
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, end);
      // LLVMBuildStore(JITC_BUILDER, jitc_get_values(0), jitc_getptr_symvalue(sym));
      // jitc_set_mvcount(1);
      // 
      // jitc_end();
    } goto next_byte;
    CASE cod_bind: {            /* (BIND n) */
      var uintL n;
      U_operand(n);
      dynamic_bind(TheCclosure(closure)->clos_consts[n],value1);
      // jitc_begin();
      // LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(BIND n)");
      // LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
      // LLVMValueRef sym = jitc_get_cconst(LLVMBuildLoad(JITC_BUILDER, jitc_closure, ""), n);
      // LLVMValueRef top = jitc_getptr_stack(0);
      // jitc_push_stack(jitc_get_symvalue(sym));
      // jitc_push_stack(sym);
      // jitc_finish_frame(DYNBIND_frame_info, 3);
      // LLVMBuildStore(JITC_BUILDER, jitc_get_values(0), jitc_getptr_symvalue(sym));
      // jitc_end();
    } goto next_byte;
    CASE cod_unbind1: {         /* (UNBIND1) */
        // #if STACKCHECKC
        // if (!(framecode(STACK_0) == DYNBIND_frame_info))
        //   GOTO_ERROR(error_STACK_putt);
        // #endif
        // /* unwind variable-binding-frame: */
        // var gcv_object_t* new_STACK = topofframe(STACK_0); /* pointer above frame */
        // var gcv_object_t* frame_end = STACKpointable(new_STACK);
        // var gcv_object_t* bindingptr = &STACK_1; /* begin of bindings */
        // /* bindingptr loops upwards through the bindings */
        // while (bindingptr != frame_end) {
        //   /* write back old value: */
        //   Symbol_value(*(bindingptr STACKop 0)) = *(bindingptr STACKop 1);
        //   bindingptr skipSTACKop 2; /* next binding */
        // }
        // /* set STACK newly, thus unwind frame: */
        // setSTACK(STACK = new_STACK);
        jitc_begin();
        LLVMBasicBlockRef entry = LLVMAppendBasicBlock(fun, "(UNBIND1)");
        LLVMBasicBlockRef cond = LLVMAppendBasicBlock(LLVMGetBasicBlockParent(entry), "");
        LLVMBasicBlockRef loop = LLVMAppendBasicBlock(LLVMGetBasicBlockParent(entry), "");
        LLVMBasicBlockRef end = LLVMAppendBasicBlock(LLVMGetBasicBlockParent(entry), "");
        
        LLVMPositionBuilderAtEnd(JITC_BUILDER, entry);
        LLVMValueRef frame_top = jitc_gettop_frame(jitc_getptr_stack(0));
        LLVMValueRef frame_end = LLVMBuildPtrToInt(JITC_BUILDER, jitc_getpointable_stackptr(frame_top), LLVMInt64Type(), "");
        LLVMValueRef bindings = LLVMBuildAlloca(JITC_BUILDER, LLVMPointerType(JITC_OBJECT_TYPE, 0), "");
        LLVMBuildStore(JITC_BUILDER, jitc_getptr_stack(1), bindings);
        LLVMBuildBr(JITC_BUILDER, cond);

        LLVMPositionBuilderAtEnd(JITC_BUILDER, cond);
        LLVMValueRef current = LLVMBuildPtrToInt(JITC_BUILDER, LLVMBuildLoad(JITC_BUILDER, bindings, ""),
                                                  LLVMInt64Type(), "");
        LLVMValueRef If = LLVMBuildICmp(JITC_BUILDER, LLVMIntNE, current, frame_end, "");
        LLVMBuildCondBr(JITC_BUILDER, If, loop, end);

        LLVMPositionBuilderAtEnd(JITC_BUILDER, loop);
        current = LLVMBuildLoad(JITC_BUILDER, bindings, "");
        LLVMValueRef val = LLVMBuildLoad(JITC_BUILDER, jitc_skip_stack(current, 1), "");
        LLVMValueRef sym = LLVMBuildLoad(JITC_BUILDER, jitc_skip_stack(current, 0), "");
        LLVMValueRef symvalue_ptr = jitc_getptr_symvalue(sym);
        LLVMBuildStore(JITC_BUILDER, val, symvalue_ptr);
        LLVMBuildStore(JITC_BUILDER, jitc_skip_stack(current, 2), bindings);
        LLVMBuildBr(JITC_BUILDER, cond);
        
        LLVMPositionBuilderAtEnd(JITC_BUILDER, end);
        current = LLVMBuildLoad(JITC_BUILDER, bindings, "");
        jitc_set_stack(frame_top);
        
        jitc_end();
      } goto next_byte;
    CASE cod_unbind: {          /* (UNBIND n) */
      var uintC n;
      U_operand(n);           /* n>0 */
      var gcv_object_t* FRAME = STACK;
      do {
       #if STACKCHECKC
        if (!(framecode(FRAME_(0)) == DYNBIND_frame_info))
          GOTO_ERROR(error_STACK_putt);
       #endif
        /* unwind variable-binding-frame: */
        var gcv_object_t* new_FRAME = topofframe(FRAME_(0)); /* pointer above frame */
        var gcv_object_t* frame_end = STACKpointable(new_FRAME);
        var gcv_object_t* bindingptr = &FRAME_(1); /* begin of the bindings */
        /* bindingptr loops upwards through the bindings */
        while (bindingptr != frame_end) {
          /* write back old value: */
          Symbol_value(*(bindingptr STACKop 0)) = *(bindingptr STACKop 1);
          bindingptr skipSTACKop 2; /* next binding */
        }
        FRAME = new_FRAME;
      } while (--n != 0);
      setSTACK(STACK = FRAME); /* set STACK newly */
    } goto next_byte;
    CASE cod_progv: {                  /* (PROGV) */
      var object vallist = value1;     /* value-list */
      var object symlist = popSTACK(); /* symbol-list */
      pushSP((aint)STACK);             /* push STACK into SP */
      with_saved_context( progv(symlist,vallist); ); /* build frame */
    } goto next_byte;
    /* ------------------- (4) Stackoperations ----------------------- */
    CASE cod_push:              /* (PUSH) */
      pushSTACK(value1);
      goto next_byte;
    CASE cod_pop:               /* (POP) */
      VALUES1(popSTACK());
      goto next_byte;
    CASE cod_skip: {            /* (SKIP n) */
      var uintL n;
      U_operand(n);
      skipSTACK(n);
    } goto next_byte;
    CASE cod_skipi: {           /* (SKIPI k1 k2 n) */
      var uintL k1;
      var uintL k2;
      var uintL n;
      U_operand(k1);
      U_operand(k2);
      U_operand(n);
      skipSP(k1+jmpbufsize*k2);
      var gcv_object_t* newSTACK;
      popSP( newSTACK = (gcv_object_t*) );
      setSTACK(STACK = newSTACK STACKop n);
    } goto next_byte;
    CASE cod_skipsp: {          /* (SKIPSP k1 k2) */
      var uintL k1;
      var uintL k2;
      U_operand(k1);
      U_operand(k2);
      skipSP(k1+jmpbufsize*k2);
    } goto next_byte;
    /* ------------------- (5) Control Flow and Jumps --------------------- */
    CASE cod_skip_ret: {        /* (SKIP&RET n) */
      var uintL n;
      U_operand(n);
      skipSTACK(n);
    } goto finished;            /* return (jump) to caller */
    CASE cod_skip_retgf: {      /* (SKIP&RETGF n) */
      var uintL n;
      U_operand(n);
      if (((Codevec)codeptr)->ccv_flags & bit(3)) { /* call inhibition? */
        skipSTACK(n);
        mv_count=1;
        goto finished;          /* return (jump) to caller */
      }
      /* It is known (refer to clos.lisp), that this function
       has no optional parameters, but poss. Rest-parameters.
       If there's no Rest-parameter: (FUNCALL value1 arg1 ... argr)
       If there's a  Rest-Parameter: (APPLY value1 arg1 ... argr restarg) */
      var uintL r = ((Codevec)codeptr)->ccv_numreq;
      n -= r;
      if (((Codevec)codeptr)->ccv_flags & bit(0)) {
        skipSTACK(n-1); apply(value1,r,popSTACK());
      } else {
        skipSTACK(n); funcall(value1,r);
      } goto finished;          /* return (jump) to caller */
    }
    #define JMP()                                            \
      { var const uintB* label_byteptr_in;                      \
        L_operand(label_byteptr_in);                            \
        DEBUG_CHECK_BYTEPTR(label_byteptr_in);                  \
        byteptr_in = label_byteptr_in;                             \
        goto next_byte;                                      \
      }
    #define NOTJMP()  \
      { L_operand_ignore(); goto next_byte; }
    jmp1: mv_count=1;
    CASE cod_jmp: jmp:          /* (JMP label) */
      JMP();
    CASE cod_jmpif:             /* (JMPIF label) */
      if (!nullp(value1)) goto jmp;
      notjmp:
      NOTJMP();
    CASE cod_jmpifnot:          /* (JMPIFNOT label) */
      if (nullp(value1)) goto jmp;
      NOTJMP();
    CASE cod_jmpif1:            /* (JMPIF1 label) */
      if (!nullp(value1)) goto jmp1;
      NOTJMP();
    CASE cod_jmpifnot1:         /* (JMPIFNOT1 label) */
      if (nullp(value1)) goto jmp1;
      NOTJMP();
    CASE cod_jmpifatom:         /* (JMPIFATOM label) */
      if (atomp(value1)) goto jmp;
      NOTJMP();
    CASE cod_jmpifconsp:        /* (JMPIFCONSP label) */
      if (consp(value1)) goto jmp;
      NOTJMP();
    CASE cod_jmpifeq:           /* (JMPIFEQ label) */
      if (eq(popSTACK(),value1)) goto jmp;
      NOTJMP();
    CASE cod_jmpifnoteq:        /* (JMPIFNOTEQ label) */
      if (!eq(popSTACK(),value1)) goto jmp;
      NOTJMP();
    CASE cod_jmpifeqto: {       /* (JMPIFEQTO n label) */
      var uintL n;
      U_operand(n);
      if (eq(popSTACK(),TheCclosure(closure)->clos_consts[n])) goto jmp;
    } NOTJMP();
    CASE cod_jmpifnoteqto: {    /* (JMPIFNOTEQTO n label) */
      var uintL n;
      U_operand(n);
      if (!eq(popSTACK(),TheCclosure(closure)->clos_consts[n])) goto jmp;
    } NOTJMP();
    CASE cod_jmphash: {         /* (JMPHASH n label) */
      var uintL n;
      U_operand(n);
      var object hashvalue =  /* search value1 in the Hash-table */
        gethash(value1,TheCclosure(closure)->clos_consts[n],false);
      if (eq(hashvalue,nullobj))
        goto jmp;             /* not found -> jump to label */
      else { /* interpret found Fixnum as label: */
        DEBUG_CHECK_BYTEPTR(byteptr_in + fixnum_to_V(hashvalue));
        byteptr_in += fixnum_to_V(hashvalue);
      }
    } goto next_byte;
    CASE cod_jmphashv: {        /* (JMPHASHV n label) */
      var uintL n;
      U_operand(n);
      var object hashvalue =  /* search value1 in the Hash-table */
        gethash(value1,TheSvector(TheCclosure(closure)->clos_consts[0])->data[n],false);
      if (eq(hashvalue,nullobj))
        goto jmp;             /* not found -> jump to label */
      else { /* interpret found Fixnum as label: */
        DEBUG_CHECK_BYTEPTR(byteptr_in + fixnum_to_V(hashvalue));
        byteptr_in += fixnum_to_V(hashvalue);
      }
    } goto next_byte;
    /* executes a (JSR label)-command. */
    #define JSR()  \
      check_STACK(); check_SP();                                \
      { var const uintB* label_byteptr_in;                         \
        L_operand(label_byteptr_in);                               \
        with_saved_context(                                     \
          with_saved_back_trace_cclosure(closure,               \
            interpret_bytecode_(closure,codeptr,label_byteptr_in); \
        ));                                                     \
      }
    CASE cod_jsr:               /* (JSR label) */
      JSR();
      goto next_byte;
    CASE cod_jsr_push:          /* (JSR&PUSH label) */
      JSR(); pushSTACK(value1);
      goto next_byte;
    CASE cod_jmptail: {         /* (JMPTAIL m n label) */
      var uintL m;
      var uintL n;
      U_operand(m);
      U_operand(n);
      /* It is n>=m. Copy m stack-entries upwards by n-m : */
      var gcv_object_t* ptr1 = STACK STACKop m;
      var gcv_object_t* ptr2 = STACK STACKop n;
      var uintC count;
      dotimesC(count,m, { NEXT(ptr2) = NEXT(ptr1); } );
      /* Now ptr1 = STACK and ptr2 = STACK STACKop (n-m). */
      *(closureptr = &NEXT(ptr2)) = closure; /* store closure in stack */
      setSTACK(STACK = ptr2);                /* shorten STACK */
    } JMP();                                 /* jump to label */
    /* ------------------- (6) Environments and Closures -------------------- */
    CASE cod_venv:              /* (VENV) */
      /* fetch VenvConst from the closure: */
      VALUES1(TheCclosure(closure)->clos_venv);
      goto next_byte;
    CASE cod_make_vector1_push: { /* (MAKE-VECTOR1&PUSH n) */
      var uintL n;
      U_operand(n);
      pushSTACK(value1);
      /* create vector: */
      var object vec;
      with_saved_context( { vec = allocate_vector(n+1); } );
      /* fill first element: */
      TheSvector(vec)->data[0] = STACK_0;
      STACK_0 = vec;
    } goto next_byte;
    CASE cod_copy_closure: {    /* (COPY-CLOSURE m n) */
      var object oldclos;
      { /* fetch closure to be copied: */
        var uintL m;
        U_operand(m);
        oldclos = TheCclosure(closure)->clos_consts[m];
      }
      /* allocate closure of equal length: */
      var object newclos;
      pushSTACK(oldclos);
      with_saved_context(newclos = allocate_cclosure_copy(oldclos););
      oldclos = popSTACK();
      /* copy contents of the old closure into the new one: */
      do_cclosure_copy(newclos,oldclos);
      {                   /* copy stack content into the new closure: */
        var uintL n;
        U_operand(n);
        var gcv_object_t* newptr = &TheCclosure(newclos)->clos_consts[n];
        dotimespL(n,n, { *--newptr = popSTACK(); } );
      }
      VALUES1(newclos);
    } goto next_byte;
    CASE cod_copy_closure_push: { /* (COPY-CLOSURE&PUSH m n) */
      var object oldclos;
      { /* fetch closure to be copied: */
        var uintL m;
        U_operand(m);
        oldclos = TheCclosure(closure)->clos_consts[m];
      }
      /* allocate closure of equal length: */
      var object newclos;
      pushSTACK(oldclos);
      with_saved_context(newclos = allocate_cclosure_copy(oldclos););
      oldclos = popSTACK();
      /* copy contents of the old closure into the new one: */
      do_cclosure_copy(newclos,oldclos);
      { /* copy stack content into the new closure: */
        var uintL n;
        U_operand(n);
        var gcv_object_t* newptr = &TheCclosure(newclos)->clos_consts[n];
        dotimespL(n,n, { *--newptr = popSTACK(); } );
      }
      pushSTACK(newclos);
    } goto next_byte;
    /* ------------------- (7) Function Calls -----------------------
     executes (CALL k n)-command. */
    #define CALL()  \
      { var uintC k;             /* number of arguments */ \
        var uintL n;                                       \
        U_operand(k);                                      \
        U_operand(n);                                      \
        with_saved_context(                                \
          funcall(TheCclosure(closure)->clos_consts[n],k); \
        );                                                 \
      }
    /* executes (CALL0 n)-command. */
    #define CALL0()  \
      { var uintL n;                                       \
        U_operand(n);                                      \
        with_saved_context(                                \
          funcall(TheCclosure(closure)->clos_consts[n],0); \
        );                                                 \
      }
    /* executes (CALL1 n)-command. */
    #define CALL1()  \
      { var uintL n;                                       \
        U_operand(n);                                      \
        with_saved_context(                                \
          funcall(TheCclosure(closure)->clos_consts[n],1); \
        );                                                 \
      }
    /* executes (CALL2 n)-command. */
    #define CALL2()  \
      { var uintL n;                                       \
        U_operand(n);                                      \
        with_saved_context(                                \
          funcall(TheCclosure(closure)->clos_consts[n],2); \
        );                                                 \
      }
    /* executes (CALLS1 n)-command. */
    #define CALLS1()                                                    \
      { var uintL n;                                                    \
        B_operand(n);                                                   \
        /* The compiler has already done the argument-check. */         \
       {var Subr fun = FUNTAB1[n];                                      \
        with_saved_context(                                             \
          with_saved_back_trace_subr(subr_tab_ptr_as_object(fun),STACK,-1, \
            (*(subr_norest_function_t*)(fun->function))();              \
          ));                                                           \
      }}
    /* executes (CALLS2 n)-command. */
    #define CALLS2()                                                    \
      { var uintL n;                                                    \
        B_operand(n);                                                   \
        /* The compiler has already done the argument-check. */         \
       {var Subr fun = FUNTAB2[n];                                      \
        with_saved_context(                                             \
          with_saved_back_trace_subr(subr_tab_ptr_as_object(fun),STACK,-1, \
            (*(subr_norest_function_t*)(fun->function))();              \
          ));                                                           \
      }}                                                                \
    /* executes (CALLSR m n)-command. */
    #define CALLSR()                                                    \
      { var uintL m;                                                    \
        var uintL n;                                                    \
        U_operand(m);                                                   \
        B_operand(n);                                                   \
        /* The compiler has already done the argument-check. */         \
       {var Subr fun = FUNTABR[n];                                      \
        with_saved_context(                                             \
          with_saved_back_trace_subr(subr_tab_ptr_as_object(fun),STACK,-1, \
            (*(subr_rest_function_t*)(fun->function))(m,args_end_pointer STACKop m); \
          ));                                                           \
      }}
    CASE cod_call:              /* (CALL k n) */
      CALL();
      goto next_byte;
    CASE cod_call_push:         /* (CALL&PUSH k n) */
      CALL(); pushSTACK(value1);
      goto next_byte;
    CASE cod_call0:             /* (CALL0 n) */
      CALL0();
      goto next_byte;
    CASE cod_call1:             /* (CALL1 n) */
      CALL1();
      goto next_byte;
    CASE cod_call1_push:        /* (CALL1&PUSH n) */
      CALL1(); pushSTACK(value1);
      goto next_byte;
    CASE cod_call2:             /* (CALL2 n) */
      CALL2();
      goto next_byte;
    CASE cod_call2_push:        /* (CALL2&PUSH n) */
      CALL2(); pushSTACK(value1);
      goto next_byte;
    CASE cod_calls1:            /* (CALLS1 n) */
      CALLS1();
      goto next_byte;
    CASE cod_calls1_push:       /* (CALLS1&PUSH n) */
      CALLS1(); pushSTACK(value1);
      goto next_byte;
    CASE cod_calls2:            /* (CALLS2 n) */
      CALLS2();
      goto next_byte;
    CASE cod_calls2_push:       /* (CALLS2&PUSH n) */
      CALLS2(); pushSTACK(value1);
      goto next_byte;
    CASE cod_callsr:            /* (CALLSR m n) */
      CALLSR();
      goto next_byte;
    CASE cod_callsr_push:       /* (CALLSR&PUSH m n) */
      CALLSR(); pushSTACK(value1);
      goto next_byte;
    /* executes a (CALLC)-command. */
    #define CALLC()  \
      { check_STACK(); check_SP();            /* check STACK and SP */ \
        with_saved_context(                                  \
          /* interprete compiled closure starting at Byte 8 */ \
          interpret_bytecode(value1,TheCclosure(value1)->clos_codevec,CCV_START_NONKEY); \
        );                                                   \
      }
    /* executes a (CALLCKEY)-command. */
    #define CALLCKEY()  \
      { check_STACK(); check_SP();            /* check STACK and SP */ \
        with_saved_context(                                  \
          /* interprete compiled closure starting at Byte 12: */ \
          interpret_bytecode(value1,TheCclosure(value1)->clos_codevec,CCV_START_KEY); \
        );                                                   \
      }
    CASE cod_callc:             /* (CALLC) */
      CALLC();
      goto next_byte;
    CASE cod_callc_push:        /* (CALLC&PUSH) */
      CALLC(); pushSTACK(value1);
      goto next_byte;
    CASE cod_callckey:          /* (CALLCKEY) */
      CALLCKEY();
      goto next_byte;
    CASE cod_callckey_push:     /* (CALLCKEY&PUSH) */
      CALLCKEY(); pushSTACK(value1);
      goto next_byte;
    CASE cod_funcall: {         /* (FUNCALL n) */
      var uintL n;
      U_operand(n);
      var object fun = STACK_(n);            /* Function */
      with_saved_context( funcall(fun,n); ); /* call Function */
      skipSTACK(1);           /* discard function from Stack */
    } goto next_byte;
    CASE cod_funcall_push: {    /* (FUNCALL&PUSH n) */
      var uintL n;
      U_operand(n);
      var object fun = STACK_(n);            /* Function */
      with_saved_context( funcall(fun,n); ); /* call Function */
      STACK_0 = value1;       /* replace Function in Stack by value */
    } goto next_byte;
    CASE cod_apply: {           /* (APPLY n) */
      var uintL n;
      U_operand(n);
      var object fun = STACK_(n);                 /* Function */
      with_saved_context( apply(fun,n,value1); ); /* call Function */
      skipSTACK(1);           /* discard Function from Stack */
    } goto next_byte;
    CASE cod_apply_push: {      /* (APPLY&PUSH n) */
      var uintL n;
      U_operand(n);
      var object fun = STACK_(n);                 /* Function */
      with_saved_context( apply(fun,n,value1); ); /* call Function */
      STACK_0 = value1;       /* replace Function in Stack by value */
    } goto next_byte;
    /* ---------------- (8) optional and Keyword-arguments ---------------- */
    CASE cod_push_unbound: {    /* (PUSH-UNBOUND n) */
      var uintC n;
      U_operand(n);
      dotimesC(n,n, { pushSTACK(unbound); } );
    } goto next_byte;
    CASE cod_unlist: {          /* (UNLIST n m) */
      var uintC n;
      var uintC m;
      U_operand(n);
      U_operand(m);
      var object l = value1;
      if (n > 0)
        do {
          if (atomp(l)) goto unlist_unbound;
          pushSTACK(Car(l)); l = Cdr(l);
        } while (--n != 0);
      if (atomp(l))
        goto next_byte;
      else
        error_apply_toomany(S(lambda));
     unlist_unbound:
      if (n > m) error_apply_toofew(S(lambda),l);
      do { pushSTACK(unbound); } while (--n != 0);
    } goto next_byte;
    CASE cod_unliststar: {      /* (UNLIST* n m) */
      var uintC n;
      var uintC m;
      U_operand(n);
      U_operand(m);
      var object l = value1;
      do {
        if (atomp(l)) goto unliststar_unbound;
        pushSTACK(Car(l)); l = Cdr(l);
      } while (--n != 0);
      pushSTACK(l);
      goto next_byte;
     unliststar_unbound:
      if (n > m) error_apply_toofew(S(lambda),l);
      do { pushSTACK(unbound); } while (--n != 0);
      pushSTACK(NIL);
    } goto next_byte;
    CASE cod_jmpifboundp: {     /* (JMPIFBOUNDP n label) */
      var uintL n;
      U_operand(n);
      var object obj = STACK_(n);
      if (!boundp(obj)) goto notjmp;
      VALUES1(obj);
    } JMP();
    CASE cod_boundp: {          /* (BOUNDP n) */
      var uintL n;
      U_operand(n);
      var object obj = STACK_(n);
      if (!boundp(obj)) goto code_nil; else goto code_t;
    }
    CASE cod_unbound_nil: {     /* (UNBOUND->NIL n) */
      var uintL n;
      U_operand(n);
      if (!boundp(STACK_(n))) { STACK_(n) = NIL; }
    } goto next_byte;
    /* ------------------- (9) Treatment of multiple values -------------- */
    CASE cod_values0:           /* (VALUES0) */
      VALUES0;
      goto next_byte;
    CASE cod_values1:           /* (VALUES1) */
      mv_count = 1;
      goto next_byte;
    CASE cod_stack_to_mv: {     /* (STACK-TO-MV n) */
      var uintL n;
      U_operand(n);
      if (n >= mv_limit) GOTO_ERROR(error_toomany_values);
      STACK_to_mv(n);
    } goto next_byte;
    CASE cod_mv_to_stack:       /* (MV-TO-STACK) */
      mv_to_STACK();            /* push values on Stack */
      goto next_byte;
    CASE cod_nv_to_stack: {     /* (NV-TO-STACK n) */
      var uintL n;
      U_operand(n);
      /* test for Stack-Overflow: */
      get_space_on_STACK(n*sizeof(gcv_object_t));
      /* push n values in the Stack: */
      var uintC count = mv_count;
      if (n==0) goto nv_to_stack_end; /* no value desired -> finished */
      /* at least 1 value desired */
      pushSTACK(value1);
      n--; if (n==0) goto nv_to_stack_end; /* only 1 value desired -> finished */
      if (count<=1) goto nv_to_stack_fill; /* only 1 value present -> fill with NILs */
      count--;
      { /* at least 2 values desired and present */
        var object* mvp = &mv_space[1];
        while (1) {
          pushSTACK(*mvp++);
          n--; if (n==0) goto nv_to_stack_end; /* no further value desired -> finished */
          count--; if (count==0) goto nv_to_stack_fill; /* no further value present -> fill with NILs */
        }
      }
     nv_to_stack_fill: /* fill up with n>0 NILs as additional values: */
      dotimespL(n,n, { pushSTACK(NIL); } );
       nv_to_stack_end: ;
    } goto next_byte;
    CASE cod_mv_to_list:        /* (MV-TO-LIST) */
      with_saved_context(
        /* push values on Stack and handicraft list out of it: */
        mv_to_list();
      );
      VALUES1(popSTACK());
      goto next_byte;
    CASE cod_list_to_mv:        /* (LIST-TO-MV) */
      list_to_mv(value1, GOTO_ERROR(error_toomany_values));
      goto next_byte;
    CASE cod_mvcallp:           /* (MVCALLP) */
      pushSP((aint)STACK);      /* save STACK */
      pushSTACK(value1);        /* save function to be executed */
      goto next_byte;
    CASE cod_mvcall: {          /* (MVCALL) */
      var gcv_object_t* FRAME; popSP( FRAME = (gcv_object_t*) ); /* Pointer to Arguments and Function */
      var object fun = NEXT(FRAME); /* Function */
      with_saved_context({
        var uintL argcount =  /* number of arguments on stack */
          STACK_item_count(STACK,FRAME);
        if (((uintL)~(uintL)0 > ca_limit_1) && (argcount > ca_limit_1)) {
          pushSTACK(fun);
          pushSTACK(S(multiple_value_call));
          /* ANSI CL 3.5.1.3. wants a PROGRAM-ERROR here. */
          error(program_error,
                GETTEXT("~S: too many arguments given to ~S"));
        }
        /* apply Function, lift Stack until below the Function: */
        funcall(fun,argcount);
        skipSTACK(1);         /* discard Function from STACK */
      });
    } goto next_byte;
    /* ------------------- (10) BLOCK ----------------------- */
    CASE cod_block_open: {      /* (BLOCK-OPEN n label) */
      /* occupies 3 STACK-entries and 1 SP-jmp_buf-entry and 2 SP-entries */
      var uintL n;
      var sintL label_dist;
      U_operand(n);
      S_operand(label_dist);
      /* create Block_Cons: */
      var object block_cons;
      with_saved_context(
        block_cons = allocate_cons();
        label_dist += index; /* CODEPTR+label_dist is the jump destination */
      );
      /* fill Block-Cons: (CONST n) as CAR */
      Car(block_cons) = TheCclosure(closure)->clos_consts[n];
      /* jump destination into SP: */
      pushSP(label_dist); pushSP((aint)closureptr);
      { /* build up CBLOCK-Frame: */
        var gcv_object_t* top_of_frame = STACK; /* Pointer above Frame */
        pushSTACK(block_cons);      /* Cons ( (CONST n) . ...) */
        var JMPBUF_on_SP(returner); /* memorize return-point */
        finish_entry_frame_1(CBLOCK,returner, goto block_return; );
      }
      /* store Framepointer in Block-Cons: */
      Cdr(block_cons) = make_framepointer(STACK);
    } goto next_byte;
   block_return: { /* jump to this label takes place, if the previously
                      built CBLOCK-Frame has catched a RETURN-FROM. */
      FREE_JMPBUF_on_SP();
      skipSTACK(2);               /* unwind CBLOCK-Frame and mark */
      Cdr(popSTACK()) = disabled; /* Block-Cons as Disabled */
      var uintL index;
      /* get closure back, byteptr_in:=label_byteptr_in : */
      popSP(closureptr = (gcv_object_t*) ); popSP(index = );
      closure = *closureptr;  /* fetch Closure from Stack */
      codeptr = TheSbvector(TheCclosure(closure)->clos_codevec);
      DEBUG_CHECK_BYTEPTR(CODEPTR + index);
      byteptr_in = CODEPTR + index;
    } goto next_byte;           /* continue interpretation at Label */
    CASE cod_block_close:       /* (BLOCK-CLOSE) */
      /* unwind CBLOCK-Frame: */
      #if STACKCHECKC
      if (!(framecode(STACK_0) == CBLOCK_frame_info))
        GOTO_ERROR(error_STACK_putt);
      #endif
      {
        FREE_JMPBUF_on_SP();
        skipSTACK(2);               /* unwind CBLOCK-Frame and mark */
        Cdr(popSTACK()) = disabled; /* Block-Cons as Disabled */
        skipSP(2); /* we know Destination-Closureptr and Destination-Label */
    } goto next_byte;           /* at Label continue interpretation */
    CASE cod_return_from: {     /* (RETURN-FROM n) */
      var uintL n;
      U_operand(n);
      var object block_cons = TheCclosure(closure)->clos_consts[n];
      if (eq(Cdr(block_cons),disabled))
        error_block_left(Car(block_cons));
      /* unwind upto Block-Frame, then jump to its routine for freeing: */
      FREE_DYNAMIC_ARRAY(private_SP_space);
      unwind_upto(uTheFramepointer(Cdr(block_cons)));
    }
    CASE cod_return_from_i: {   /* (RETURN-FROM-I k1 k2 n) */
      var uintL k1;
      var uintL k2;
      var uintL n;
      U_operand(k1);
      U_operand(k2);
      U_operand(n);
      var gcv_object_t* FRAME = (gcv_object_t*) SP_(k1+jmpbufsize*k2);
      var object block_cons = FRAME_(n);
      if (eq(Cdr(block_cons),disabled))
        error_block_left(Car(block_cons));
      /* unwind upto Block-Frame, then jump to its routine for freeing: */
      FREE_DYNAMIC_ARRAY(private_SP_space);
      unwind_upto(uTheFramepointer(Cdr(block_cons)));
    }
    /* ------------------- (11) TAGBODY ----------------------- */
    CASE cod_tagbody_open: {    /* (TAGBODY-OPEN n label1 ... labelm) */
      /* occupies 3+m STACK-Entries and 1 SP-jmp_buf-Entry and 1 SP-Entry */
      var uintL n;
      U_operand(n);
      /* create Tagbody-Cons: */
      var object tagbody_cons;
      with_saved_context(tagbody_cons = allocate_cons(););
      { /* fill Tagbody-Cons: Tag-Vector (CONST n) as CAR */
        var object tag_vector = TheCclosure(closure)->clos_consts[n];
        var uintL m = Svector_length(tag_vector);
        Car(tagbody_cons) = tag_vector;
        get_space_on_STACK(m*sizeof(gcv_object_t)); /* allocate space */
        /* push all labeli as Fixnums on the STACK: */
        var uintL count;
        dotimespL(count,m, {
          var const uintB* label_byteptr_in;
          L_operand(label_byteptr_in);
          pushSTACK(fixnum(label_byteptr_in - CODEPTR));
        });
      }
      /* jump destination in the SP: */
      pushSP((aint)closureptr);
      { /* build upCTAGBODY-Frame: */
        var gcv_object_t* top_of_frame = STACK; /* Pointer above Frame */
        pushSTACK(tagbody_cons);    /* Cons ( (CONST n) . ...) */
        var JMPBUF_on_SP(returner); /* memorize return-point */
        finish_entry_frame_1(CTAGBODY,returner, goto tagbody_go; );
      }
      /* store Framepointer in Tagbody-Cons: */
      Cdr(tagbody_cons) = make_framepointer(STACK);
    } goto next_byte;
   tagbody_go: { /* jump to this label takes place, if the previously
                    built CTAGBODY-Frame has catched a GO to Label nr. i. */
      var uintL m = Svector_length(Car(STACK_2)); /* Number of Labels */
      /* (I could also declare the m above as 'auto' and use it here.) */
      var uintL i = posfixnum_to_V(value1); /* Number of Labels */
      var uintL index = posfixnum_to_V(STACK_((m-i)+3)); /* labeli */
      /* get closure back, byteptr_in:=labeli_byteptr_in : */
      closureptr = (gcv_object_t*) SP_(jmpbufsize+0);
      closure = *closureptr;  /* fetch Closure from Stack */
      codeptr = TheSbvector(TheCclosure(closure)->clos_codevec);
      DEBUG_CHECK_BYTEPTR(CODEPTR + index);
      byteptr_in = CODEPTR + index;
    } goto next_byte;           /* continue interpretation at Label i */
    CASE cod_tagbody_close_nil: /* (TAGBODY-CLOSE-NIL) */
      VALUES1(NIL); /* value of Tagbody is NIL */
    CASE cod_tagbody_close:     /* (TAGBODY-CLOSE) */
      /* unwind CTAGBODY-Frame: */
      #if STACKCHECKC
      if (!(framecode(STACK_0) == CTAGBODY_frame_info))
        GOTO_ERROR(error_STACK_putt);
      #endif
      {
        FREE_JMPBUF_on_SP();
        var object tagbody_cons = STACK_2; /* Tagbody-Cons */
        Cdr(tagbody_cons) = disabled;      /* mark as Disabled */
        skipSTACK(3+Svector_length(Car(tagbody_cons)));
        skipSP(1);
    } goto next_byte;
    CASE cod_go: {              /* (GO n l) */
      var uintL n;
      var uintL l;
      U_operand(n);
      U_operand(l);
      var object tagbody_cons = /* (CONST n) */
        TheCclosure(closure)->clos_consts[n];
      if (eq(Cdr(tagbody_cons),disabled)) {
        var object tag_vector = Car(tagbody_cons);
        pushSTACK(tag_vector);
        pushSTACK(TheSvector(tag_vector)->data[l]); /* label l */
        pushSTACK(S(go));
        error(control_error,GETTEXT("(~S ~S): the tagbody of the tags ~S has already been left"));
      }
      /* value passed to the Tagbody:
         For CTAGBODY-Frames: 1+l as Fixnum,
         For ITAGBODY-Frames: the form-list for Tag nr. l. */
      var gcv_object_t* FRAME = uTheFramepointer(Cdr(tagbody_cons));
      VALUES1(framecode(FRAME_(0)) == CTAGBODY_frame_info
              ? fixnum(1+l)
              : (object)FRAME_(frame_bindings+2*l+1));
      /* unwind upto Tagbody-Frame, then jump to its Routine,
         which then jumps to Label l: */
      FREE_DYNAMIC_ARRAY(private_SP_space);
      unwind_upto(FRAME);
    }
    CASE cod_go_i: {            /* (GO-I k1 k2 n l) */
      var uintL k1;
      var uintL k2;
      var uintL n;
      var uintL l;
      U_operand(k1);
      U_operand(k2);
      U_operand(n);
      U_operand(l);
      var gcv_object_t* FRAME = (gcv_object_t*) SP_(k1+jmpbufsize*k2);
      var object tagbody_cons = FRAME_(n);
      if (eq(Cdr(tagbody_cons),disabled)) {
        var object tag_vector = Car(tagbody_cons);
        pushSTACK(tag_vector);
        pushSTACK(TheSvector(tag_vector)->data[l]); /* label l */
        pushSTACK(S(go));
        error(control_error,GETTEXT("(~S ~S): the tagbody of the tags ~S has already been left"));
      }
      /* value passed to Tagbody:
         For CTAGBODY-Frames 1+l as Fixnum. */
      FRAME = uTheFramepointer(Cdr(tagbody_cons));
      VALUES1(fixnum(1+l));
      /* unwind upto Tagbody-Frame, then jump to its Routine,
         which then jumps to Label l: */
      FREE_DYNAMIC_ARRAY(private_SP_space);
      unwind_upto(FRAME);
    }
    /* ------------------- (12) CATCH and THROW ----------------------- */
    CASE cod_catch_open:        /* (CATCH-OPEN label) */
      { /* occupies 3 STACK-Entries and 1 SP-jmp_buf-Entry and 2 SP-Entries */
        var const uintB* label_byteptr_in;
        L_operand(label_byteptr_in);
        /* save closureptr, label_byteptr_in: */
        pushSP(label_byteptr_in - CODEPTR); pushSP((aint)closureptr);
      }
      { /* build up Frame: */
        var gcv_object_t* top_of_frame = STACK;
        pushSTACK(value1);          /* Tag */
        var JMPBUF_on_SP(returner); /* memorize return-point */
        finish_entry_frame_1(CATCH,returner, goto catch_return; );
    } goto next_byte;
   catch_return: { /* jump to this label takes place, if the previoulsy
                      built Catch-Frame has catched a Throw. */
      FREE_JMPBUF_on_SP();
      skipSTACK(3);           /* unwind CATCH-Frame */
      var uintL index;
      /* get closure back, byteptr_in:=label_byteptr_in : */
      popSP(closureptr = (gcv_object_t*) ); popSP(index = );
      closure = *closureptr;  /* fetch Closure from Stack */
      codeptr = TheSbvector(TheCclosure(closure)->clos_codevec);
      DEBUG_CHECK_BYTEPTR(CODEPTR + index);
      byteptr_in = CODEPTR + index;
    } goto next_byte;           /* continue interpretation at Label */
    CASE cod_catch_close:       /* (CATCH-CLOSE) */
      /* a CATCH-Frame has to come: */
      #if STACKCHECKC
      if (!(framecode(STACK_0) == CATCH_frame_info))
        GOTO_ERROR(error_STACK_putt);
      #endif
      FREE_JMPBUF_on_SP();
      #if STACKCHECKC
      if (!(closureptr == (gcv_object_t*)SP_(0))) /* that Closureptr must be the current one */
        GOTO_ERROR(error_STACK_putt);
      #endif
      skipSP(2); skipSTACK(3);  /* unwind CATCH-Frame */
      goto next_byte;
    CASE cod_throw: {           /* (THROW) */
      var object tag = popSTACK();
      throw_to(tag);
      pushSTACK(tag);
      pushSTACK(S(throw));
      error(control_error,GETTEXT("~S: there is no CATCHer for tag ~S"));
    }
    /* ------------------- (13) UNWIND-PROTECT ----------------------- */
    CASE cod_uwp_open:          /* (UNWIND-PROTECT-OPEN label) */
      { /* occupies 2 STACK-Entries and 1 SP-jmp_buf-Entry and 2 SP-Entries */
        var const uintB* label_byteptr_in;
        L_operand(label_byteptr_in);
        /* save closureptr, label_byteptr_in: */
        pushSP(label_byteptr_in - CODEPTR); pushSP((aint)closureptr);
      }
      { /* build Frame: */
        var gcv_object_t* top_of_frame = STACK;
        var JMPBUF_on_SP(returner); /* memorize return-point */
        finish_entry_frame_1(UNWIND_PROTECT,returner, goto throw_save; );
    } goto next_byte;
   throw_save: /* jump to this label takes place, if the previously
                  built Unwind-Protect-Frame has stopped a Throw.
       unwind_protect_to_save is to be saved and jumped to at the end. */
      #if STACKCHECKC
      if (!(framecode(STACK_0) == UNWIND_PROTECT_frame_info)) {
        error(serious_condition,GETTEXT("STACK corrupted"));
      }
      #endif
      /* unwind Frame: */
      FREE_JMPBUF_on_SP();
      skipSTACK(2);
      {
        var uintL index;
        /* get closure back, byteptr_in:=label_byteptr_in : */
        popSP(closureptr = (gcv_object_t*) );
        popSP(index = );
        /* save unwind_protect_to_save: */
        pushSP((aint)unwind_protect_to_save.fun);
        pushSP((aint)unwind_protect_to_save.upto_frame);
        pushSP((aint)STACK); /* push Pointer above Frame additionally on the SP */
        /* move all values to the Stack: */
        mv_to_STACK();
        /* execute Cleanup-Forms: */
        closure = *closureptr;  /* fetch Closure from Stack */
        codeptr = TheSbvector(TheCclosure(closure)->clos_codevec);
        DEBUG_CHECK_BYTEPTR(CODEPTR + index);
        byteptr_in = CODEPTR + index;
    } goto next_byte;
    CASE cod_uwp_normal_exit:   /* (UNWIND-PROTECT-NORMAL-EXIT) */
      #if STACKCHECKC
      if (!(framecode(STACK_0) == UNWIND_PROTECT_frame_info))
        GOTO_ERROR(error_STACK_putt);
      if (!(closureptr == (gcv_object_t*)SP_(jmpbufsize+0))) /* that Closureptr must be the current one */
        GOTO_ERROR(error_STACK_putt);
      #endif
      /* unwind Frame:
       nothing to do, because closure and byteptr_in stay unmodified. */
      FREE_JMPBUF_on_SP(); skipSP(2);
      skipSTACK(2);
      /* dummy value for 'unwind_protect_to_save': */
      pushSP((aint)NULL); pushSP((aint)NULL); /* NULL,NULL -> uwp_continue */
      pushSP((aint)STACK); /* push Pointer above Frame additionally on the SP */
      /* move all values to the Stack: */
      mv_to_STACK();
      /* execute Cleanup-Forms: */
      goto next_byte;
    CASE cod_uwp_close:         /* (UNWIND-PROTECT-CLOSE) */
      { /* jump to this label takes place at the end of the Cleanup-Forms. */
        var gcv_object_t* oldSTACK; /* value of STACK before saveing the values */
        popSP( oldSTACK = (gcv_object_t*) );
        var uintL mvcount =     /* number of saved values on Stack */
          STACK_item_count(STACK,oldSTACK);
        if (mvcount >= mv_limit) GOTO_ERROR(error_toomany_values);
        STACK_to_mv(mvcount);
      }
      { /* return to the saved unwind_protect_to_save.fun : */
        var restartf_t fun;
        var gcv_object_t* arg;
        popSP( arg = (gcv_object_t*) ); popSP( fun = (restartf_t) );
        /* return to uwp_continue or uwp_jmpback or unwind_upto: */
        if (fun != NULL) {
          (*fun)(arg);          /* return to unwind_upto or similar. */
          NOTREACHED;
        }
        if (arg == (gcv_object_t*)NULL) {
          /* uwp_continue:
           jump to this label takes place, if after the execution of
           the Cleanup-Forms simply interpretation shall continue. */
          goto next_byte;
        } else {
          /* uwp_jmpback:
           jump to this label takes place, if after the execution of
           the Cleanup-Forms interpretation shall continue at the old
           location in the same Closure. */
          DEBUG_CHECK_BYTEPTR(CODEPTR + (uintP)arg);
          byteptr_in = CODEPTR + (uintP)arg;
          goto next_byte;
        }
      }
    CASE cod_uwp_cleanup:       /* (UNWIND-PROTECT-CLEANUP) */
      /* this is executed, if within the same Closure an execution
       of the Cleanup-Code is necessary. */
      #if STACKCHECKC
      if (!(framecode(STACK_0) == UNWIND_PROTECT_frame_info))
        GOTO_ERROR(error_STACK_putt);
      if (!(closureptr == (gcv_object_t*)SP_(jmpbufsize+0))) /* that Closureptr must be the current one */
        GOTO_ERROR(error_STACK_putt);
      #endif
      { /* closure remains, byteptr_in:=label_byteptr_in : */
        var uintL index = SP_(jmpbufsize+1);
        /* unwind Frame: */
        FREE_JMPBUF_on_SP(); skipSP(2);
        skipSTACK(2);
        /* Dummy-values for 'unwind_protect_to_save': */
        pushSP((aint)NULL);     /* NULL -> uwp_jmpback */
        pushSP(byteptr_in - CODEPTR);
        pushSP((aint)STACK); /* push Pointer above Frame additionally on the SP */
        /* move all values to the Stack: */
        mv_to_STACK();
        /* execute Cleanup-Forms: */
        DEBUG_CHECK_BYTEPTR(CODEPTR + index);
        byteptr_in = CODEPTR + index;
    } goto next_byte;
    /* ------------------- (14) HANDLER-BIND ----------------------- */
    CASE cod_handler_open: {    /* (HANDLER-OPEN n) */
      /* occupies 4 STACK-Entries */
      var uintL n;
      U_operand(n);
      /* build up Frame: */
      var gcv_object_t* top_of_frame = STACK; /* Pointer above Frame */
      pushSTACK(TheCclosure(closure)->clos_consts[n]);
      pushSTACK(closure);
      pushSTACK(fake_gcv_object((aint)(_SP_(0))));
      finish_frame(HANDLER);
    } goto next_byte;
    CASE cod_handler_begin_push: /* (HANDLER-BEGIN&PUSH) */
      /* builds up SP newly, occupies 1 SP-Entry and
         starts a new STACK-Region. */
      {
        var uintL count = (uintL)posfixnum_to_V(Car(handler_args.spdepth))
          + jmpbufsize * (uintL)posfixnum_to_V(Cdr(handler_args.spdepth));
        if (count > 0) {
          var SPint* oldsp = handler_args.sp; /* was formerly &SP_(0) */
          /* copy oldsp[0..count-1] to the current SP: */
          oldsp skipSPop count;
          dotimespL(count,count, { oldsp skipSPop -1; pushSP(*oldsp); } );
        }
      }
      pushSP((aint)handler_args.stack); /* Pointer above Handler-Frame */
      VALUES1(handler_args.condition);
      pushSTACK(value1);
      goto next_byte;
    /* ------------------- (15) a few Functions ----------------------- */
    CASE cod_not:               /* (NOT) */
      if (nullp(value1)) goto code_t; else goto code_nil;
    CASE cod_eq:                /* (EQ) */
      if (!eq(value1,popSTACK())) goto code_nil; else goto code_t;
    CASE cod_car: {             /* (CAR) */
      var object arg = value1;
      if (consp(arg)) {
        value1 = Car(arg);    /* CAR of a Cons */
      } else if (nullp(arg)) {
        /* (CAR NIL) = NIL: value1 remains NIL */
      } else
        with_saved_back_trace_subr(L(car),STACK STACKop -1,-1,
                                   error_list(arg); );
      mv_count=1;
    } goto next_byte;
    CASE cod_car_push: {        /* (CAR&PUSH) */
      var object arg = value1;
      if (consp(arg)) {
        pushSTACK(Car(arg));  /* CAR of a Cons */
      } else if (nullp(arg)) {
        pushSTACK(arg);       /* (CAR NIL) = NIL */
      } else
        with_saved_back_trace_subr(L(car),STACK STACKop -1,-1,
                                   error_list(arg); );
    } goto next_byte;
    CASE cod_load_car_push: {   /* (LOAD&CAR&PUSH n) */
      var uintL n;
      U_operand(n);
      var object arg = STACK_(n);
      if (consp(arg)) {
        pushSTACK(Car(arg));  /* CAR of a Cons */
      } else if (nullp(arg)) {
        pushSTACK(arg);       /* (CAR NIL) = NIL */
      } else
        with_saved_back_trace_subr(L(car),STACK STACKop -1,-1,
                                   error_list(arg); );
    } goto next_byte;
    CASE cod_load_car_store: {  /* (LOAD&CAR&STORE m n) */
      var uintL m;
      var uintL n;
      U_operand(m);
      U_operand(n);
      var object arg = STACK_(m);
      if (consp(arg)) {
        STACK_(n) = value1 = Car(arg); /* CAR of a Cons */
      } else if (nullp(arg)) {
        STACK_(n) = value1 = arg; /* (CAR NIL) = NIL */
      } else
        with_saved_back_trace_subr(L(car),STACK STACKop -1,-1,
                                   error_list(arg); );
      mv_count=1;
    } goto next_byte;
    CASE cod_cdr: {             /* (CDR) */
      var object arg = value1;
      if (consp(arg)) {
        value1 = Cdr(arg);    /* CDR of a Cons */
      } else if (nullp(arg)) {
        /* (CDR NIL) = NIL: value1 remains NIL */
      } else
        with_saved_back_trace_subr(L(cdr),STACK STACKop -1,-1,
                                   error_list(arg); );
      mv_count=1;
    } goto next_byte;
    CASE cod_cdr_push: {        /* (CDR&PUSH) */
      var object arg = value1;
      if (consp(arg)) {
        pushSTACK(Cdr(arg));  /* CDR of a Cons */
      } else if (nullp(arg)) {
        pushSTACK(arg);       /* (CDR NIL) = NIL */
      } else
        with_saved_back_trace_subr(L(cdr),STACK STACKop -1,-1,
                                   error_list(arg); );
    } goto next_byte;
    CASE cod_load_cdr_push: {   /* (LOAD&CDR&PUSH n) */
      var uintL n;
      U_operand(n);
      var object arg = STACK_(n);
      if (consp(arg)) {
        pushSTACK(Cdr(arg));  /* CDR of a Cons */
      } else if (nullp(arg)) {
        pushSTACK(arg);       /* (CDR NIL) = NIL */
      } else
        with_saved_back_trace_subr(L(cdr),STACK STACKop -1,-1,
                                   error_list(arg); );
    } goto next_byte;
    CASE cod_load_cdr_store: {  /* (LOAD&CDR&STORE n) */
      var uintL n;
      U_operand(n);
      var gcv_object_t* arg_ = &STACK_(n);
      var object arg = *arg_;
      if (consp(arg)) {
        *arg_ = value1 = Cdr(arg); /* CDR of a Cons */
      } else if (nullp(arg)) {
        value1 = arg;         /* (CDR NIL) = NIL */
      } else
        with_saved_back_trace_subr(L(cdr),STACK STACKop -1,-1,
                                   error_list(arg); );
      mv_count=1;
    } goto next_byte;
    CASE cod_cons: {            /* (CONS) */
      pushSTACK(value1);
      /* request Cons: */
      var object new_cons;
      with_saved_context( { new_cons = allocate_cons(); } );
      /* fill Cons: */
      Cdr(new_cons) = popSTACK();
      Car(new_cons) = popSTACK();
      VALUES1(new_cons);
    } goto next_byte;
    CASE cod_cons_push: {       /* (CONS&PUSH) */
      pushSTACK(value1);
      /* request Cons: */
      var object new_cons;
      with_saved_context( { new_cons = allocate_cons(); } );
      /* fill Cons: */
      Cdr(new_cons) = popSTACK();
      Car(new_cons) = STACK_0;
      STACK_0 = new_cons;
    } goto next_byte;
    CASE cod_load_cons_store: { /* (LOAD&CONS&STORE n) */
      var uintL n;
      U_operand(n);
      /* request Cons: */
      var object new_cons;
      with_saved_context( { new_cons = allocate_cons(); } );
      /* fill Cons: */
      Car(new_cons) = popSTACK();
      var gcv_object_t* arg_ = &STACK_(n);
      Cdr(new_cons) = *arg_;
      VALUES1(*arg_ = new_cons);
    } goto next_byte;
    {var object symbol;
     var object fdef;
     #define CHECK_FDEF()                                                   \
       if (!symbolp(symbol))                                                \
         with_saved_back_trace_subr(L(symbol_function),STACK STACKop -1,-1, \
           symbol = check_symbol(symbol); );                                \
       fdef = Symbol_function(symbol);                                      \
       if (!boundp(fdef))                                                   \
         /* (symbol may be not the actual function-name, for e.g.           \
            (FUNCTION (SETF FOO)) shows as (SYMBOL-FUNCTION '#:|(SETF FOO)|),\
            but that should be enough for the error message.) */            \
         fdef = check_fdefinition(symbol,S(symbol_function))
    CASE cod_symbol_function:   /* (SYMBOL-FUNCTION) */
      symbol = value1;
      CHECK_FDEF();
      VALUES1(fdef);
      goto next_byte;
    CASE cod_const_symbol_function: { /* (CONST&SYMBOL-FUNCTION n) */
      var uintL n;
      U_operand(n);
      symbol = TheCclosure(closure)->clos_consts[n];
    } CHECK_FDEF();
      VALUES1(fdef);
      goto next_byte;
    CASE cod_const_symbol_function_push: { /* (CONST&SYMBOL-FUNCTION&PUSH n) */
      var uintL n;
      U_operand(n);
      symbol = TheCclosure(closure)->clos_consts[n];
    } CHECK_FDEF();
      pushSTACK(fdef);
      goto next_byte;
    CASE cod_const_symbol_function_store: { /* (CONST&SYMBOL-FUNCTION&STORE n k) */
      var uintL n;
      U_operand(n);
      symbol = TheCclosure(closure)->clos_consts[n];
    } CHECK_FDEF(); {
      var uintL k;
      U_operand(k);
      STACK_(k) = value1 = fdef; mv_count=1;
    } goto next_byte;
    }
    {var object vec; var object index;
    CASE cod_svref:             /* (SVREF) */
      /* STACK_0 must be a Simple-Vector: */
      if (!simple_vector_p(STACK_0)) goto svref_not_a_svector;
      vec = popSTACK();         /* Simple-Vector */
      index = value1;
      { /* and the Index must be Fixnum >= 0, < length(vec) : */
        var uintV i;
        if (!(posfixnump(index)
              && ((i = posfixnum_to_V(index)) < Svector_length(vec))))
          goto svref_not_an_index;
        VALUES1(TheSvector(vec)->data[i]); /* indexed Element as value */
    } goto next_byte;
    CASE cod_svset:             /* (SVSET) */
      /* STACK_0 must be a Simple-Vector: */
      if (!simple_vector_p(STACK_0)) goto svref_not_a_svector;
      vec = popSTACK();         /* Simple-Vector */
      index = value1;
      { /* and the Index must be a Fixnum >=0, <Length(vec) : */
        var uintV i;
        if (!(posfixnump(index)
              && ((i = posfixnum_to_V(index)) < Svector_length(vec))))
          goto svref_not_an_index;
        VALUES1(TheSvector(vec)->data[i] = popSTACK()); /* put in new element */
    } goto next_byte;
    svref_not_a_svector:         /* Non-Simple-Vector in STACK_0 */
      { error_no_svector(S(svref),STACK_0); }
    svref_not_an_index:    /* unsuitable Index in index, for Vector vec */
      pushSTACK(vec);
      pushSTACK(index);
      pushSTACK(index);         /* TYPE-ERROR slot DATUM */
      {
        var object tmp;
        pushSTACK(S(integer)); pushSTACK(Fixnum_0); pushSTACK(UL_to_I(Svector_length(vec)));
        tmp = listof(1); pushSTACK(tmp); tmp = listof(3);
        pushSTACK(tmp);         /* TYPE-ERROR slot EXPECTED-TYPE */
      }
      pushSTACK(STACK_(1+2));   /* vec */
      pushSTACK(STACK_(0+3));   /* index */
      pushSTACK(S(svref));
      error(type_error,GETTEXT("~S: ~S is not a correct index into ~S"));
    }
    CASE cod_list: {            /* (LIST n) */
      var uintC n;
      U_operand(n);
      with_saved_context( { value1 = listof(n); mv_count=1; } );
    } goto next_byte;
    CASE cod_list_push: {       /* (LIST&PUSH n) */
      var uintC n;
      U_operand(n);
      with_saved_context( { object res = listof(n); pushSTACK(res); } );
    } goto next_byte;
    CASE cod_liststar: { /* (LIST* n) */
      var uintC n;
      U_operand(n);
      with_saved_context({
        pushSTACK(value1);
        dotimespC(n,n, {
          var object new_cons = allocate_cons();
          Cdr(new_cons) = popSTACK();
          Car(new_cons) = STACK_0;
          STACK_0 = new_cons;
        });
        value1 = popSTACK(); mv_count=1;
      });
    } goto next_byte;
    CASE cod_liststar_push: {   /* (LIST*&PUSH n) */
      var uintC n;
      U_operand(n);
      with_saved_context({
        pushSTACK(value1);
        dotimespC(n,n, {
          var object new_cons = allocate_cons();
          Cdr(new_cons) = popSTACK();
          Car(new_cons) = STACK_0;
          STACK_0 = new_cons;
        });
      });
    } goto next_byte;
    /* ------------------- (16) combined Operations ----------------------- */
    CASE cod_nil_store: {       /* (NIL&STORE n) */
      var uintL n;
      U_operand(n);
      STACK_(n) = value1 = NIL; mv_count=1;
    } goto next_byte;
    CASE cod_t_store: {         /* (T&STORE n) */
      var uintL n;
      U_operand(n);
      STACK_(n) = value1 = T; mv_count=1;
    } goto next_byte;
    CASE cod_calls1_store:      /* (CALLS1&STORE n k) */
      CALLS1();
      goto store;
    CASE cod_calls2_store:      /* (CALLS2&STORE n k) */
      CALLS2();
      goto store;
    CASE cod_callsr_store:      /* (CALLSR&STORE m n k) */
      CALLSR();
      goto store;
    /* Increment. Optimized specifically for Fixnums >=0. */
    #define INC(arg,statement)  \
      { if (posfixnump(arg) /* Fixnum >= 0 and < most-positive-fixnum ? */ \
            && !eq(arg,fixnum(vbitm(oint_data_len)-1))) {              \
          arg = fixnum_inc(arg,1); statement;                          \
        } else {                                                       \
          with_saved_context(                                          \
            /* funcall(L(plus_one),1): */                              \
            pushSTACK(arg);                                            \
            with_saved_back_trace_subr(L(plus_one),STACK,1,            \
              { C_plus_one(); });                                      \
          );                                                           \
          arg = value1;                                                \
        }                                                              \
      }
    /* Decrement. Optimized specifically for Fixnums >=0. */
    #define DEC(arg,statement)  \
      { if (posfixnump(arg) && !eq(arg,Fixnum_0)) { /* Fixnum > 0 ? */ \
          arg = fixnum_inc(arg,-1); statement;                     \
        } else {                                                   \
          with_saved_context(                                      \
            /* funcall(L(minus_one),1): */                         \
            pushSTACK(arg);                                        \
            with_saved_back_trace_subr(L(minus_one),STACK,1,       \
              { C_minus_one(); });                                 \
          );                                                       \
          arg = value1;                                            \
        }                                                          \
      }
    CASE cod_load_inc_push: {   /* (LOAD&INC&PUSH n) */
      var uintL n;
      U_operand(n);
      var object arg = STACK_(n);
      INC(arg,);              /* increment */
      pushSTACK(arg);
    } goto next_byte;
    CASE cod_load_inc_store: {  /* (LOAD&INC&STORE n) */
      var uintL n;
      U_operand(n);
      var gcv_object_t* arg_ = &STACK_(n);
      var object arg = *arg_;
      INC(arg,mv_count=1);    /* increment, one value */
      value1 = *arg_ = arg;
    } goto next_byte;
    CASE cod_load_dec_push: {   /* (LOAD&DEC&PUSH n) */
      var uintL n;
      U_operand(n);
      var object arg = STACK_(n);
      DEC(arg,);              /* decrement */
      pushSTACK(arg);
    } goto next_byte;
    CASE cod_load_dec_store: {  /* (LOAD&DEC&STORE n) */
      var uintL n;
      U_operand(n);
      var gcv_object_t* arg_ = &STACK_(n);
      var object arg = *arg_;
      DEC(arg,mv_count=1);    /* decrement, one value */
      value1 = *arg_ = arg;
    } goto next_byte;
    CASE cod_call1_jmpif:       /* (CALL1&JMPIF n label) */
      CALL1();
      if (!nullp(value1)) goto jmp; else goto notjmp;
    CASE cod_call1_jmpifnot:    /* (CALL1&JMPIFNOT n label) */
      CALL1();
      if (nullp(value1)) goto jmp; else goto notjmp;
    CASE cod_call2_jmpif:       /* (CALL2&JMPIF n label) */
      CALL2();
      if (!nullp(value1)) goto jmp; else goto notjmp;
    CASE cod_call2_jmpifnot:    /* (CALL2&JMPIFNOT n label) */
      CALL2();
      if (nullp(value1)) goto jmp; else goto notjmp;
    CASE cod_calls1_jmpif:      /* (CALLS1&JMPIF n label) */
      CALLS1();
      if (!nullp(value1)) goto jmp; else goto notjmp;
    CASE cod_calls1_jmpifnot:   /* (CALLS1&JMPIFNOT n label) */
      CALLS1();
      if (nullp(value1)) goto jmp; else goto notjmp;
    CASE cod_calls2_jmpif:      /* (CALLS2&JMPIF n label) */
      CALLS2();
      if (!nullp(value1)) goto jmp; else goto notjmp;
    CASE cod_calls2_jmpifnot:   /* (CALLS2&JMPIFNOT n label) */
      CALLS2();
      if (nullp(value1)) goto jmp; else goto notjmp;
    CASE cod_callsr_jmpif:      /* (CALLSR&JMPIF m n label) */
      CALLSR();
      if (!nullp(value1)) goto jmp; else goto notjmp;
    CASE cod_callsr_jmpifnot:   /* (CALLSR&JMPIFNOT m n label) */
      CALLSR();
      if (nullp(value1)) goto jmp; else goto notjmp;
    CASE cod_load_jmpif: {      /* (LOAD&JMPIF n label) */
      var uintL n;
      U_operand(n);
      mv_count=1;
      if (!nullp(value1 = STACK_(n))) goto jmp; else goto notjmp;
    }
    CASE cod_load_jmpifnot: {   /* (LOAD&JMPIFNOT n label) */
      var uintL n;
      U_operand(n);
      mv_count=1;
      if (nullp(value1 = STACK_(n))) goto jmp; else goto notjmp;
    }
    CASE cod_apply_skip_ret: {  /* (APPLY&SKIP&RET n k) */
      var uintL n;
      var uintL k;
      U_operand(n);
      U_operand(k);
      var object fun = STACK_(n); /* Function */
      with_saved_context({
        apply(fun,n,value1);  /* call Function */
        skipSTACK(k+1);   /* discard Function and others from Stack */
        goto finished;    /* return (jump) to caller */
      });                 /* the context is not restored */
    }
    CASE cod_funcall_skip_retgf: { /* (FUNCALL&SKIP&RETGF n k) */
      var uintL n;
      var uintL k;
      U_operand(n);
      U_operand(k);
      var object fun = STACK_(n); /* Function */
      var uintL r = ((Codevec)codeptr)->ccv_numreq;
      var uintB flags = ((Codevec)codeptr)->ccv_flags;
      with_saved_context({
        funcall(fun,n);       /* call Function */
        if (flags & bit(3)) { /* call inhibition? */
          skipSTACK(k+1);
          mv_count=1;
          goto finished;      /* return (jump) to caller */
        }
        k -= r;
        if (flags & bit(0)) {
          skipSTACK(k); apply(value1,r,popSTACK());
        } else {
          skipSTACK(k+1); funcall(value1,r);
        }
        goto finished;        /* return (jump) to caller */
      });                     /* the context is not restored */
    }
    /* ------------------- (17) short codes ----------------------- */
    CASE cod_load0:             /* (LOAD.S 0) */
    CASE cod_load1:             /* (LOAD.S 1) */
    CASE cod_load2:             /* (LOAD.S 2) */
    CASE cod_load3:             /* (LOAD.S 3) */
    CASE cod_load4:             /* (LOAD.S 4) */
    CASE cod_load5:             /* (LOAD.S 5) */
    CASE cod_load6:             /* (LOAD.S 6) */
    CASE cod_load7:             /* (LOAD.S 7) */
    CASE cod_load8:             /* (LOAD.S 8) */
    CASE cod_load9:             /* (LOAD.S 9) */
    CASE cod_load10:            /* (LOAD.S 10) */
    CASE cod_load11:            /* (LOAD.S 11) */
    CASE cod_load12:            /* (LOAD.S 12) */
    CASE cod_load13:            /* (LOAD.S 13) */
    CASE cod_load14:            /* (LOAD.S 14) */
      VALUES1(STACK_(*(byteptr_in-1) - cod_load0));
      goto next_byte;
    CASE cod_load_push0:        /* (LOAD&PUSH.S 0) */
    CASE cod_load_push1:        /* (LOAD&PUSH.S 1) */
    CASE cod_load_push2:        /* (LOAD&PUSH.S 2) */
    CASE cod_load_push3:        /* (LOAD&PUSH.S 3) */
    CASE cod_load_push4:        /* (LOAD&PUSH.S 4) */
    CASE cod_load_push5:        /* (LOAD&PUSH.S 5) */
    CASE cod_load_push6:        /* (LOAD&PUSH.S 6) */
    CASE cod_load_push7:        /* (LOAD&PUSH.S 7) */
    CASE cod_load_push8:        /* (LOAD&PUSH.S 8) */
    CASE cod_load_push9:        /* (LOAD&PUSH.S 9) */
    CASE cod_load_push10:       /* (LOAD&PUSH.S 10) */
    CASE cod_load_push11:       /* (LOAD&PUSH.S 11) */
    CASE cod_load_push12:       /* (LOAD&PUSH.S 12) */
    CASE cod_load_push13:       /* (LOAD&PUSH.S 13) */
    CASE cod_load_push14:       /* (LOAD&PUSH.S 14) */
    CASE cod_load_push15:       /* (LOAD&PUSH.S 15) */
    CASE cod_load_push16:       /* (LOAD&PUSH.S 16) */
    CASE cod_load_push17:       /* (LOAD&PUSH.S 17) */
    CASE cod_load_push18:       /* (LOAD&PUSH.S 18) */
    CASE cod_load_push19:       /* (LOAD&PUSH.S 19) */
    CASE cod_load_push20:       /* (LOAD&PUSH.S 20) */
    CASE cod_load_push21:       /* (LOAD&PUSH.S 21) */
    CASE cod_load_push22:       /* (LOAD&PUSH.S 22) */
    CASE cod_load_push23:       /* (LOAD&PUSH.S 23) */
    CASE cod_load_push24:       /* (LOAD&PUSH.S 24) */
      pushSTACK(STACK_(*(byteptr_in-1) - cod_load_push0));
      goto next_byte;
    CASE cod_const0:            /* (CONST.S 0) */
    CASE cod_const1:            /* (CONST.S 1) */
    CASE cod_const2:            /* (CONST.S 2) */
    CASE cod_const3:            /* (CONST.S 3) */
    CASE cod_const4:            /* (CONST.S 4) */
    CASE cod_const5:            /* (CONST.S 5) */
    CASE cod_const6:            /* (CONST.S 6) */
    CASE cod_const7:            /* (CONST.S 7) */
    CASE cod_const8:            /* (CONST.S 8) */
    CASE cod_const9:            /* (CONST.S 9) */
    CASE cod_const10:           /* (CONST.S 10) */
    CASE cod_const11:           /* (CONST.S 11) */
    CASE cod_const12:           /* (CONST.S 12) */
    CASE cod_const13:           /* (CONST.S 13) */
    CASE cod_const14:           /* (CONST.S 14) */
    CASE cod_const15:           /* (CONST.S 15) */
    CASE cod_const16:           /* (CONST.S 16) */
    CASE cod_const17:           /* (CONST.S 17) */
    CASE cod_const18:           /* (CONST.S 18) */
    CASE cod_const19:           /* (CONST.S 19) */
    CASE cod_const20:           /* (CONST.S 20) */
      VALUES1(TheCclosure(closure)->clos_consts[*(byteptr_in-1) - cod_const0]);
      goto next_byte;
    CASE cod_const_push0:       /* (CONST&PUSH.S 0) */
    CASE cod_const_push1:       /* (CONST&PUSH.S 1) */
    CASE cod_const_push2:       /* (CONST&PUSH.S 2) */
    CASE cod_const_push3:       /* (CONST&PUSH.S 3) */
    CASE cod_const_push4:       /* (CONST&PUSH.S 4) */
    CASE cod_const_push5:       /* (CONST&PUSH.S 5) */
    CASE cod_const_push6:       /* (CONST&PUSH.S 6) */
    CASE cod_const_push7:       /* (CONST&PUSH.S 7) */
    CASE cod_const_push8:       /* (CONST&PUSH.S 8) */
    CASE cod_const_push9:       /* (CONST&PUSH.S 9) */
    CASE cod_const_push10:      /* (CONST&PUSH.S 10) */
    CASE cod_const_push11:      /* (CONST&PUSH.S 11) */
    CASE cod_const_push12:      /* (CONST&PUSH.S 12) */
    CASE cod_const_push13:      /* (CONST&PUSH.S 13) */
    CASE cod_const_push14:      /* (CONST&PUSH.S 14) */
    CASE cod_const_push15:      /* (CONST&PUSH.S 15) */
    CASE cod_const_push16:      /* (CONST&PUSH.S 16) */
    CASE cod_const_push17:      /* (CONST&PUSH.S 17) */
    CASE cod_const_push18:      /* (CONST&PUSH.S 18) */
    CASE cod_const_push19:      /* (CONST&PUSH.S 19) */
    CASE cod_const_push20:      /* (CONST&PUSH.S 20) */
    CASE cod_const_push21:      /* (CONST&PUSH.S 21) */
    CASE cod_const_push22:      /* (CONST&PUSH.S 22) */
    CASE cod_const_push23:      /* (CONST&PUSH.S 23) */
    CASE cod_const_push24:      /* (CONST&PUSH.S 24) */
    CASE cod_const_push25:      /* (CONST&PUSH.S 25) */
    CASE cod_const_push26:      /* (CONST&PUSH.S 26) */
    CASE cod_const_push27:      /* (CONST&PUSH.S 27) */
    CASE cod_const_push28:      /* (CONST&PUSH.S 28) */
    CASE cod_const_push29:      /* (CONST&PUSH.S 29) */
      pushSTACK(TheCclosure(closure)->clos_consts[*(byteptr_in-1) - cod_const_push0]);
      goto next_byte;
    CASE cod_store0:            /* (STORE.S 0) */
    CASE cod_store1:            /* (STORE.S 1) */
    CASE cod_store2:            /* (STORE.S 2) */
    CASE cod_store3:            /* (STORE.S 3) */
    CASE cod_store4:            /* (STORE.S 4) */
    CASE cod_store5:            /* (STORE.S 5) */
    CASE cod_store6:            /* (STORE.S 6) */
    CASE cod_store7:            /* (STORE.S 7) */
      STACK_(*(byteptr_in-1) - cod_store0) = value1; mv_count=1;
      goto next_byte;
    /* ------------------- miscellaneous ----------------------- */
    default:
      /* undefined Code */
      pushSTACK(fixnum(byteptr_in-&codeptr->data[0]-1)); /* bad byte number */
      pushSTACK(closure);                             /* Closure */
      error(serious_condition,GETTEXT("undefined bytecode in ~S at byte ~S"));
  }
 #if DEBUG_BYTECODE
 error_byteptr_in: {
    pushSTACK(fixnum(byteptr_max));
    pushSTACK(fixnum(byteptr_min));
    pushSTACK(fixnum(byteptr_in - codeptr->data));
    pushSTACK(sfixnum(byteptr_bad_jump));
    pushSTACK(closure);
    error(error_condition,GETTEXT("~S: jump by ~S takes ~S outside [~S;~S]"));
  }
 #endif
 error_toomany_values: {
    pushSTACK(closure);
    error(error_condition,GETTEXT("~S: too many return values"));
  }
 #if STACKCHECKC
 error_STACK_putt: {
    pushSTACK(fixnum(byteptr_in - codeptr->data - byteptr_min)); /* PC */
    pushSTACK(closure);                       /* FUNC */
    error(serious_condition,GETTEXT("Corrupted STACK in ~S at byte ~S"));
  }
 #endif
 finished:
  FREE_DYNAMIC_ARRAY(private_SP_space);
  return;
}

/* ensure that the function has been jit-compiled and run it */
static Values jitc_run (object closure_in, Sbvector codeptr,
                        const uintB* byteptr_in) {
  struct jitc_object *jo;
  // if (!fpointerp(cclosure_jitc(closure_in))) {
  //   pushSTACK(closure_in);
  //   object fp = allocate_fpointer(NULL);
  //   closure_in = popSTACK();
  //   
  //   cclosure_jitc(closure_in) = fp;
  // }
  jitc_compile(closure_in,codeptr,byteptr_in);
}