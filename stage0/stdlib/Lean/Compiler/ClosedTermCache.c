// Lean compiler output
// Module: Lean.Compiler.ClosedTermCache
// Imports: Init Lean.Environment
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isClosedTermName___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_50____closed__1;
LEAN_EXPORT lean_object* l_Lean_ClosedTermCache_constNames___default;
static lean_object* l_Lean_ClosedTermCache_map___default___closed__2;
static lean_object* l_Lean_cacheClosedTermName___closed__1;
LEAN_EXPORT lean_object* lean_cache_closed_term_name(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ClosedTermCache_map___default___closed__1;
extern lean_object* l_Lean_Expr_instHashableExpr;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_closedTermCacheExt;
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_ClosedTermCache_map___default;
static lean_object* l_Lean_ClosedTermCache_map___default___closed__3;
static lean_object* l_Lean_instInhabitedClosedTermCache___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedClosedTermCache;
LEAN_EXPORT uint8_t l_Lean_isClosedTermName(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_closed_term_name(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_50_(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_ClosedTermCache_map___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_ClosedTermCache_map___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ClosedTermCache_map___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ClosedTermCache_map___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ClosedTermCache_map___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ClosedTermCache_map___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ClosedTermCache_map___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_ClosedTermCache_constNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ClosedTermCache_map___default___closed__3;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedClosedTermCache___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_50____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedClosedTermCache___closed__1;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_50_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_50____closed__1;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Expr_instBEqExpr;
x_6 = l_Lean_Expr_instHashableExpr;
lean_inc(x_2);
x_7 = l_Std_PersistentHashMap_insert___rarg(x_5, x_6, x_4, x_1, x_2);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_8, x_2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_cacheClosedTermName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_closedTermCacheExt;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_cache_closed_term_name(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_cacheClosedTermName___lambda__1), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Lean_cacheClosedTermName___closed__1;
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_5, x_1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_get_closed_term_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_instInhabitedClosedTermCache;
x_4 = l_Lean_cacheClosedTermName___closed__1;
x_5 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_3, x_4, x_1);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Expr_instBEqExpr;
x_8 = l_Lean_Expr_instHashableExpr;
x_9 = l_Std_PersistentHashMap_find_x3f___rarg(x_7, x_8, x_6, x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_isClosedTermName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Lean_instInhabitedClosedTermCache;
x_4 = l_Lean_cacheClosedTermName___closed__1;
x_5 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_3, x_4, x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_NameSet_contains(x_6, x_2);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isClosedTermName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isClosedTermName(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ClosedTermCache(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ClosedTermCache_map___default___closed__1 = _init_l_Lean_ClosedTermCache_map___default___closed__1();
lean_mark_persistent(l_Lean_ClosedTermCache_map___default___closed__1);
l_Lean_ClosedTermCache_map___default___closed__2 = _init_l_Lean_ClosedTermCache_map___default___closed__2();
lean_mark_persistent(l_Lean_ClosedTermCache_map___default___closed__2);
l_Lean_ClosedTermCache_map___default___closed__3 = _init_l_Lean_ClosedTermCache_map___default___closed__3();
lean_mark_persistent(l_Lean_ClosedTermCache_map___default___closed__3);
l_Lean_ClosedTermCache_map___default = _init_l_Lean_ClosedTermCache_map___default();
lean_mark_persistent(l_Lean_ClosedTermCache_map___default);
l_Lean_ClosedTermCache_constNames___default = _init_l_Lean_ClosedTermCache_constNames___default();
lean_mark_persistent(l_Lean_ClosedTermCache_constNames___default);
l_Lean_instInhabitedClosedTermCache___closed__1 = _init_l_Lean_instInhabitedClosedTermCache___closed__1();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache___closed__1);
l_Lean_instInhabitedClosedTermCache = _init_l_Lean_instInhabitedClosedTermCache();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache);
l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_50____closed__1 = _init_l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_50____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_50____closed__1);
res = l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_50_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_closedTermCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_closedTermCacheExt);
lean_dec_ref(res);
l_Lean_cacheClosedTermName___closed__1 = _init_l_Lean_cacheClosedTermName___closed__1();
lean_mark_persistent(l_Lean_cacheClosedTermName___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
