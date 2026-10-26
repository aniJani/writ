/* Force-included (-include) before every Lean-generated C file of the WASM build.

   The C comes from the 64-bit Lean compiler, which types a Nat literal up to 2^63-1 as a tagged
   scalar (Lean.maxSmallNat of the host) and so emits no reference counting for it. On wasm32 a
   Nat above 2^31-1 is a heap object, so such a literal would leak on every evaluation, and an
   unbalanced dec on a copy of it could free it while still in use. Each literal call site below
   instead builds its value once and marks it persistent: reference counting on a persistent
   object is a no-op, matching what the compiler assumed, and nothing is allocated again.
   Generated C only calls these two functions for literals (see EmitC.emitLit). */
#pragma once
#include <lean/lean.h>

static inline lean_object* writ_persistent_nat(lean_object* o) {
  if (!lean_is_scalar(o)) lean_mark_persistent(o);
  return o;
}

#define lean_unsigned_to_nat(n) __extension__({                                     \
  static lean_object* writ_lit_;                                                    \
  (n) <= LEAN_MAX_SMALL_NAT ? lean_box(n)                                          \
    : (writ_lit_ ? writ_lit_ : (writ_lit_ = writ_persistent_nat(lean_big_usize_to_nat(n)))); })

#define lean_cstr_to_nat(s) __extension__({                                         \
  static lean_object* writ_lit_;                                                    \
  writ_lit_ ? writ_lit_ : (writ_lit_ = writ_persistent_nat(lean_cstr_to_nat(s))); })
