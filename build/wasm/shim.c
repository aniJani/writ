#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <malloc.h>
#include <emscripten.h>
#include <lean/lean.h>

void lean_initialize_runtime_module(void);
uint8_t lean_string_validate_utf8(lean_object* bytes);
lean_object* lean_string_from_utf8_unchecked(lean_object* bytes);
lean_object* initialize_writ_WritWasm_Exports(uint8_t builtin);

lean_object* writ_lean_check(lean_object* a);
lean_object* writ_lean_digest(lean_object* a);
lean_object* writ_lean_canonical(lean_object* a);
lean_object* writ_lean_initial(lean_object* a, lean_object* b);
lean_object* writ_lean_step(lean_object* a, lean_object* b, lean_object* c);
lean_object* writ_lean_replay(lean_object* a);
lean_object* writ_lean_version(lean_object* unit);
lean_object* writ_lean_tombstone(lean_object* a, lean_object* b);
lean_object* writ_lean_inspect(lean_object* a, lean_object* b, lean_object* c);
lean_object* writ_lean_profile(lean_object* a);

/* 0: not started, 1: ready, -1: a module initializer failed (not retried). */
static int g_state = 0;

EMSCRIPTEN_KEEPALIVE int writ_init(void) {
  if (g_state == 0) {
    lean_initialize_runtime_module();
    /* Same sequence as the main() that Lean emits for an executable. */
    lean_set_panic_messages(false);
    lean_object* r = initialize_writ_WritWasm_Exports(1);
    lean_set_panic_messages(true);
    if (lean_io_result_is_ok(r)) {
      lean_io_mark_end_initialization();
      g_state = 1;
    } else {
      g_state = -1;
    }
    lean_dec_ref(r);
  }
  return g_state == 1 ? 0 : 1;
}

static uint8_t* copy_out(const char* s, size_t n, size_t* out_len) {
  uint8_t* p = malloc(n == 0 ? 1 : n);
  if (p == NULL) {
    *out_len = 0;
    return NULL;
  }
  memcpy(p, s, n);
  *out_len = n;
  return p;
}

static uint8_t* error_out(const char* msg, size_t* out_len) {
  return copy_out(msg, strlen(msg), out_len);
}

#define FN_COUNT 10

static const int arity[FN_COUNT + 1] = {0, 1, 1, 1, 2, 3, 1, 0, 2, 3, 1};

/* The Api input name of each argument, as in its error envelopes. The tombstone flag has none:
   the binding writes it, not the host. */
static const char* const input_names[FN_COUNT + 1][3] = {
  {NULL}, {"policy"}, {"json"}, {"json"}, {"policy", "digest"}, {"policy", "state", "event"},
  {"traces"}, {NULL}, {"ledger", NULL}, {"policy", "state", "time"}, {"json"},
};

static uint8_t* input_error(int fn, int i, int bad, size_t* out_len) {
  char buf[96];
  const char* what = bad ? "is not valid UTF-8" : "contains a NUL byte";
  const char* name = input_names[fn][i];
  int n = name != NULL
    ? snprintf(buf, sizeof buf, "{\"error\":\"input %c %s\",\"input\":\"%s\"}", 'a' + i, what, name)
    : snprintf(buf, sizeof buf, "{\"error\":\"input %c %s\"}", 'a' + i, what);
  return copy_out(buf, (size_t)n, out_len);
}

/* Builds a Lean string from untrusted bytes with the check `String.fromUTF8?` uses.
   A NUL is rejected too: no kernel input may contain one, and hosts that hand the
   bytes on as C strings would truncate there. On failure returns NULL and sets *bad
   to 0 for a NUL, 1 for invalid UTF-8. */
static lean_object* to_string(const uint8_t* p, size_t n, int* bad) {
  if (n > 0 && memchr(p, 0, n) != NULL) {
    *bad = 0;
    return NULL;
  }
  lean_object* bytes = lean_alloc_sarray(1, n, n);
  if (n > 0) memcpy(lean_sarray_cptr(bytes), p, n);
  if (!lean_string_validate_utf8(bytes)) {
    lean_dec(bytes);
    *bad = 1;
    return NULL;
  }
  return lean_string_from_utf8_unchecked(bytes);
}

EMSCRIPTEN_KEEPALIVE uint8_t* writ_call(int fn, const uint8_t* a, size_t an, const uint8_t* b, size_t bn,
                                        const uint8_t* c, size_t cn, size_t* out_len) {
  if (fn < 1 || fn > FN_COUNT) return error_out("{\"error\":\"unknown function code\"}", out_len);
  if (writ_init() != 0) return error_out("{\"error\":\"kernel initialization failed\"}", out_len);

  const uint8_t* ptrs[3] = {a, b, c};
  size_t lens[3] = {an, bn, cn};
  lean_object* args[3] = {NULL, NULL, NULL};
  for (int i = 0; i < arity[fn]; i++) {
    int bad = 0;
    args[i] = to_string(ptrs[i], lens[i], &bad);
    if (args[i] == NULL) {
      for (int j = 0; j < i; j++) lean_dec(args[j]);
      return input_error(fn, i, bad, out_len);
    }
  }

  /* The exports take their arguments owned, so the strings are consumed here. */
  lean_object* r;
  switch (fn) {
    case 1: r = writ_lean_check(args[0]); break;
    case 2: r = writ_lean_digest(args[0]); break;
    case 3: r = writ_lean_canonical(args[0]); break;
    case 4: r = writ_lean_initial(args[0], args[1]); break;
    case 5: r = writ_lean_step(args[0], args[1], args[2]); break;
    case 6: r = writ_lean_replay(args[0]); break;
    case 8: r = writ_lean_tombstone(args[0], args[1]); break;
    case 9: r = writ_lean_inspect(args[0], args[1], args[2]); break;
    case 10: r = writ_lean_profile(args[0]); break;
    default: r = writ_lean_version(lean_box(0)); break;
  }
  uint8_t* out = copy_out(lean_string_cstr(r), lean_string_size(r) - 1, out_len);
  lean_dec(r);
  return out;
}

EMSCRIPTEN_KEEPALIVE void writ_free(uint8_t* p) {
  free(p);
}

/* Diagnostic: bytes currently allocated from the malloc heap. HEAPU8.length cannot show a
   leak because the initial memory has megabytes of slack. */
EMSCRIPTEN_KEEPALIVE size_t writ_heap_used(void) {
  struct mallinfo mi = mallinfo();
  return (size_t)(unsigned)mi.uordblks;
}
