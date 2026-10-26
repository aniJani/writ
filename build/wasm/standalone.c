#include <stdint.h>
#include <wasi/api.h>
#include <lean/lean.h>

/* Linked only into the standalone module, with -Wl,--wrap=lean_io_get_random_bytes. Lean seeds
   IO.stdGenRef from IO.getRandomBytes while the module initializes, and the runtime reads
   /dev/urandom, which a standalone module cannot open: Emscripten's standalone open() admits only
   the standard streams. This asks the WASI host for the bytes instead. */
lean_obj_res __wrap_lean_io_get_random_bytes(size_t nbytes) {
  if (lean_alloc_sarray_would_overflow(1, nbytes)) {
    return lean_io_result_mk_error(lean_decode_io_error(__WASI_ERRNO_NOMEM, NULL));
  }
  lean_object* res = lean_alloc_sarray(1, nbytes, nbytes);
  if (nbytes > 0) {
    __wasi_errno_t err = __wasi_random_get(lean_sarray_cptr(res), nbytes);
    if (err != __WASI_ERRNO_SUCCESS) {
      lean_dec(res);
      return lean_io_result_mk_error(lean_decode_io_error(err, NULL));
    }
  }
  return lean_io_result_mk_ok(res);
}
