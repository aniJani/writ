#include <string.h>

/* The only libuv symbol the linked runtime still reaches: io.cpp formats the message of an
   IO error with it. libuv error codes are negated errno values on Unix, which Emscripten
   follows, so libc's text for the same errno stands in for libuv's. See build/wasm/README.md. */
const char* uv_strerror(int err) {
  return strerror(-err);
}
