// Emscripten 6 no longer reads Module.quit, and its Node default sets process.exitCode before
// throwing, which outlives an abort the caller caught. This restores the option.
if (Module["quit"]) quit_ = Module["quit"];
