import { MemoryStore } from "../src/index.js"
import { storeSuite } from "./store-suite.js"

storeSuite("MemoryStore", () => new MemoryStore())
