import type { Kernel } from "./kernel.js"
import type { CallStatus, Disposition, ProfileEnvelope, Verdict } from "./types.js"

const ID = "mcp-tool-approval"

/**
 * The MCP SEP-2848 profile. Both functions ask the kernel, which holds the only copy of the tables.
 * `disposition` is undefined while the call can still move; `envelope` is undefined for a verdict
 * that is neither `needs_approval` nor a denial or rejection.
 */
export const mcpToolApproval = {
  id: ID,
  disposition: (kernel: Kernel, status: CallStatus): Disposition | undefined => kernel.profile(ID, { status }).disposition,
  envelope: (kernel: Kernel, verdict: Verdict): ProfileEnvelope | undefined => kernel.profile(ID, { verdict }).envelope,
} as const
