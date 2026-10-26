from __future__ import annotations

from typing import Final

from .kernel import Kernel
from .types import CallStatus, JsonObject, Verdict


class _McpToolApproval:
    """The MCP SEP-2848 profile. Both functions ask the kernel, which holds the only copy of the tables.

    `disposition` is None while the call can still move; `envelope` is None for a verdict that is
    neither `needs_approval` nor a denial or rejection.
    """

    id: Final = "mcp-tool-approval"

    def disposition(self, kernel: Kernel, status: CallStatus) -> str | None:
        return kernel.profile(self.id, {"status": status}).disposition

    def envelope(self, kernel: Kernel, verdict: Verdict) -> JsonObject | None:
        return kernel.profile(self.id, {"verdict": verdict}).envelope

    def __repr__(self) -> str:
        return "writ.mcp_tool_approval"


mcp_tool_approval: Final = _McpToolApproval()
