from __future__ import annotations


class WritInputError(ValueError):
    """A value the caller passed is not one the kernel or a digest accepts.

    `path` names the offending argument or JSON value, `items[3].name` style; it is "" when
    the whole input is at fault.
    """

    def __init__(self, message: str, path: str = "") -> None:
        # A path can hold a lone surrogate (the offending key itself), which str(e) must not carry.
        shown = path.encode("utf-8", "backslashreplace").decode("utf-8")
        super().__init__(message if path == "" else f"{shown}: {message}")
        self.path = path


class WritKernelError(RuntimeError):
    """The kernel failed, or was aborted by an earlier trap and must be replaced."""


class WritConflictError(Exception):
    """A commit kept losing to other writers, so the step was given up without an effect."""


class WritStoreError(Exception):
    """A store refused a record it cannot hold, or found one it cannot read.

    The gate never raises it; a custom store raises it for its own failures, and the gate passes it on.
    """


class WritStateFullError(Exception):
    """A session's stored state has no room for the step: end the session and start a new one."""

    def __init__(self, message: str, session_id: str, bytes: int, limit: int) -> None:
        super().__init__(message)
        self.session_id = session_id
        #: UTF-8 bytes of the state that did not fit.
        self.bytes = bytes
        #: The byte limit it is over.
        self.limit = limit


class WritPolicyChangedError(Exception):
    """A stored session was started under a policy this gate does not run, or runs only to settle and end."""

    def __init__(self, message: str, session_id: str, policy_digest: str) -> None:
        super().__init__(message)
        self.session_id = session_id
        #: The digest of the policy the session was started under.
        self.policy_digest = policy_digest
