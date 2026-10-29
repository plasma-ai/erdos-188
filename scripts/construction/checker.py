"""Named pass/fail checks with a printed transcript and exit protocol."""

from __future__ import annotations

__all__ = ['Checker']


class Checker:
    """Record named checks, print one line per check and a final verdict."""

    def __init__(self: Checker) -> None:
        # initialize check state
        self._count = 0
        self._failures: list[str] = []

    @property
    def failures(self: Checker) -> list[str]:
        """Return failed check names in check order."""
        return list(self._failures)

    @property
    def passed(self: Checker) -> bool:
        """Return whether at least one check ran and every check passed."""
        return (self._count > 0) and not self._failures

    def check(self: Checker, name: str, ok: bool, detail: str = '') -> bool:
        """Record one named check and return ``ok`` unchanged."""
        # record the outcome
        self._count += 1
        if not ok:
            self._failures.append(name)
        # print the transcript line with detail only for failures
        tag = 'ok' if ok else 'FAIL'
        suffix = f' -- {detail}' if detail and not ok else ''
        print(f'  [{tag}] {name}{suffix}')
        return ok

    def summary(self: Checker) -> str:
        """Return the one-line verdict over every recorded check."""
        # reject an empty run
        if self._count == 0:
            return 'NO CHECKS RUN (0 checks)'
        # render the passing or failing verdict
        suffix = 's' if self._count != 1 else ''
        if self.passed:
            return f'ALL CHECKS PASS ({self._count} check{suffix})'
        names = ', '.join(self._failures)
        return (
            f'FAILURES ({len(self._failures)} of {self._count} check{suffix}): {names}'
        )

    def finish(self: Checker) -> int:
        """Print the summary and return zero on pass, one on failure."""
        print(self.summary())
        return 0 if self.passed else 1
