#!/usr/bin/env python3
"""Reject obvious trust-boundary escapes in project Lean sources."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "OutcastsMathLab"

RULES = {
    "unfinished proof": re.compile(r"\b(sorry|admit)\b"),
    "new trusted declaration": re.compile(r"^\s*(axiom|constant)\b", re.MULTILINE),
    "unsafe declaration": re.compile(r"^\s*unsafe\b", re.MULTILINE),
}


def strip_comments_and_strings(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    text = re.sub(r"--.*?$", "", text, flags=re.MULTILINE)
    text = re.sub(r'"(?:\\.|[^"\\])*"', '""', text)
    return text


def main() -> int:
    failures: list[str] = []
    files = sorted(SOURCE_ROOT.rglob("*.lean"))
    if not files:
        print("policy: no Lean source files found", file=sys.stderr)
        return 2

    for path in files:
        clean = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for label, pattern in RULES.items():
            if pattern.search(clean):
                failures.append(f"{path.relative_to(ROOT)}: {label}")

    if failures:
        print("policy check failed:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1

    print(f"policy: checked {len(files)} Lean files; no blocked construct found")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
