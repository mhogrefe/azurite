#!/usr/bin/env python3
"""Check (and with --fix, insert) the Azurite license header in every tracked source file.

The header mirrors the one used in Malachite, adapted to the Apache License 2.0:

    Copyright © <year> Mikhail Hogrefe

    This file is part of Azurite.

    Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
    License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.

It is written as a `/- ... -/` block comment in Lean files, as `//` line comments in Rust and C
files, and as `#` line comments (after the shebang line, if any) in shell scripts.  The header must
be the first thing in the file and must be followed by a blank line.

Usage:
    scripts/check_headers.py          # report files without a header; exit 1 if any
    scripts/check_headers.py --fix    # insert the header (with the current year) where missing

Run from anywhere inside the repository; the set of files is `git ls-files` restricted to the
source extensions above.
"""

import datetime
import re
import subprocess
import sys

TEXT = [
    "Copyright © {year} Mikhail Hogrefe",
    "",
    "This file is part of Azurite.",
    "",
    "Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache",
    "License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.",
]

EXTENSIONS = (".lean", ".rs", ".c", ".h", ".sh")


def header_lines(path: str, year: str) -> list[str]:
    """The header for `path`, as a list of lines (without newlines)."""
    text = [line.format(year=year) for line in TEXT]
    if path.endswith(".lean"):
        return ["/-", *text, "-/"]
    if path.endswith((".rs", ".c", ".h")):
        return [("// " + line).rstrip() for line in text]
    if path.endswith(".sh"):
        return [("# " + line).rstrip() for line in text]
    raise ValueError(path)


def has_header(lines: list[str], path: str) -> bool:
    """Whether `lines` (the file's lines) start with a valid header and a blank line."""
    start = 1 if lines and lines[0].startswith("#!") else 0
    expected = header_lines(path, "0000")
    body = lines[start : start + len(expected)]
    if len(body) != len(expected):
        return False
    for got, want in zip(body, expected):
        pattern = "^" + re.escape(want).replace("0000", r"\d{4}") + "$"
        if not re.match(pattern, got):
            return False
    rest = lines[start + len(expected) :]
    return bool(rest) and rest[0] == ""


def insert_header(lines: list[str], path: str, year: str) -> list[str]:
    start = 1 if lines and lines[0].startswith("#!") else 0
    return lines[:start] + header_lines(path, year) + [""] + lines[start:]


def main() -> int:
    fix = "--fix" in sys.argv[1:]
    root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True
    ).stdout.strip()
    files = subprocess.run(
        ["git", "-C", root, "ls-files", "-z", "--", *(f"*{ext}" for ext in EXTENSIONS)],
        capture_output=True, text=True, check=True,
    ).stdout.split("\0")
    files = [f for f in files if f]
    year = str(datetime.date.today().year)
    missing = []
    for rel in files:
        path = f"{root}/{rel}"
        with open(path, encoding="utf-8") as fh:
            content = fh.read()
        lines = content.split("\n")
        if has_header(lines, rel):
            continue
        missing.append(rel)
        if fix:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("\n".join(insert_header(lines, rel, year)))
    if not missing:
        print(f"License headers present in all {len(files)} source files.")
        return 0
    verb = "Added license header to" if fix else "Missing license header in"
    print(f"{verb} {len(missing)} file(s):")
    for rel in missing:
        print(f"  {rel}")
    return 0 if fix else 1


if __name__ == "__main__":
    sys.exit(main())
