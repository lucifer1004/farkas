"""Shared source transform for compiling Lean files outside their package.

`module`-marked files cannot import the (non-module) farkas package, so the
transform demotes the file to a plain one: the `module` keyword (wherever it
sits after the copyright header) is replaced with a comment, and
module-system markers revert to their plain forms (`public import` ->
`import`, `public section` / `@[expose] public section` -> `section`,
`meta def` -> `def`). Whether or not an import is injected, exactly one line
is inserted at the same slot so diagnostics stay line-number-comparable
between transformed variants.
"""

import re


def wrap_source(text: str, inject: str | None) -> str:
    """Transform Lean source; `inject` is an import line or None (placeholder)."""
    lines = []
    demoted = False
    for l in text.splitlines():
        if not demoted and l.strip() == "module":
            lines.append("-- (farkas wrap: was `module`)")
            demoted = True
            continue
        l = re.sub(r"^public import\b", "import", l)
        l = re.sub(r"^(@\[expose\] )?public section\b", "section", l)
        l = re.sub(r"^(\s*)meta def\b", r"\1def", l)
        lines.append(l)
    last_import = max(
        (i for i, l in enumerate(lines) if l.startswith("import ")), default=-1
    )
    lines.insert(last_import + 1, inject or "-- (farkas wrap: import slot)")
    return "\n".join(lines) + "\n"
