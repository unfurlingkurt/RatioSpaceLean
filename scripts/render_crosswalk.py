#!/usr/bin/env python3
"""Render the public Markdown crosswalk from its two authoritative TSV files."""

from __future__ import annotations

import csv
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SOURCE_COMMIT = (ROOT / "SOURCE_COMMIT").read_text(encoding="utf-8").strip()


def cell(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def render_book(title: str, path: Path) -> list[str]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))

    result = [
        f"## {title}",
        "",
        "| Item | Section | Statement | Establishment | Lean declarations | Ledger | Open gaps |",
        "|---|---:|---|---|---|---|---|",
    ]
    for row in rows:
        result.append(
            "| "
            + " | ".join(
                cell(row[key])
                for key in (
                    "item",
                    "section",
                    "statement",
                    "establishment",
                    "declarations",
                    "ledger",
                    "gaps",
                )
            )
            + " |"
        )
    result.append("")
    return result


def main() -> None:
    lines = [
        "# RatioSpace Elements I and II v0.25: Lean crosswalk",
        "",
        (
            "This document is generated from `crosswalk/elements-i.tsv` and "
            "`crosswalk/elements-ii.tsv`; edit those TSV files and re-run "
            "`python3 scripts/render_crosswalk.py`."
        ),
        "",
        f"Source commit: `{SOURCE_COMMIT}`.",
        "",
        (
            "`proved` marks a theorem established over its stated domain; `instances` "
            "marks an exact finite instance result; `defined` marks a realized definition; "
            "`imported` marks a result the book imports from earlier mathematics and cites; "
            "its listed declarations realize its statement, hypotheses or definitions in the library; "
            "`constraint` marks a library-wide rule; and `outside-scope` records an item "
            "that has no Lean declaration, with the reason."
        ),
        "",
    ]
    lines.extend(render_book("Elements I", ROOT / "crosswalk" / "elements-i.tsv"))
    lines.extend(render_book("Elements II", ROOT / "crosswalk" / "elements-ii.tsv"))
    (ROOT / "CROSSWALK.md").write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()
