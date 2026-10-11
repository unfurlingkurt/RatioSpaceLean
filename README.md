# RatioSpace Elements I and II v0.25: Lean release

## What this repository is

This is the public Lean 4 formalization accompanying *RatioSpace Elements I*
and *RatioSpace Elements II*, version 0.25. It contains the declarations
reachable from the source root at the commit recorded in `SOURCE_COMMIT`, apart
from the two non-shipping census modules identified by the release specification.
The source declarations have been moved into book-and-section directories without
changing their names, statements, definitions, or axiom sets.

## Build

With Lean available through `elan`, fetch the pinned Mathlib cache and build:

```sh
lake exe cache get
lake build
```

A clean build of the 1,609 jobs of this repository (no `.lake/build` directory
present, Mathlib and its dependencies prebuilt from the pinned cache and not
rebuilt) was measured at 2 minutes 3 seconds (123.4 s wall clock) on Linux with an
AMD Ryzen 9 7950X (16 cores, 32 threads) and 61 GB RAM. That build emits no
warnings.

## Reading the crosswalk

`CROSSWALK.md` is generated from `crosswalk/elements-i.tsv` and
`crosswalk/elements-ii.tsv`. Each row pairs one numbered book item with a
verbatim opening statement, its mode of establishment, the fully qualified Lean
declarations that realize it, the applicable correction-ledger identifiers, and
any gap still open at the recorded source commit. Cross-book imports and shared
constraints are documented in `crosswalk/placement-exceptions.tsv`.

## Axiom policy

The release permits only `propext`, `Quot.sound`, and `Classical.choice` where
`reports/axioms.tsv` lists it. Nothing else is admitted. In particular, the
release has no `sorry`, declared `axiom`, `Lean.ofReduceBool`, or dependency whose
name contains `native_decide`.

## License

The Lean source and release metadata are licensed under the Apache License 2.0.
See `LICENSE`.

## Citation

Please cite the RatioSpace Elements Lean release as:

Russell, Kurt Michael. 2026. *RatioSpace Elements Lean release*, version 0.25. Zenodo. [https://doi.org/10.5281/zenodo.23287489](https://doi.org/10.5281/zenodo.23287489).
