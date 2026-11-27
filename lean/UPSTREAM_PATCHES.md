# Upstream Compatibility Patch Manifest (`lsernau/grh-lean` commit `72fead1`)

This directory packages the upstream `grh-compact` formalization from [`lsernau/grh-lean`](https://github.com/lsernau/grh-lean) at commit `72fead1` (Copyright 2026 Anthropic, PBC, Apache 2.0) alongside our five-file pedagogical walkthrough spine (`src/Readable/`).

To compile cleanly under the pinned Lean `v4.35.0` toolchain and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, **13 files in `src/New/`** carry minimal tactic-compatibility patches relative to commit `72fead1`, plus two project-harness edits (`lakefile.toml` and `scripts/PrintAxioms.lean`).

- **Zero edits** to `src/Statements.lean`, `src/Main.lean`, or `src/Lib/`.
- **Zero edits** to any theorem or definition statement anywhere in `src/New/`.
- **Zero custom axioms, `sorry`, `admit`, `unsafe`, `native_decide`, or `implemented_by`** introduced; all 20 audited theorems depend strictly on `[propext, Classical.choice, Quot.sound]` (see [`verification_axioms.log`](./verification_axioms.log)).

## 1. Tactic-Compatibility Patches in `src/New/` (13 files)

| # | File | Line(s) | Exact Change vs. `72fead1` | Reason |
|---|---|---:|---|---|
| 1 | `src/New/Columns/LocalStatement.lean` | 225, 239 | `ring` → `ring_nf`; `field` → `field_simp` | Lean `v4.35.0` / Mathlib tactic behavior on non-closing intermediate goals |
| 2 | `src/New/Data/DataExist.lean` | 88, 106 | `ring` → `ring_nf`; `field` → `field_simp` | Non-closing intermediate ring/field normalization |
| 3 | `src/New/Endgame/ShortAndEnough.lean` | 152 | `ring` → `ring_nf` | Non-closing intermediate ring normalization |
| 4 | `src/New/Exchange/CrudeRows.lean` | 103–104 | `... <;> grind` → newline `all_goals grind` | Split combinator for multi-goal `grind` dispatch |
| 5 | `src/New/Exchange/GridFirstColumns.lean` | 90 | `ring` → `ring_nf` | Non-closing intermediate ring normalization |
| 6 | `src/New/Filling/FiniteSystem.lean` | 86, 290 | `coe_finsetSum` → `ofNNReal_finsetSum`; `ring` → `ring_nf` | Mathlib lemma rename + intermediate ring normalization |
| 7 | `src/New/Filling/Moments.lean` | 230, 252, 272 | `sum_nonneg'` → `Finset.sum_nonneg` | Mathlib lemma rename |
| 8 | `src/New/Heights/OneDeterminant.lean` | 50 | `sum_nonneg'` → `Finset.sum_nonneg` | Mathlib lemma rename |
| 9 | `src/New/Patching/OnePrime.lean` | 113 | `ring` → `ring_nf` inside `simpa (disch := ...)` | Non-closing ring normalization inside discharger |
| 10 | `src/New/Rows/ComparisonForms.lean` | 157 | Split `simp [*, twist_one_spec] <;> lia` into `(simp [*, twist_one_spec]; done) \| (simp [*]; lia)` | Explicit branch handling when `simp` closes goals before `lia` |
| 11 | `src/New/Seesaw/SeesawTheorem.lean` | 120 | Dropped redundant `NeZero.one_le` from `simp` list | Avoid `simp` loop/redundancy before `omega` |
| 12 | `src/New/Selmer/FitTwistsExist.lean` | 47 | `prod_le_prod'` → `prod_le_prod` | Mathlib lemma rename |
| 13 | `src/New/Selmer/ReciprocityLaw.lean` | 152 | `prod_le_prod'` → `prod_le_prod` | Mathlib lemma rename |

## 2. Project Harness Additions (2 files + `src/Readable/`)

| File | Change vs. `72fead1` | Purpose |
|---|---|---|
| `lakefile.toml` | Added `Readable` library target (`globs = ["Readable.+"]`) to `defaultTargets` | Compiles the 5-file walkthrough spine during `lake build` |
| `scripts/PrintAxioms.lean` | Imported `Readable.Step0`–`Step4` and appended `#print axioms` for all 15 public walkthrough theorems | Audits both the 5 upstream root theorems and all 15 walkthrough theorems together |
| `src/Readable/Step0`–`Step4.lean` | New files (`1,271` LOC total; 15 `theorem` + 18 public helper `lemma` declarations) | Paper C section-by-section pedagogical Lean 4 walkthrough |
