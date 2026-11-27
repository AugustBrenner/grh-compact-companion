# The Riemann Hypothesis via Multiplicity Chains

**An Expository Companion and Modular Lean 4 Walkthrough for the Alpöge–Claude `grh-compact` Proof**

[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](./LICENSE)
<!-- Replace with the Zenodo DOI badge after enabling the GitHub–Zenodo webhook and publishing v1.0.0 -->
<!-- [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX) -->

- **Read the paper:** [`paper_c.pdf`](./paper_c.pdf) (LaTeX source: [`paper_c.tex`](./paper_c.tex))
- **Modular Lean 4 walkthrough spine:** [`lean/src/Readable/`](./lean/src/Readable/) (5 files, 15 public theorems, `1,271` LOC)
- **Full compiled formalization:** [`lean/`](./lean/) (unmodified `grh-compact` + `Readable`, 799 `.lean` files, `114,098` LOC, Lean `v4.35.0`)
- **Executable sanity checks:** [`verify_paper_c.py`](./verify_paper_c.py)

---

## Attribution & Scope

The proof of the Generalized Riemann Hypothesis (GRH) for Dirichlet $L$-functions—and hence the classical Riemann Hypothesis (RH)—is due to **Levent Alpöge (with Claude)** ([`alpo.ge/remark.pdf`](https://alpo.ge/remark.pdf), linking to `alpo.ge/lean.tar.gz.part01`–`14`). Separately, Anthropic released a shorter rewriting in [`lsernau/grh-lean`](https://github.com/lsernau/grh-lean) (commit `72fead1`, Copyright 2026 Anthropic, PBC, Apache 2.0), containing `grh/` (readable edition) and `grh-compact/` (compact edition).

Inside [`lean/`](./lean/), all 794 upstream source files in `src/Lib/` (`77,850` LOC), `src/New/` (`34,948` LOC), `src/Main.lean` (`13` LOC), `src/Statements.lean` (`16` LOC; `29`-line trust surface), and `lake-manifest.json` are packaged **byte-for-byte unmodified** from `lsernau/grh-lean` (`grh-compact/`, commit `72fead1`).

This repository adds:
1. **`paper_c.pdf` / `paper_c.tex`**: An expository companion translating the global architecture of `grh-compact` from Stepanov's 1969 polynomial method over $\mathbb{F}_p$ to $\mathbb{Z}$, highlighting four core mechanisms of `grh-compact` (Cauchy-moment window eliminating Siegel–Walfisz from the analytic endgame, rank-2 Siegel-discriminant global sieve, full-chain generating-function Hecke inversion, and Higman's operator in Ribet's method). Every theorem carries an explicit status line distinguishing complete prose proofs from sketches and Lean-backed summaries.
2. **`lean/src/Readable/`**: A 5-file modular Lean 4 walkthrough spine (`Step0`–`Step4`, 15 designated `theorem` declarations + 18 public helper lemmas) compiled alongside unmodified `grh-compact` via `lakefile.toml`, with all 5 root theorems and 15 walkthrough theorems audited via [`lean/scripts/PrintAxioms.lean`](./lean/scripts/PrintAxioms.lean) (output recorded in [`lean/verification_axioms.log`](./lean/verification_axioms.log)) to depend only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
3. **`verify_paper_c.py` & `build.sh`**: Exact rational/finite numerical checks for the elementary identities, constructive Stepanov polynomial over $\mathbb{F}_{101}$, Behrend sphere triples, weaker sufficient-scale spot checks and regression tests, and strict zero-warning/zero-box LaTeX verification (`build.sh` runs Python and LaTeX only; Lean verification is run separately below).

### What Is Proved in Full vs. Sketched vs. Summarized

| Paper Sections | Status in `paper_c.pdf` | Machine-Checked Lean Backing |
|---|---|---|
| **§§2–5** (Stepanov prototype, Landau lemma, Cauchy-moment window, one-sided criterion, volume pinch, Behrend sphere, prime-sum cancellation, assembly of $(\star)$ and GRH, exact CM prime-sum identity) | **Proved in full in prose**; outlines/sketches for Pólya–Vinogradov twist (Prop. 3.4), admissible-data existence (Prop. 4.9), CM normal form (Prop. 5.2), and theta-jet divisibility (Thm. 5.4(1),(3)) | `lean/src/Readable/Step0`–`Step4` + unmodified `lean/src/New/` & `src/Lib/` |
| **§§6–8** (Theorems A, B, and C: seesaw, elementary divisors, Siegel's lemma, Ribet/Kisin modules) | **Architectural summary** with exact constants/hypotheses of `grh-compact` (plus complete prose proofs of Prop. 6.2(2), Lem. 7.1, and top-level assemblies of Thms. A & C from their sub-propositions) | Unmodified `lean/src/New/` + `lean/src/Lib/` |
| **§9** (Lean verification & axiom audit) | Exact build and `#print axioms` record | `lean/src/Statements.lean` + `lean/src/Main.lean` (29-line trust surface) |

**AI-assistance disclosure:** This expository companion, `lean/src/Readable/`, and `verify_paper_c.py` were prepared with AI-assisted drafting and cross-checking and verified directly against the Lean `v4.35.0` kernel and executable checks. The author takes full responsibility for the manuscript. Note that while `grh-compact` passes Lean's kernel checks using only the three standard axioms, the full 799-file Lean artifact has not yet undergone complete human line-by-line refereeing.

---

## Proof Spine (`lean/src/Readable/`)

| File | Paper Section | Key Audited Theorems |
|---|---|---|
| [`Step0_StepanovWarmup.lean`](./lean/src/Readable/Step0_StepanovWarmup.lean) *(Mathlib-only)* | §2 (Theorem 2.1) | `stepanov_S_plus_bound`, `stepanov_warmup` |
| [`Step1_ProductFormulaAndPinch.lean`](./lean/src/Readable/Step1_ProductFormulaAndPinch.lean) | §4 & §7 (Lem. 4.4, Thm. 4.5, Lem. 7.1) | `rational_product_formula_log`, `product_formula_for_heights`, `greedy_covering_from_spread`, `twisted_lattice_volume_pinch` |
| [`Step2_BehrendSphere.lean`](./lean/src/Readable/Step2_BehrendSphere.lean) *(Mathlib-only)* | §4 (Prop. 4.7) | `behrend_three_term_free` |
| [`Step3_AnalyticEndgame.lean`](./lean/src/Readable/Step3_AnalyticEndgame.lean) | §3 (Thms. 3.5–3.6) | `cauchy_moment_window`, `one_sided_zero_free_criterion` |
| [`Step4_MainProof.lean`](./lean/src/Readable/Step4_MainProof.lean) | §§4, 8 (Thms. 1.1, 4.14–4.15) | `theorem_C_integral_forms_long`, `star_inequality`, `eventually_one_sided_prime_bound`, `grh_half_plane`, `grh_critical_line`, `rh_critical_line` |

See [`lean/README_READABLE.md`](./lean/README_READABLE.md) and [`lean/GUIDE.md`](./lean/GUIDE.md) for the full reading order.

---

## Quick Verification

### 1. Run numerical checks & rebuild the PDF (~10 seconds)
Requires Python 3 and TeX Live (`pdflatex`, `pdftotext`):
```bash
python3 -I verify_paper_c.py
./build.sh
```
`build.sh` verifies that `verify_paper_c.py` passes, `paper_c.tex` converges with zero LaTeX errors/warnings, and zero overfull or underfull hboxes/vboxes occur.

### 2. Verify the Lean 4 formalization & axioms
Requires [Elan](https://github.com/leanprover/elan) (Lean toolchain pinned to `v4.35.0` in [`lean/lean-toolchain`](./lean/lean-toolchain); Mathlib pinned in [`lean/lake-manifest.json`](./lean/lake-manifest.json); allow ~24 GB RAM and 1–2 hours on 12 cores for a full build):
```bash
cd lean
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
for f in src/Readable/Step*.lean; do lake env lean "$f"; done
```
Every theorem in `src/Main.lean` (5 root theorems) and `src/Readable/` (15 walkthrough theorems) depends only on `[propext, Classical.choice, Quot.sound]`. All 799 source files under `lean/src/` contain zero `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or `implemented_by` tokens (the separate, unimported upstream file [`lean/Challenge.lean`](./lean/Challenge.lean) contains five intentional `sorry` stubs used by `Comparator` verification, matching the disclosure in §9.2 of `paper_c.pdf`).

To audit soundness without reading 114k lines of proof tactics, inspect the **29-line trust surface**: [`lean/src/Statements.lean`](./lean/src/Statements.lean) and [`lean/src/Main.lean`](./lean/src/Main.lean), verify byte-for-byte parity with `lsernau/grh-lean@72fead1`, and run the build and `PrintAxioms.lean`.

---

## Errata & Mathematical Feedback

Mathematical corrections, notation improvements, Lean-alignment catches, and readability suggestions are warmly welcome:
- Open an issue using the **[Mathematical / Lean Errata](https://github.com/AugustBrenner/grh-compact-companion/issues/new?template=errata.md)** or **[Readability / Exposition Feedback](https://github.com/AugustBrenner/grh-compact-companion/issues/new?template=readability.md)** template.
- Please include section/page numbers (or Lean `file:line` references) so issues can be audited and fixed cleanly in tagged Zenodo revisions.

---

## License & Upstream Attribution

This repository is licensed under the **Apache License, Version 2.0** (see [`LICENSE`](./LICENSE) and [`NOTICE`](./NOTICE)).
Upstream `grh-compact` files in `lean/` preserve Anthropic, PBC's Apache 2.0 [`LICENSE`](./lean/LICENSE), [`NOTICE`](./lean/NOTICE), and Mathlib [`ATTRIBUTION.md`](./lean/ATTRIBUTION.md).
