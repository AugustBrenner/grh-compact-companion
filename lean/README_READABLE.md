# Reading Guide: Modular Lean 4 Proof of RH & GRH

This Lean 4.35 formalization packages the **byte-for-byte unmodified** upstream `grh-compact` formalization (`lsernau/grh-lean`, commit `72fead1`, Apache 2.0, implementing Levent Alpöge and Claude's proof of GRH) alongside an original five-file modular walkthrough spine in `src/Readable/` aligned section-by-section with `../paper_c.tex`.

## Proof Spine

1. **`src/Readable/Step0_StepanovWarmup.lean`** *(Mathlib-only)*
   - Proves **Theorem 2.1** (`stepanov_warmup`, `stepanov_S_plus_bound`): Stepanov's 1969 bound `|N_E - (p + 1)| ≤ 2p/m + 3m + 4` for elliptic curves `y² = f(x)` over `𝔽_p`, via polynomial derivatives, Fermat's Little Theorem, rank–nullity, and degree-quotient parity.
2. **`src/Readable/Step1_ProductFormulaAndPinch.lean`**
   - Proves the **Rational Product Formula** (`rational_product_formula_log`), **Lemma 4.4** (`product_formula_for_heights`: `HeightLe c 1 → 0 ≤ c`), **Lemma 7.1** (`greedy_covering_from_spread`), and **Theorem 4.5(2)** (`twisted_lattice_volume_pinch`).
3. **`src/Readable/Step2_BehrendSphere.lean`** *(Mathlib-only)*
   - Proves **Proposition 4.7** (`behrend_three_term_free`): Behrend's 1946 sphere construction eliminating nontrivial weighted three-term ratios via the weighted parallelogram identity.
4. **`src/Readable/Step3_AnalyticEndgame.lean`**
   - Proves **Theorem 3.6** (`cauchy_moment_window`, eliminating Siegel–Walfisz from the endgame) and **Theorem 3.5** (`one_sided_zero_free_criterion`, combining Landau's 1905 lemma and Pólya–Vinogradov zero avoidance).
5. **`src/Readable/Step4_MainProof.lean`** & **`src/Main.lean`**
   - Assembles **Theorem C** (`theorem_C_integral_forms_long`, **Theorem 4.14**), the **Main Inequality `(⋆)`** (`star_inequality`, **Theorem 4.15**), the one-sided prime bound (`eventually_one_sided_prime_bound`, **Section 4.5**), **GRH** (`grh_half_plane`, `grh_critical_line`, **Theorem 1.1**), and the classical **Riemann Hypothesis** (`rh_critical_line`).

## Verification Commands

```bash
export ELAN_HOME="$PWD/.elan" XDG_CACHE_HOME="$PWD/.cache" PATH="$PWD/.elan/bin:$PATH"
lake build
lake env lean scripts/PrintAxioms.lean
for f in src/Readable/Step*.lean; do lake env lean "$f"; done
```

Every theorem in `src/Main.lean` (5 root theorems) and `src/Readable/` (15 walkthrough theorems) compiles with zero errors, zero `sorry`, and depends strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); the five files in `src/Readable/` compile with zero warnings.
