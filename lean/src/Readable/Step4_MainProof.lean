import Statements
import New.Data.DataExist
import New.Endgame.LongForms
import Readable.Step1_ProductFormulaAndPinch
import Readable.Step3_AnalyticEndgame

/-!
# Step 4: Main Inequality (⋆), GRH, and the Riemann Hypothesis

Top-level assembly of the proof of GRH and RH from Steps 1 and 3 together with the geometric and
arithmetic inputs in `New`:

1. **Theorem C (`theorem_C_integral_forms_long`, Theorem 4.14)**: Pairs `Data.heightLe_volume_rows` and
   `Data.heightLe_volume_ratio_sq` through `twisted_lattice_volume_pinch`.
2. **Main Inequality `(⋆)` (`star_inequality`, Theorem 4.15)**: Pits Theorems A–B against Theorem C
   so `D.mainHeight` cancels identically, leaving `m · rem ≤ (log b)² · budget`.
3. **One-sided prime bound (`eventually_one_sided_prime_bound`, Section 4.5)**: Slides `log x₁` into `[t, t²]`
   via `cauchy_moment_window`, yielding `primeError d N₀ x ≤ x^(-1/2 + 8ε)`.
4. **GRH and RH (`grh_half_plane`, `grh_critical_line`, `rh_critical_line`)**: Induces `χ mod q`
   to `N₀ = 18480 q`, applies `one_sided_zero_free_criterion`, and reflects across `s ↔ 1 - s`.
-/

open DirichletCharacter Real Finset Filter Data Parameters ZMod Module LevelPlaces.LevelForm
open Readable.ProductFormulaAndPinch Readable.AnalyticEndgame

namespace Readable.MainProof

/-- **Theorem C of Paper C (`theorem_C_integral_forms_long`)**. -/
theorem theorem_C_integral_forms_long {P : Parameters} {D : Data P} {n : ℕ} {y : Fin n → D.rows}
    {δ V : ℝ} (hind : LinearIndependent ℂ y) (hbig : (1 - 4 / D.b ^ 2) * D.rowDim ≤ n)
    (hidx : D.IndexLe y δ) (hvol : ∀ σ, covolumeSq (D.Θ 1 ∘ y) σ ≤ Real.exp V) :
    (D.rowDim : ℝ) * (D.mainHeight - 3 * (D.logB * D.budget)) ≤ V + 2 * δ := by
  obtain ⟨θ, hfit⟩ := exists_isFitFamily D
  obtain ⟨_, _, hvol_spec⟩ := D.volume_iota_eq_prod_liftVolume
  have h_upper := D.heightLe_volume_rows hind hbig hidx hvol hfit
  have h_lower : HeightLe (2 * ((D.rowDim : ℝ) * (2 * (D.logB * D.budget) - D.mainHeight)))
      fun ι ↦ D.𝔷 (1 : D.MFoldTwist) ^ 2 / D.𝔷 (θ ι) ^ 2 := by
    simpa [mul_assoc] using D.heightLe_volume_ratio_sq hfit
  have hpinch := twisted_lattice_volume_pinch (hvol_spec 1).1 (fun ι ↦ (hvol_spec (θ ι)).1)
    h_upper h_lower
  have hb_le_L : (D.rowDim : ℝ) * D.b ≤ (D.rowDim : ℝ) * (D.logB * D.budget) := by
    gcongr; exact D.le_of_hasLogBound
  linarith

/-- **Main Inequality `(⋆)` (Theorem 4.15 of Paper C)**: `m · rem ≤ (log b)² · budget`. -/
theorem star_inequality {P : Parameters} {D : Data P} :
    D.m * D.remainder ≤ D.logB ^ 2 * D.budget := by
  obtain ⟨n, y, hind, hbig, ⟨δ, hδ_le, hidx⟩, hshort⟩ := D.exists_family_covolumeSq_le
  have hd_pos : (0 : ℝ) < D.rowDim := by exact_mod_cast D.finrank_rows_ne_zero.pos
  set d : ℝ := (D.rowDim : ℝ); set L : ℝ := D.logB * D.budget
  set h : ℝ := D.mainHeight - D.m * D.remainder + L with def_h
  have hcrude : -h ≤ D.b ^ 2 * D.x ^ 99 := by
    have : 0 < L := HasLogBound.pos D
    have := D.abs_mainHeight_add_remainder_le; have := neg_le_abs D.mainHeight
    have := mul_le_mul_of_nonneg_left (le_abs_self D.remainder) (Nat.cast_nonneg D.m)
    linarith
  have hn_le_d : (n : ℝ) ≤ d :=
    Nat.cast_le.mpr (Fintype.card_fin n ▸ hind.fintype_card_le_finrank : n ≤ D.rowDim)
  have hC := theorem_C_integral_forms_long hind hbig hidx hshort
  have hmiss : (d - n) * (-h) ≤ d * (4 * D.x ^ 99) := by
    have hb_ne : D.b ≠ 0 := (HasLogBound.pos D : (0 : ℝ) < D.b).ne'
    calc (d - n) * (-h) ≤ (d - n) * (D.b ^ 2 * D.x ^ 99) :=
            mul_le_mul_of_nonneg_left hcrude (sub_nonneg.mpr hn_le_d)
      _ ≤ (4 / D.b ^ 2 * d) * (D.b ^ 2 * D.x ^ 99) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = d * (4 * D.x ^ 99) := by field_simp [hb_ne]
  have hboth : d * (D.mainHeight - 3 * L) ≤
      d * (D.mainHeight - D.m * D.remainder + L + 4 * D.x ^ 99 +
        10 * Real.log (1 + D.b ^ 2) * D.budget) := calc
    d * (D.mainHeight - 3 * L) ≤ d * h + (d - n) * (-h) + 2 * δ := by linarith
    _ ≤ d * h + d * (4 * D.x ^ 99) + 2 * (5 * d * Real.log (1 + D.b ^ 2) * D.budget) := by linarith
    _ = _ := by rw [def_h]; ring
  calc D.m * D.remainder
      ≤ 4 * L + 4 * D.x ^ 99 + 10 * Real.log (1 + D.b ^ 2) * D.budget := by
          linarith [le_of_mul_le_mul_left hboth hd_pos]
    _ ≤ D.logB ^ 2 * D.budget := D.le_of_hasLogBound

/-- **One-sided prime bound from `(⋆)` and the Cauchy-moment window (Section 4.5 of Paper C)**. -/
theorem eventually_one_sided_prime_bound (P : Parameters) {ε : ℝ}
    (hε : 0 < ε / 6 ∧ ε < 1 / 100) :
    ∀ᶠ x in atTop, primeError P.d P.N₀ x ≤ x ^ (8 * ε + (2 : ℝ)⁻¹ - 1) := by
  have hwin := (tendsto_log_atTop.const_mul_atTop (r := (1e6 : ℝ)) (by norm_num)).eventually
    (cauchy_moment_window
      (isPolar_primeError PrimeSevenModEight.mod_eight (P.coprime_N₁_d 0).coprime_mul_right)
      (isPolar_primeError PrimeSevenModEight.mod_eight P.d.coprime_one_left))
  filter_upwards [exists_data P hε.1 hε.2, hwin] with x ⟨D, hx_eq, _, hlogx1_ge, hlogB_eq, hthick_ge⟩ hW
  subst hx_eq; simp only [Real.log_exp] at hlogx1_ge hlogB_eq hthick_ge hW
  have := D.hasLogLower_of_le hthick_ge; have hscale := D.scale
  obtain ⟨u, ⟨hu_lo, hu_hi⟩, hu_bound⟩ :=
    hW ((towerDeg D.s : ℝ) / #D.thick) ⟨by positivity, D.le_of_hasLogBound⟩
  let D' : Data P := { D with
    logX₁ := u
    scale := by
      have hu_le : u ≤ D.logX₁ := hu_hi.trans hlogx1_ge
      have hlogX_pos : 0 < D.logX := by linarith [hscale.1, hscale.2.1, (@Data.c_ge P).1]
      exact ⟨hscale.1, hscale.2.1, hu_lo, by linarith [hscale.2.2.2.1],
        by linarith [hscale.2.2.2.2, Real.log_le_log (by linarith : 0 < u) hu_le]⟩ }
  have := D'.hasLogLower_of_le hthick_ge
  have hid : primeError P.d P.N₀ D.x =
      D'.m * D'.remainder / D'.m / D'.a / #D.thick +
      (primeError P.d P.N₀ D'.x₁ - (towerDeg D.s : ℝ) / #D.thick * primeError P.d 1 D'.x₁) := by
    have htops : #D'.tops = towerDeg D.s := by
      simpa [tops] using P.card_placeClass_eq (s := D.s) (P.N₀.dvd_mul_right _)
    rw [D'.remainder_eq, htops]
    field_simp [(HasLogBound.pos D' : (0 : ℝ) < D'.m).ne',
      (HasLogBound.pos D' : (0 : ℝ) < D'.a).ne', (HasLogBound.pos D' : (0 : ℝ) < #D.thick).ne']
    ring
  calc primeError P.d P.N₀ D.x
      ≤ D'.logB ^ 2 * D'.budget / D'.m / D'.a / #D.thick + Real.exp (-(1e6 * D.logX)) := by
        have h1 : D'.m * D'.remainder / D'.m / D'.a / #D.thick ≤
            D'.logB ^ 2 * D'.budget / D'.m / D'.a / #D.thick := by grw [star_inequality]
        have h2 : primeError P.d P.N₀ D'.x₁ - (towerDeg D.s : ℝ) / #D.thick * primeError P.d 1 D'.x₁ ≤
            Real.exp (-(1e6 * D.logX)) := by simpa [Data.x₁, D'] using hu_bound
        linarith
    _ ≤ D.x ^ (8 * ε + (2 : ℝ)⁻¹ - 1) := by
        simpa [Data.x, ← Real.exp_mul] using
          (D'.le_of_hasLogBound (by grind) :
            D'.logB ^ 2 * D'.budget / D'.m / D'.a / #D.thick + Real.exp (-(1e6 * D.logX)) ≤
              Real.exp (D.logX * (8 * ε + (2 : ℝ)⁻¹ - 1)))

private def paramsOfPrimeMod (q : ℕ) [NeZero q] (d : Nat.Primes)
    (hd : (d : ZMod (18480 * q)) = ((9240 * q - 1 : ℕ) : ZMod (18480 * q))) : Parameters :=
  have hq_pos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hsub : ((d.1 + 1 : ℕ) : ZMod (18480 * q)) = (9240 * q : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one, hd, Nat.cast_sub (by omega : 1 ≤ 9240 * q), Nat.cast_one,
      sub_add_cancel]
  have h2d : 18480 * q ∣ 2 * (d.1 + 1) := (ZMod.natCast_eq_zero_iff _ _).mp <| by
    calc ((2 * (d.1 + 1) : ℕ) : ZMod (18480 * q))
        = 2 * ((d.1 + 1 : ℕ) : ZMod (18480 * q)) := by push_cast; ring
      _ = ((18480 * q : ℕ) : ZMod (18480 * q)) := by rw [hsub]; push_cast; ring
      _ = 0 := ZMod.natCast_self _
  have hndvd : ¬ 18480 * q ∣ d.1 + 1 := fun hdvd ↦ by
    have h0 := hsub.symm.trans ((ZMod.natCast_eq_zero_iff _ _).mpr hdvd)
    have := Nat.le_of_dvd (by positivity) ((ZMod.natCast_eq_zero_iff _ _).mp h0); omega
  Parameters.mk (18480 * q) d.1 ⟨q, rfl⟩ d.2 ⟨h2d, hndvd⟩

/-- **Generalized Riemann Hypothesis (Half-Plane Form, Theorem 1.1 of Paper C)**. -/
theorem grh_half_plane : DirichletLNonvanishingRightOfHalf := by
  intro q hq χ ρ hρ hpole hzero
  set ε : ℝ := (min ρ.re 1 - (2 : ℝ)⁻¹) / 51 with hε_def
  have hε_pos : 0 < ε := by
    have : (2 : ℝ)⁻¹ < min ρ.re 1 := lt_min (by linarith) (by norm_num)
    linarith
  have hε_lt : ε < 1 / 100 := by have := min_le_right ρ.re 1; linarith
  have hβ_lt : 8 * ε + (2 : ℝ)⁻¹ < ρ.re := by have := min_le_left ρ.re 1; linarith
  let N₀ : ℕ := 18480 * q
  have hdiv : q ∣ N₀ := dvd_mul_left q 18480
  have : NeZero N₀ := ⟨mul_ne_zero (by norm_num) (NeZero.ne q)⟩
  have hind_zero : entireL (χ.changeLevel hdiv) ρ = 0 := by
    have hL_ind : (χ.changeLevel hdiv).LFunction ρ = 0 := by
      rw [DirichletCharacter.LFunction_changeLevel hdiv χ hpole, hzero, zero_mul]
    rw [entireL]; by_cases h1 : χ.changeLevel hdiv = 1
    · have hρ_ne1 := hpole.resolve_left (not_not.mpr ((DirichletCharacter.changeLevel_eq_one_iff hdiv).mp h1))
      rw [h1] at hL_ind
      simp [h1, hρ_ne1, hL_ind]
    · simp [h1, hL_ind]
  let d₀ : ZMod N₀ := (9240 * q - 1 : ℕ)
  have hd₀_unit : IsUnit d₀ := IsUnit.of_mul_eq_one d₀ <| by
    have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hsq_nat : (9240 * q - 1) * (9240 * q - 1) = (4620 * q - 1) * N₀ + 1 := by
      dsimp only [N₀]; zify [show 1 ≤ 9240 * q by omega, show 1 ≤ 4620 * q by omega]; ring
    simpa [d₀, ZMod.natCast_self] using congrArg (Nat.cast (R := ZMod N₀)) hsq_nat
  have hprimes : ∀ d : Nat.Primes, (d : ZMod N₀) = d₀ →
      (d.1 % 8 = 7 ∧ N₀.Coprime d) ∧
      ∀ᶠ x in atTop, primeError d N₀ x ≤ x ^ ((8 * ε + (2 : ℝ)⁻¹) - 1) := fun d hd ↦ by
    let P := paramsOfPrimeMod q d hd
    exact ⟨⟨P.instHeegD.2, (P.coprime_N₁_d 0).coprime_mul_right⟩,
      eventually_one_sided_prime_bound P ⟨by linarith, hε_lt⟩⟩
  exact one_sided_zero_free_criterion (by linarith) hd₀_unit hprimes ρ hβ_lt
    (χ.changeLevel hdiv) hind_zero

/-- **Generalized Riemann Hypothesis (Critical-Line Form)**. -/
theorem grh_critical_line : DirichletLZerosOnLine := by
  intro N hN χ s hs0 hs1 hL0
  have hs_ne1 : s ≠ 1 := ne_of_apply_ne Complex.re (by simp; linarith)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1s_gt : (1 : ℝ) / 2 < (1 - s).re := by simp; linarith
    have h1s_ne1 : 1 - s ≠ 1 := fun h1 ↦ (ne_of_apply_ne Complex.re (by simp; linarith)) (sub_eq_self.mp h1)
    have hγ_ne : χ.gammaFactor s ≠ 0 := by
      rw [DirichletCharacter.gammaFactor]; split_ifs
      · exact Complex.Gammaℝ_ne_zero_of_re_pos hs0
      · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    exact grh_half_plane N (χ⁻¹) (1 - s) h1s_gt (Or.inr h1s_ne1)
      ((LFunction_one_sub_eq_zero χ s hs0.ne' hs_ne1 hL0).resolve_left hγ_ne)
  · exact grh_half_plane N χ s hgt (Or.inr hs_ne1) hL0

/-- **The Classical Riemann Hypothesis**. -/
theorem rh_critical_line : RiemannZetaZerosOnLine := by
  intro s hζ htriv hs1
  have hζ_ne_right : ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → riemannZeta z ≠ 0 := fun z hz hz1 ↦ by
    simpa [DirichletCharacter.LFunction_modOne_eq] using grh_half_plane 1 1 z hz (Or.inr hz1)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1s_gt : (1 : ℝ) / 2 < (1 - s).re := by simp; linarith
    have hs_ne0 : s ≠ 0 := fun h0 ↦ by rw [h0, riemannZeta_zero] at hζ; norm_num at hζ
    have hΓ_ne : Complex.Gammaℝ s ≠ 0 := by
      rw [Ne, Complex.Gammaℝ_eq_zero_iff]; rintro ⟨n, hn⟩
      cases n with
      | zero => exact hs_ne0 (by simpa using hn)
      | succ m => exact htriv ⟨m, by push_cast at hn ⊢; linear_combination hn⟩
    have hξ0 : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs_ne0] at hζ
      exact (div_eq_zero_iff.mp hζ).resolve_right hΓ_ne
    have hζ1s : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr hs1.symm), completedRiemannZeta_one_sub,
        hξ0, zero_div]
    exact hζ_ne_right (1 - s) h1s_gt (fun h1 ↦ hs_ne0 (sub_eq_self.mp h1)) hζ1s
  · exact hζ_ne_right s hgt hs1 hζ

end Readable.MainProof
