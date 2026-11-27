import New.Endgame.OneSidedCriterion

/-!
# Step 3: Analytic Endgame — Cauchy-Moment Window and One-Sided Zero-Free Criterion

Proofs of the two analytic theorems of **Section 3 of Paper C**:

1. **Cauchy-moment window (`cauchy_moment_window`, Theorem 3.6)**: For polar functions `E, E'`,
   all large `t`, and every `X ∈ [0, e^t]`, some `u ∈ [t, t²]` satisfies `E(u) - X E'(u) ≤ e^(-t)`.
2. **One-sided zero-free criterion (`one_sided_zero_free_criterion`, Theorem 3.5)**: For `β > 1/2`,
   if every prime `d ≡ a (mod M)` (`a ∈ (ℤ/Mℤ)×`, `d ≡ 7 mod 8`, `gcd(M, d) = 1`) satisfies
   `primeError d M x ≤ x^(β - 1)` eventually, then `entireL χ ρ ≠ 0` whenever `Re ρ > β`.
-/

open Complex Filter Nat Real Set MeasureTheory Topology

namespace Readable.AnalyticEndgame

private lemma cauchy_integrand_nonneg {E E' : ℝ → ℝ} {R t X : ℝ} (k : ℕ)
    (hR3 : 3 < R) (hR4 : R < 4) (ht9 : 9 ≤ t) (hX0 : 0 ≤ X)
    (hgrowth : t + t * X + 1 ≤ (2 * t).exp)
    (hE : ∀ v ≥ 0, |E v| ≤ t * v.exp) (hE' : ∀ v ≥ 0, |E' v| ≤ t * v.exp)
    (hno : ∀ u ∈ Icc t (t ^ 2), (-t).exp < E u - X * E' u) :
    ∀ v ∈ Ioi (0 : ℝ), 0 ≤ v ^ k * ((-R * v).exp * (7 * t).exp +
      (-(1 : ℝ) * v).exp * (2 * t - t ^ 2).exp + (-3 * v).exp * (E v - X * E' v - (-t).exp)) := by
  intro v hv; have hv_pos : 0 < v := hv
  refine mul_nonneg (by positivity) ?_
  by_cases hwin : v ∈ Icc t (t ^ 2)
  · have : 0 ≤ E v - X * E' v - (-t).exp := by linarith [hno v hwin]
    positivity
  · have hE_lo : -(t * v.exp) ≤ E v := (abs_le.mp (hE v hv_pos.le)).1
    have hE'_hi : E' v ≤ t * v.exp := (abs_le.mp (hE' v hv_pos.le)).2
    have hneg_t : (-t).exp ≤ v.exp := Real.exp_le_exp.mpr (by linarith)
    have hstep : -((2 * t).exp * v.exp) ≤ E v - X * E' v - (-t).exp := by nlinarith [Real.exp_pos v]
    have hlower : -((-2 * v + 2 * t).exp) ≤ (-3 * v).exp * (E v - X * E' v - (-t).exp) := by
      have hexp : (-3 * v).exp * ((2 * t).exp * v.exp) = (-2 * v + 2 * t).exp := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have := mul_le_mul_of_nonneg_left hstep (Real.exp_nonneg (-3 * v)); linarith
    simp only [Icc, mem_ofPred_eq, not_and_or, not_le] at hwin
    rcases hwin with hlt_t | hgt_t2
    · have hdom : (-2 * v + 2 * t).exp ≤ (-R * v).exp * (7 * t).exp := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
      have : 0 ≤ (-(1 : ℝ) * v).exp * (2 * t - t ^ 2).exp := by positivity
      linarith
    · have hdom : (-2 * v + 2 * t).exp ≤ (-(1 : ℝ) * v).exp * (2 * t - t ^ 2).exp := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
      have : 0 ≤ (-R * v).exp * (7 * t).exp := by positivity
      linarith

/-- **Theorem 3.6 of Paper C (`cauchy_moment_window`)**:
For polar functions `E, E'`, all sufficiently large `t`, and every `X ∈ [0, e^t]`, there exists
`u ∈ [t, t²]` with `E(u) - X E'(u) ≤ e^(-t)`. -/
theorem cauchy_moment_window {E E' : ℝ → ℝ} {r r' : ℂ → ℂ}
    (hE : IsPolar E r) (hE' : IsPolar E' r') :
    ∀ᶠ t in atTop, ∀ X ∈ Icc (0 : ℝ) t.exp,
      ∃ u ∈ Icc t (t ^ 2), E u - X * E' u ≤ (-t).exp := by
  obtain ⟨R, hE_ev, hE'_ev, hR_gt3, hR_lt4⟩ :=
    (hE.eventually_moment_le.and
      (hE'.eventually_moment_le.and (Ioo_mem_nhdsGT (by norm_num : (3 : ℝ) < 4)))).exists
  have hR_pos : 0 < R := by linarith
  have hlogR3_pos : 0 < Real.log R - Real.log 3 := sub_pos.mpr (Real.log_lt_log (by norm_num) hR_gt3)
  filter_upwards [hE_ev, hE'_ev, mem_atTop (99 / (Real.log R - Real.log 3)), mem_atTop (9 : ℝ)]
    with t ⟨hE_grow, hE_mom⟩ ⟨hE'_grow, hE'_mom⟩ ht_log ht9
  intro X ⟨hX0, hX_le⟩
  let k : ℕ := ⌈t ^ 2 / 9⌉₊
  have hk_ge : t ^ 2 / 9 ≤ (k : ℝ) := Nat.le_ceil _
  have hk_lt : (k : ℝ) < t ^ 2 / 9 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlaplace : ∀ α : ℝ, 0 < α →
      ∫ v in Ioi (0 : ℝ), v ^ k * (-α * v).exp = (k ! : ℝ) / α ^ (k + 1) := fun α hα ↦ by
    exact_mod_cast (@laplace_pow (α : ℂ) (by simpa using hα) k)
  have hint_exp : ∀ α : ℝ, 0 < α → IntegrableOn (fun v : ℝ ↦ v ^ k * (-α * v).exp) (Ioi 0) :=
    fun α hα ↦ Integrable.of_integral_ne_zero (by rw [hlaplace α hα]; positivity)
  have hgrowth_const : t + t * X + 1 ≤ (2 * t).exp := by
    have : t + 1 ≤ t.exp := by linarith [Real.add_one_le_exp t]
    have : (2 * t).exp = t.exp * t.exp := by rw [two_mul, Real.exp_add]
    nlinarith [Real.exp_pos t]
  by_contra hno; push Not at hno
  let g : ℝ → ℝ := fun v ↦ v ^ k * ((-R * v).exp * (7 * t).exp +
      (-(1 : ℝ) * v).exp * (2 * t - t ^ 2).exp + (-3 * v).exp * (E v - X * E' v - (-t).exp))
  have hint_nonneg : 0 ≤ ∫ v in Ioi (0 : ℝ), g v :=
    setIntegral_nonneg measurableSet_Ioi
      (cauchy_integrand_nonneg k hR_gt3 hR_lt4 ht9 hX0 hgrowth_const hE_grow hE'_grow hno)
  let fR : ℝ → ℝ := fun v ↦ v ^ k * (-R * v).exp * (7 * t).exp
  let f1 : ℝ → ℝ := fun v ↦ v ^ k * (-(1 : ℝ) * v).exp * (2 * t - t ^ 2).exp
  let f3 : ℝ → ℝ := fun v ↦ v ^ k * (-3 * v).exp * (-t).exp
  let fE : ℝ → ℝ := fun v ↦ v ^ k * (-3 * v).exp * E v
  let fE' : ℝ → ℝ := fun v ↦ X * (v ^ k * (-3 * v).exp * E' v)
  have hI_R : IntegrableOn fR (Ioi 0) := (hint_exp R hR_pos).mul_const _
  have hI_1 : IntegrableOn f1 (Ioi 0) := (hint_exp 1 zero_lt_one).mul_const _
  have hI_3 : IntegrableOn f3 (Ioi 0) := (hint_exp 3 (by norm_num)).mul_const _
  have hI_E : IntegrableOn fE (Ioi 0) := (hE_mom k).1
  have hI_E' : IntegrableOn fE' (Ioi 0) := (hE'_mom k).1.const_mul X
  have h12 : IntegrableOn (fun v ↦ fR v + f1 v) (Ioi 0) := hI_R.add hI_1
  have hEE' : IntegrableOn (fun v ↦ fE v - fE' v) (Ioi 0) := hI_E.sub hI_E'
  have h12EE' : IntegrableOn (fun v ↦ (fR v + f1 v) + (fE v - fE' v)) (Ioi 0) := h12.add hEE'
  have hg_eq : g = fun v ↦ ((fR v + f1 v) + (fE v - fE' v)) - f3 v := funext fun v ↦ by
    dsimp only [g, fR, f1, f3, fE, fE']; ring
  rw [hg_eq] at hint_nonneg
  dsimp only at hint_nonneg
  rw [integral_sub h12EE' hI_3, integral_add h12 hEE', integral_add hI_R hI_1,
    integral_sub hI_E hI_E'] at hint_nonneg
  simp only [fR, f1, f3, fE, fE', integral_mul_const, integral_const_mul,
    hlaplace R hR_pos, hlaplace 1 zero_lt_one, hlaplace 3 (by norm_num), one_pow, div_one] at hint_nonneg
  have hdiff_mom : (∫ v in Ioi (0 : ℝ), v ^ k * (-3 * v).exp * E v) -
      X * (∫ v in Ioi (0 : ℝ), v ^ k * (-3 * v).exp * E' v) ≤ (k ! : ℝ) * (2 * t).exp / R ^ k := by
    have hE_hi := (abs_le.mp (hE_mom k).2).2
    have hE'_lo := mul_le_mul_of_nonneg_left (abs_le.mp (hE'_mom k).2).1 hX0
    have hring : (k ! : ℝ) * t / R ^ k + X * ((k ! : ℝ) * t / R ^ k) =
        (k ! : ℝ) * (t + t * X) / R ^ k := by ring
    have hstep : (k ! : ℝ) * (t + t * X) / R ^ k ≤ (k ! : ℝ) * (2 * t).exp / R ^ k := by gcongr; linarith
    linarith
  -- Each of the three RHS terms is strictly less than `1/3` of the LHS.
  have hkf_pos : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hk_log : 11 * t ≤ (k : ℝ) * (Real.log R - Real.log 3) := by
    have := (div_le_iff₀ hlogR3_pos).mp ht_log; nlinarith
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 < 1.1 := by linarith [Real.log_three_lt_d9]
  have htails : (k ! : ℝ) / R ^ (k + 1) * (7 * t).exp < (k ! : ℝ) / 3 ^ (k + 1) * (-t).exp / 3 ∧
      (k ! : ℝ) * (2 * t - t ^ 2).exp < (k ! : ℝ) / 3 ^ (k + 1) * (-t).exp / 3 ∧
      (k ! : ℝ) * (2 * t).exp / R ^ k < (k ! : ℝ) / 3 ^ (k + 1) * (-t).exp / 3 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      (rw [← Real.log_lt_log_iff (by positivity) (by positivity)]
       simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow, Real.log_exp,
         Nat.cast_add, Nat.cast_one]
       try linarith)
    have hbound_k : ((k : ℝ) + 2) * Real.log 3 < (t ^ 2 / 9 + 3) * 1.1 := by
      nlinarith only [hk_lt, hlog3, hlog3_pos]
    nlinarith only [hbound_k, ht9]
  linarith

/-- **Theorem 3.5 of Paper C (`one_sided_zero_free_criterion`)**:
If `β > 1/2` and every prime `d ≡ a (mod M)` (`a ∈ (ℤ/Mℤ)×`) satisfies `d ≡ 7 (mod 8)`,
`gcd(M, d) = 1`, and `primeError d M x ≤ x^(β - 1)` eventually, then `entireL χ ρ ≠ 0` for every
`χ mod M` and `Re ρ > β`. -/
theorem one_sided_zero_free_criterion {M : ℕ} [NeZero M] {a : ZMod M} {β : ℝ}
    (hβ : 1 / 2 < β) (ha : IsUnit a)
    (hbound : ∀ d : Nat.Primes, (d : ZMod M) = a →
      (d.1 % 8 = 7 ∧ M.Coprime d) ∧ ∀ᶠ x in atTop, primeError d M x ≤ x ^ (β - 1))
    (ρ : ℂ) (hρ : β < ρ.re) (χ : DirichletCharacter ℂ M) : entireL χ ρ ≠ 0 := by
  by_cases hρ_ge1 : 1 ≤ ρ.re
  · exact entireL_ne_zero χ hρ_ge1
  have hρ_lt1 : ρ.re < 1 := not_le.mp hρ_ge1
  obtain ⟨d, hd_eq, hno_twist_zero⟩ :=
    exists_entireL_quadTwist_ne_zero |ρ.im| hβ ha (fun d hd ↦ (hbound d hd).1)
  have : Fact d.1.Prime := ⟨d.2⟩
  obtain ⟨⟨hd_mod8, hd_cop⟩, hd_ev⟩ := hbound d hd_eq
  have hord0 : ∀ {K : ℕ} [NeZero K] (ψ : DirichletCharacter ℂ K) (z : ℂ),
      entireL ψ z ≠ 0 → analyticOrderNatAt (entireL ψ) z = 0 :=
    fun ψ _ hz ↦ (tendsto_sub_mul_logDeriv_entireL ψ).1.mpr hz
  have hres_nonneg : ∀ x : ℝ, β < x →
      0 ≤ ((∑ ψ : DirichletCharacter ℂ M,
          ((analyticOrderNatAt (@entireL M _ ψ) (x : ℂ) : ℂ) -
            (analyticOrderNatAt (entireL (quadTwist ψ d)) (x : ℂ) : ℂ))) /
          (Nat.totient M : ℂ) / ((x : ℂ) * (1 - (x : ℂ)))).re := fun x hx ↦ by
    by_cases hx1 : 1 ≤ x
    · have hzero : ∀ ψ : DirichletCharacter ℂ M,
          (analyticOrderNatAt (@entireL M _ ψ) (x : ℂ) : ℂ) -
            (analyticOrderNatAt (entireL (quadTwist ψ d)) (x : ℂ) : ℂ) = 0 := fun ψ ↦ by
        simp [hord0 ψ (x : ℂ) (entireL_ne_zero ψ (by simpa using hx1)),
          hord0 (quadTwist ψ d) (x : ℂ) (entireL_ne_zero (quadTwist ψ d) (by simpa using hx1))]
      simp [Finset.sum_eq_zero fun ψ _ ↦ hzero ψ]
    · have htwist : ∀ ψ : DirichletCharacter ℂ M,
          analyticOrderNatAt (entireL (quadTwist ψ d)) (x : ℂ) = 0 := fun ψ ↦
        hord0 _ _ (hno_twist_zero ψ x (by simpa using hx.le) (by simp))
      have hreal : (((∑ ψ : DirichletCharacter ℂ M,
            ((analyticOrderNatAt (@entireL M _ ψ) (x : ℂ) : ℂ) -
              (analyticOrderNatAt (entireL (quadTwist ψ d)) (x : ℂ) : ℂ))) /
            (Nat.totient M : ℂ) / ((x : ℂ) * (1 - (x : ℂ)))).re) =
          ((∑ ψ : DirichletCharacter ℂ M, analyticOrderNatAt (@entireL M _ ψ) (x : ℂ) : ℕ) : ℝ) /
            (Nat.totient M : ℝ) / (x * (1 - x)) := by
        simp only [htwist, Nat.cast_zero, sub_zero, ← Nat.cast_sum]
        rw [← Complex.ofReal_re (((∑ ψ : DirichletCharacter ℂ M,
          analyticOrderNatAt (@entireL M _ ψ) (x : ℂ) : ℕ) : ℝ) /
          (Nat.totient M : ℝ) / (x * (1 - x)))]
        congr 1; push_cast; rfl
      rw [hreal]
      have : 0 < x := by linarith
      have : 0 < 1 - x := by linarith [not_le.mp hx1]
      positivity
  have hbound_exp : ∀ᶠ v in atTop, primeError d M v.exp ≤ ((β - 1) * v).exp := by
    filter_upwards [tendsto_exp_atTop.eventually hd_ev] with v hv
    simpa [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp, mul_comm] using hv
  have hres_zero := (isPolar_primeError hd_mod8 hd_cop).landau (by linarith : 0 < β)
    hres_nonneg hbound_exp hρ
  have htwist_rho : ∀ ψ : DirichletCharacter ℂ M,
      analyticOrderNatAt (entireL (quadTwist ψ d)) ρ = 0 := fun ψ ↦
    hord0 _ _ (hno_twist_zero ψ ρ hρ.le le_rfl)
  have hφ_ne : (Nat.totient M : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))).ne'
  have hρ_ne0 : ρ ≠ 0 := ne_of_apply_ne Complex.re (by simp; linarith)
  have h1ρ_ne0 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (ne_of_apply_ne Complex.re (by simp; linarith)).symm
  have hnum_zero := (div_eq_zero_iff.mp
    ((div_eq_zero_iff.mp hres_zero).resolve_right (mul_ne_zero hρ_ne0 h1ρ_ne0))).resolve_right hφ_ne
  simp only [htwist_rho, Nat.cast_zero, sub_zero, ← Nat.cast_sum, Nat.cast_eq_zero] at hnum_zero
  exact (tendsto_sub_mul_logDeriv_entireL χ).1.mp
    ((Finset.sum_eq_zero_iff.mp hnum_zero) χ (Finset.mem_univ χ))

end Readable.AnalyticEndgame
