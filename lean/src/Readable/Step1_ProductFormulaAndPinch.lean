import New.Heights.OneDeterminant

/-!
# Step 1: Product Formula, Greedy Covering, and the Twisted-Lattice Volume Pinch

Proofs of the linear-algebraic and height-theoretic steps from **Sections 4 and 7** of Paper C:

1. **Rational product formula (`rational_product_formula_log`)**: For nonzero `q ∈ ℚ` with
   `max(|num q|, den q) < M`, `log |q| + ∑_{p < M prime} log |q|_p = 0`.
2. **Product formula for heights (`product_formula_for_heights`, Lemma 4.3)**: `HeightLe c 1 → 0 ≤ c`.
3. **Greedy covering from spreading (`greedy_covering_from_spread`, Lemma 7.1)**: An `η`-spread
   family `B : Θ → (V →ₗ[ℂ] W)` admits `t : Finset Θ` with `#t · dim V ≤ 5 dim W log(1 + η⁻¹)`
   covering at least `(1 - 4η) dim W` dimensions.
4. **Twisted-lattice volume pinch (`twisted_lattice_volume_pinch`, Theorem 4.4(2))**: Combining
   upper and lower height bounds for `Z(θ)/Z(1)` and `Z(1)²/Z(θ)²` yields `0 ≤ c_up + c_low`.
-/

open Filter Finset IntermediateField Module Real AdjoinSimple Submodule

namespace Readable.ProductFormulaAndPinch

private lemma log_nat_eq_sum_padicValNat {M n : ℕ} (hn : n ≠ 0) (hnM : n < M) :
    Real.log (n : ℝ) = ∑ p ∈ Finset.range M with p.Prime, (padicValNat p n : ℝ) * Real.log p := by
  have hcast : (n : ℝ) = ∏ p ∈ Finset.range M with p.Prime, (p : ℝ) ^ padicValNat p n := by
    exact_mod_cast (Nat.prod_pow_prime_padicValNat n hn M hnM).symm
  rw [hcast, Real.log_prod fun p hp ↦ pow_ne_zero _ (Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.pos).ne']
  exact Finset.sum_congr rfl fun p _ ↦ Real.log_pow _ _

/-- **Rational product formula in logarithms** (Section 4.1 of Paper C). -/
theorem rational_product_formula_log {M : ℕ} {q : ℚ} (hq : q ≠ 0) (hM : q.num.natAbs ⊔ q.den < M) :
    Real.log (q : ℝ) + ∑ p ∈ Finset.range M with p.Prime, Real.log (padicNorm p q) = 0 := by
  have hnum := log_nat_eq_sum_padicValNat (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq))
    (lt_of_le_of_lt le_sup_left hM)
  have hden := log_nat_eq_sum_padicValNat q.den_nz (lt_of_le_of_lt le_sup_right hM)
  have hlog_q : Real.log (q : ℝ) = Real.log (q.num.natAbs : ℝ) - Real.log (q.den : ℝ) := by
    rw [q.cast_def, Real.log_div (by exact_mod_cast Rat.num_ne_zero.mpr hq)
      (by exact_mod_cast q.den_nz), ← Real.log_abs, ← Int.cast_abs, ← Int.natCast_natAbs,
      Int.cast_natCast]
  have hlog_padic : ∀ p ∈ (Finset.range M).filter Nat.Prime,
      Real.log (padicNorm p q) =
        ((padicValNat p q.den : ℝ) - (padicValNat p q.num.natAbs : ℝ)) * Real.log p := fun p hp ↦ by
    have : Fact p.Prime := ⟨(Finset.mem_filter.mp hp).2⟩
    rw [padicNorm.eq_zpow_of_nonzero hq, Rat.cast_zpow, Rat.cast_natCast, Real.log_zpow]
    simp only [padicValRat, padicValInt, Int.cast_neg, Int.cast_sub, Int.cast_natCast]; ring
  rw [hlog_q, hnum, hden, Finset.sum_congr rfl hlog_padic, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun p _ ↦ by ring

/-- **Lemma 4.3 of Paper C (`product_formula_for_heights`)**: `HeightLe c 1 → 0 ≤ c`.
Bounded `2`-adic norms force the witness `H ≠ 0` to be algebraic over `ℚ`; applying
`rational_product_formula_log` to `q = Nm_{ℚ(H)/ℚ}(H)` yields `0 ≤ c`. -/
theorem product_formula_for_heights {c : ℝ} (h : HeightLe c 1) : 0 ≤ c := by
  rcases h with ⟨H, α, e, hH_ne, harch, hpadic, hsum_le⟩
  have hpadic' : ∀ ι : PrimePadicIso, ‖ι.2 H‖ ≤ Real.exp (e ι.1) := fun ι ↦ by
    simpa only [Pi.one_apply, mul_one] using hpadic ι
  have hH_alg : IsAlgebraic ℚ H :=
    isAlgebraic_of_padic (c := Real.exp (e 2))
      (fun ι ↦ by simpa using hpadic' ⟨⟨2, Nat.prime_two⟩, ι⟩)
  have : FiniteDimensional ℚ ℚ⟮H⟯ := IntermediateField.adjoin.finiteDimensional hH_alg.isIntegral
  have : NumberField ℚ⟮H⟯ := NumberField.mk
  let q : ℚ := Algebra.norm ℚ (IntermediateField.AdjoinSimple.gen ℚ H)
  let n : ℕ := Module.finrank ℚ ℚ⟮H⟯
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := ℚ⟮H⟯)
  have hq_ne : q ≠ 0 := Algebra.norm_ne_zero_iff.mpr fun h0 ↦ hH_ne (congrArg Subtype.val h0)
  have hnorm_bound : ∀ {F : Type} [NormedField F] [CharZero F] [IsAlgClosed F]
      (_ : Cardinal.mk ℂ = Cardinal.mk F) (b : ℝ),
      (∀ ι : ℂ ≃+* F, ‖ι H‖ ≤ Real.exp b) → Real.log ‖algebraMap ℚ F q‖ / n ≤ b := by
    intro F _ _ _ hcard b hb
    have hprod_le : ‖algebraMap ℚ F q‖ ≤ (Real.exp b) ^ n := by
      calc ‖algebraMap ℚ F q‖
          = ∏ σ : ℚ⟮H⟯ →ₐ[ℚ] F, ‖σ (IntermediateField.AdjoinSimple.gen ℚ H)‖ := by
              rw [Algebra.norm_eq_prod_embeddings ℚ F, norm_prod]
        _ ≤ ∏ _σ : ℚ⟮H⟯ →ₐ[ℚ] F, Real.exp b :=
              Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun σ _ ↦ by
                obtain ⟨ι, hι⟩ := exists_ringEquiv_extend hcard ℚ⟮H⟯.val σ.toRingHom
                have hval : σ (IntermediateField.AdjoinSimple.gen ℚ H) = ι H :=
                  (hι (IntermediateField.AdjoinSimple.gen ℚ H)).symm
                rw [hval]; exact hb ι
        _ = (Real.exp b) ^ n := by simp [n]
    have hqF_pos : 0 < ‖algebraMap ℚ F q‖ := norm_pos_iff.mpr (by simpa using hq_ne)
    exact (div_le_iff₀ hn_pos).mpr <|
      (Real.log_le_log hqF_pos hprod_le).trans_eq (by rw [Real.log_pow, Real.log_exp]; ring)
  have harch_q : Real.log (q : ℝ) / n ≤ α := by
    simpa [Real.log_abs] using hnorm_bound (F := ℂ) rfl α harch
  have hpadic_q : ∀ l : ℕ, l.Prime → Real.log (padicNorm l q) / n ≤ e l := fun l hl ↦ by
    have : Fact l.Prime := ⟨hl⟩
    have hL := hnorm_bound (F := PadicAlgCl l) (@mk_complex_eq_mk_padicAlgCl l _) (e l)
      (fun ι ↦ hpadic' ⟨⟨l, hl⟩, ι⟩)
    have hext : ‖algebraMap ℚ (PadicAlgCl l) q‖ = padicNorm l q := by
      rw [IsScalarTower.algebraMap_apply ℚ ℚ_[l] (PadicAlgCl l), @PadicAlgCl.norm_extends l _]
      exact @Padic.eq_padicNorm l _ q
    rwa [hext] at hL
  rcases Filter.eventually_atTop.mp hsum_le with ⟨M₀, hM₀⟩
  let M : ℕ := max M₀ (q.num.natAbs ⊔ q.den + 1)
  have hM_gt : q.num.natAbs ⊔ q.den < M := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right M₀ _)
  have hprod_zero := rational_product_formula_log hq_ne hM_gt
  calc (0 : ℝ)
      = (Real.log (q : ℝ) + ∑ l ∈ Finset.range M with l.Prime, Real.log (padicNorm l q)) / n := by
          rw [hprod_zero, zero_div]
    _ = Real.log (q : ℝ) / n + ∑ l ∈ Finset.range M with l.Prime, Real.log (padicNorm l q) / n := by
          rw [add_div, Finset.sum_div]
    _ ≤ α + ∑ l ∈ Finset.range M with l.Prime, e l :=
          add_le_add harch_q (Finset.sum_le_sum fun l hl ↦ hpadic_q l (Finset.mem_filter.mp hl).2)
    _ ≤ c := hM₀ M (le_max_left _ _)

private lemma finrank_quot_sub_add_comap {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ V] [Module.Finite ℂ W]
    (F : Submodule ℂ W) (f : V →ₗ[ℂ] W) :
    (Module.finrank ℂ (W ⧸ F) : ℝ) - Module.finrank ℂ (W ⧸ (F ⊔ f.range)) +
      Module.finrank ℂ (Submodule.comap f F) = Module.finrank ℂ V := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (F.mkQ.comp f)
  rw [LinearMap.ker_comp, Submodule.ker_mkQ, LinearMap.range_comp] at hrn
  have hq := (Submodule.map F.mkQ f.range).finrank_quotient_add_finrank
  rw [(Submodule.quotientQuotientEquivQuotientSup F f.range).finrank_eq] at hq
  have hle : Module.finrank ℂ (W ⧸ (F ⊔ f.range)) ≤ Module.finrank ℂ (W ⧸ F) := by omega
  have hsub : Module.finrank ℂ (Submodule.map F.mkQ f.range) =
      Module.finrank ℂ (W ⧸ F) - Module.finrank ℂ (W ⧸ (F ⊔ f.range)) := Nat.eq_sub_of_add_eq' hq
  rw [hsub] at hrn
  have hcast : ((Module.finrank ℂ (W ⧸ F) - Module.finrank ℂ (W ⧸ (F ⊔ f.range)) : ℕ) : ℝ) =
      (Module.finrank ℂ (W ⧸ F) : ℝ) - Module.finrank ℂ (W ⧸ (F ⊔ f.range)) := Nat.cast_sub hle
  rw [← hcast]; exact_mod_cast hrn

private lemma greedy_potential_drop {w v q q' η : ℝ} (hw : 0 < w) (hv : 0 < v) (hη : 0 < η)
    (hq' : 0 ≤ q') (hq_big : 4 * η * w < q) (hstep : (q / (2 * w) - η) * v ≤ q - q') :
    5 * w * Real.log (1 + q' / w / η) - 5 * w * Real.log (1 + q / w / η) ≤ -v := by
  set a := 1 + q' / w / η; set b := 1 + q / w / η
  have hq_pos : 0 < q := by nlinarith
  have ha_pos : 0 < a := by positivity
  have hb_pos : 0 < b := by positivity
  have hden_pos : 0 < η * w + q := by positivity
  have hratio : a / b - 1 = -(q - q') / (η * w + q) := by
    dsimp only [a, b]; field_simp [hη.ne', hw.ne', hb_pos.ne', hden_pos.ne']; ring
  have hlog : 5 * w * (Real.log a - Real.log b) ≤ 5 * w * (-(q - q') / (η * w + q)) := by
    rw [← hratio, ← Real.log_div ha_pos.ne' hb_pos.ne']
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ha_pos hb_pos)) (by positivity)
  have halg : 5 * w * (-(q - q') / (η * w + q)) ≤ -v := by
    rw [← mul_div_assoc, div_le_iff₀ hden_pos]
    have : 5 * w * (q / (2 * w) - η) = 5 / 2 * q - 5 * η * w := by field_simp [hw.ne']
    have h1 : (η * w + q) * v ≤ 5 * w * ((q / (2 * w) - η) * v) := by nlinarith
    nlinarith
  linarith [mul_sub (5 * w) (Real.log a) (Real.log b)]

/-- **Lemma 7.1 of Paper C (`greedy_covering_from_spread`)**:
An `η`-spread family `B : Θ → (V →ₗ[ℂ] W)` admits a finite `t : Finset Θ` with
`#t · dim V ≤ 5 dim W log(1 + η⁻¹)` and `dim (∑_{s ∈ t} range(B s)) ≥ (1 - 4η) dim W`. -/
theorem greedy_covering_from_spread {Θ V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ V] [Module.Finite ℂ W] [Nontrivial V]
    {B : Θ → V →ₗ[ℂ] W} {η : ℝ} (hη : 0 < η) (hspread : IsSpread B η) :
    ∃ t : Finset Θ,
      (t.card : ℝ) * Module.finrank ℂ V ≤ 5 * Module.finrank ℂ W * Real.log (1 + η⁻¹) ∧
      (1 - 4 * η) * Module.finrank ℂ W ≤ Module.finrank ℂ ↥(⨆ s ∈ t, (B s).range) := by
  let T : Finset Θ → Submodule ℂ W := fun t ↦ ⨆ s ∈ t, (B s).range
  let ψ : Submodule ℂ W → ℝ := fun F ↦
    5 * Module.finrank ℂ W * Real.log (1 + Module.finrank ℂ (W ⧸ F) / Module.finrank ℂ W / η)
  let budget : ℝ := 5 * Module.finrank ℂ W * Real.log (1 + η⁻¹)
  have hempty : ((∅ : Finset Θ).card : ℝ) * Module.finrank ℂ V + ψ (T ∅) ≤ budget := by
    simp only [card_empty, Nat.cast_zero, zero_mul, zero_add, ψ, budget]
    have hq_le : (Module.finrank ℂ (W ⧸ T ∅) : ℝ) / Module.finrank ℂ W ≤ 1 := by
      by_cases hW : (Module.finrank ℂ W : ℝ) = 0
      · simp [hW]
      · exact (div_le_one (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hW))).mpr
          (Nat.cast_le.mpr (Submodule.finrank_quotient_le (T ∅)))
    have harg : 1 + (Module.finrank ℂ (W ⧸ T ∅) : ℝ) / Module.finrank ℂ W / η ≤ 1 + η⁻¹ := by
      simpa [one_div] using add_le_add_left (div_le_div_of_nonneg_right hq_le hη.le) 1
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) harg) (by positivity)
  obtain ⟨t, ht_adm, ht_max⟩ := exists_maximalFor_of_wellFoundedGT
    (fun t : Finset Θ ↦ (t.card : ℝ) * Module.finrank ℂ V + ψ (T t) ≤ budget) T ⟨∅, hempty⟩
  have hψ_nonneg : 0 ≤ ψ (T t) := mul_nonneg (by positivity) (Real.log_nonneg <| by
    have : (0 : ℝ) ≤ Module.finrank ℂ (W ⧸ T t) / Module.finrank ℂ W / η := by positivity
    linarith)
  refine ⟨t, by linarith, ?_⟩
  by_contra hlt; push Not at hlt
  have hW_pos : (0 : ℝ) < Module.finrank ℂ W := by
    by_contra hW0
    have hW_eq : (Module.finrank ℂ W : ℝ) = 0 := le_antisymm (not_lt.mp hW0) (Nat.cast_nonneg _)
    rw [hW_eq, mul_zero] at hlt
    linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℂ ↥(⨆ s ∈ t, (B s).range))]
  have hV_pos : (0 : ℝ) < Module.finrank ℂ V := by exact_mod_cast Module.finrank_pos (R := ℂ) (M := V)
  obtain ⟨s, hs⟩ := hspread (T t)
  set F := T t; set F' := F ⊔ (B s).range
  have hqF : (Module.finrank ℂ (W ⧸ F) : ℝ) + Module.finrank ℂ F = Module.finrank ℂ W := by
    exact_mod_cast F.finrank_quotient_add_finrank
  have hrn := finrank_quot_sub_add_comap F (B s)
  have hstep : ((Module.finrank ℂ (W ⧸ F) : ℝ) / (2 * Module.finrank ℂ W) - η) *
      Module.finrank ℂ V ≤ (Module.finrank ℂ (W ⧸ F) : ℝ) - Module.finrank ℂ (W ⧸ F') := by
    have hφ : (1 - (Module.finrank ℂ F : ℝ) / Module.finrank ℂ W) / 2 =
        (Module.finrank ℂ (W ⧸ F) : ℝ) / (2 * Module.finrank ℂ W) := by
      field_simp [hW_pos.ne']; linarith
    have hs' : (Module.finrank ℂ (Submodule.comap (B s) F) : ℝ) ≤
        ((1 + (Module.finrank ℂ F : ℝ) / Module.finrank ℂ W) / 2 + η) * Module.finrank ℂ V := hs
    nlinarith
  have hq_big : 4 * η * Module.finrank ℂ W < Module.finrank ℂ (W ⧸ F) := by linarith
  have hdrop : ψ F' - ψ F ≤ -(Module.finrank ℂ V : ℝ) :=
    greedy_potential_drop hW_pos hV_pos hη (Nat.cast_nonneg _) hq_big hstep
  have hT_ins : T (insert s t) = F' := by simp only [T, F, F', Finset.iSup_insert, sup_comm]
  have hins_adm : ((insert s t).card : ℝ) * Module.finrank ℂ V + ψ (T (insert s t)) ≤ budget := by
    have hcard : ((insert s t).card : ℝ) ≤ (t.card : ℝ) + 1 := by exact_mod_cast Finset.card_insert_le s t
    rw [hT_ins]; nlinarith
  have hΔ_pos : 0 < (Module.finrank ℂ (W ⧸ F) : ℝ) - Module.finrank ℂ (W ⧸ F') := by
    have : 0 < (Module.finrank ℂ (W ⧸ F) : ℝ) / (2 * Module.finrank ℂ W) - η := by
      rw [sub_pos, lt_div_iff₀ (by positivity)]; linarith
    nlinarith
  have hstrict : F < F' := lt_of_le_of_ne le_sup_left fun heq ↦ by rw [heq] at hΔ_pos; linarith
  exact (not_lt_of_ge (ht_max hins_adm (hT_ins ▸ le_sup_left))) (hT_ins ▸ hstrict)

/-- **Theorem 4.4(2) of Paper C (`twisted_lattice_volume_pinch`)**:
Multiplying `(Z(θ)/Z(1))²` by `Z(1)²/Z(θ)²` gives `1` of height `2(c_up + c_low)`, forcing `0 ≤ c_up + c_low`. -/
theorem twisted_lattice_volume_pinch {Z₁ : ℂ} {Zθ : PrimePadicIso → ℂ}
    {c_up c_low : ℝ} (hZ₁ : Z₁ ≠ 0) (hZθ : ∀ ι, Zθ ι ≠ 0)
    (h_up : HeightLe c_up fun ι ↦ Zθ ι / Z₁)
    (h_low : HeightLe (2 * c_low) fun ι ↦ Z₁ ^ 2 / (Zθ ι) ^ 2) : 0 ≤ c_up + c_low := by
  have hsq_up : HeightLe (2 * c_up) ((fun ι ↦ Zθ ι / Z₁) ^ 2) := by
    simpa [Nat.cast_ofNat] using h_up.pow 2
  have h_one : HeightLe (2 * c_up + 2 * c_low) 1 :=
    (hsq_up.mul h_low).mono le_rfl fun ι ↦ by
      have hcancel : (Zθ ι / Z₁) ^ 2 * (Z₁ ^ 2 / (Zθ ι) ^ 2) = 1 := by field_simp [hZ₁, hZθ ι]
      simp [Pi.mul_apply, Pi.pow_apply, hcancel]
  linarith [product_formula_for_heights h_one]

end Readable.ProductFormulaAndPinch
