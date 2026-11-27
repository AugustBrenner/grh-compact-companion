import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Step 0: Stepanov's Elementary Bound for Cubic Curves y² = f(x) over 𝔽_p

Standalone Mathlib-only proof of **Theorem 2.1 of Paper C** (Stepanov, 1969): for an odd prime `p`,
a cubic `f ∈ 𝔽_p[X]`, and an odd `m ≥ 1` with `3m² + m + 5 ≤ p`, the projective point count
`N = 1 + |S_0| + 2|S_+|` of `y² = f(x)` over `𝔽_p = ZMod p` satisfies
`|N - (p + 1)| ≤ 2p/m + 3m + 4`.

1. **Auxiliary polynomial (`exists_aux_pair`)**: Rank–nullity gives a nonzero `(A, B)` of degree
   `< J` so `P(X) = A(X, X^p) + B(X, X^p) f(X)^((p-1)/2)` vanishes to order `≥ m` on `S_+`.
2. **Nonvanishing (`evalPoly_ne_zero`)**: Since `2J + 1 < p`, `P = 0` yields
   `f · A(X, X^p)² = f^p · B(X, X^p)²`, contradicting parity of the `p`-quotient of the degree.
3. **Multiplicity vs. degree (`stepanov_S_plus_bound`, `stepanov_warmup`)**: Root multiplicities
   bound `|S_+|`; a nonsquare twist `c · f` bounds `|S_-|` identically.
-/

noncomputable section
open Polynomial Finset Module
namespace Readable.StepanovWarmup

variable {p : ℕ} [Fact p.Prime]

private lemma natDegree_sum_le_bound {ι : Type*} {s : Finset ι} {g : ι → (ZMod p)[X]} {B : ℕ}
    (hg : ∀ i ∈ s, (g i).natDegree ≤ B) : (∑ i ∈ s, g i).natDegree ≤ B := by
  refine (natDegree_sum_le s g).trans ?_; rw [Finset.fold_max_le]; exact ⟨Nat.zero_le _, hg⟩

private lemma sum_rootMultiplicity_le_natDegree (P : (ZMod p)[X]) (S : Finset (ZMod p)) :
    ∑ x ∈ S, P.rootMultiplicity x ≤ P.natDegree := by
  have hsub : (∑ x ∈ S, Multiset.replicate (P.rootMultiplicity x) x) ≤ P.roots := by
    rw [Multiset.le_iff_count]; intro a; rw [Multiset.count_sum']
    by_cases ha : a ∈ S
    · rw [Finset.sum_eq_single a (fun b _ hba ↦ by simp [Multiset.count_replicate, hba])
        (fun h ↦ absurd ha h)]; simp [Polynomial.count_roots]
    · rw [Finset.sum_eq_zero fun b hb ↦ by
        simp [Multiset.count_replicate, show b ≠ a from fun h ↦ ha (h ▸ hb)]]
      exact Nat.zero_le _
  exact (by simpa using Multiset.card_le_card hsub : _ ≤ P.roots.card).trans (Polynomial.card_roots' P)

/-- Evaluate a polynomial family `A : Fin K → 𝔽_p[X]` at `(X, X^p)`. -/
def evalXXp {K : ℕ} (A : Fin K → (ZMod p)[X]) : (ZMod p)[X] := ∑ k : Fin K, A k * X ^ (k.1 * p)

lemma derivative_evalXXp {K : ℕ} (A : Fin K → (ZMod p)[X]) :
    derivative (evalXXp A) = evalXXp (fun k ↦ derivative (A k)) := by
  have hXp : ∀ k : ℕ, derivative ((X : (ZMod p)[X]) ^ (k * p)) = 0 := fun k ↦ by
    rw [derivative_X_pow]; simp [(ZMod.natCast_eq_zero_iff (k * p) p).mpr (dvd_mul_left p k)]
  simp [evalXXp, derivative_mul, hXp]

/-- By Fermat's Little Theorem (`x₀^p = x₀`), evaluating `evalXXp A` at `x₀ ∈ 𝔽_p` collapses `X^p ↦ X`. -/
lemma eval_evalXXp {K : ℕ} (A : Fin K → (ZMod p)[X]) (x₀ : ZMod p) :
    (evalXXp A).eval x₀ = (∑ k : Fin K, A k * X ^ k.1).eval x₀ := by
  simp only [evalXXp, eval_finsetSum, eval_mul, eval_pow, eval_X]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [pow_mul', ZMod.pow_card]

/-- Disjoint degree bands: `A ≠ 0` and `∀ k, (A k).natDegree < J ≤ p` imply `evalXXp A ≠ 0` and
`(evalXXp A).natDegree = k₀ * p + d` for some `k₀ : Fin K`, `d < J`. -/
lemma evalXXp_ne_zero_and_natDegree {K J : ℕ} (hJp : J ≤ p) (A : Fin K → (ZMod p)[X])
    (hdeg : ∀ k, (A k).natDegree < J) (hne : A ≠ 0) :
    evalXXp A ≠ 0 ∧ ∃ k₀ : Fin K, ∃ d < J, (evalXXp A).natDegree = k₀.1 * p + d := by
  have hS : (Finset.univ.filter fun k : Fin K ↦ A k ≠ 0).Nonempty := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hne; exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
  let k₀ := (Finset.univ.filter fun k : Fin K ↦ A k ≠ 0).max' hS
  have hk₀_ne : A k₀ ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem _ hS)).2
  have hne_0 : A k₀ * X ^ (k₀.1 * p) ≠ 0 := mul_ne_zero hk₀_ne (pow_ne_zero _ X_ne_zero)
  have hterm_deg : (A k₀ * X ^ (k₀.1 * p)).natDegree = k₀.1 * p + (A k₀).natDegree := by
    rw [natDegree_mul hk₀_ne (pow_ne_zero _ X_ne_zero), natDegree_X_pow, add_comm]
  have hdeg_strict : ∀ k ∈ Finset.univ.erase k₀,
      (A k * X ^ (k.1 * p)).degree < (A k₀ * X ^ (k₀.1 * p)).degree := fun k hk ↦ by
    by_cases hAk : A k = 0
    · rw [hAk, zero_mul, degree_zero]; exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hne_0)
    · have hk_lt : k.1 < k₀.1 := lt_of_le_of_ne
        (Finset.le_max' _ k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hAk⟩))
        (Fin.val_ne_of_ne (Finset.mem_erase.mp hk).1)
      rw [degree_eq_natDegree (mul_ne_zero hAk (pow_ne_zero _ X_ne_zero)), degree_eq_natDegree hne_0]
      exact_mod_cast (by
        rw [natDegree_mul hAk (pow_ne_zero _ X_ne_zero), natDegree_X_pow, hterm_deg]
        have := Nat.mul_le_mul_right p hk_lt; have := (hdeg k).trans_le hJp; nlinarith :
        (A k * X ^ (k.1 * p)).natDegree < (A k₀ * X ^ (k₀.1 * p)).natDegree)
  have hdeg_eq : (evalXXp A).degree = (A k₀ * X ^ (k₀.1 * p)).degree := by
    rw [evalXXp, ← Finset.add_sum_erase _ _ (Finset.mem_univ k₀),
      degree_add_eq_left_of_degree_lt ((degree_sum_le _ _).trans_lt
        ((Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hne_0))).mpr hdeg_strict))]
  have heval_ne : evalXXp A ≠ 0 := fun h0 ↦ degree_ne_bot.mpr hne_0 (by rw [← hdeg_eq, h0, degree_zero])
  refine ⟨heval_ne, k₀, (A k₀).natDegree, hdeg k₀, ?_⟩
  rw [degree_eq_natDegree heval_ne, degree_eq_natDegree hne_0] at hdeg_eq
  exact (Nat.cast_injective (R := WithBot ℕ) hdeg_eq).trans hterm_deg

lemma natDegree_evalXXp_le {K J : ℕ} (A : Fin K → (ZMod p)[X]) (hdeg : ∀ k, (A k).natDegree < J) :
    (evalXXp A).natDegree ≤ (K - 1) * p + (J - 1) :=
  natDegree_sum_le_bound fun k _ ↦ natDegree_mul_le.trans <| by
    rw [natDegree_X_pow]; have := Nat.mul_le_mul_right p (Nat.le_sub_one_of_lt k.2)
    have := Nat.le_sub_one_of_lt (hdeg k); omega

/-- Taylor multiplicity test in characteristic `p`: `m < p` and `P^(r)(x₀) = 0` (`r < m`) imply `m ≤ mult(x₀, P)`. -/
lemma le_rootMultiplicity_of_iterate_derivative_eval {P : (ZMod p)[X]} (hP : P ≠ 0)
    {x₀ : ZMod p} {m : ℕ} (hmp : m < p)
    (hderiv : ∀ r < m, (derivative^[r] P).eval x₀ = 0) : m ≤ P.rootMultiplicity x₀ := by
  have hcoeff : ∀ (Q : (ZMod p)[X]) r n,
      (derivative^[r] Q).coeff n = (((n + r).descFactorial r : ℕ) : ZMod p) * Q.coeff (n + r) := fun Q r ↦ by
    induction r with
    | zero => intro n; simp
    | succ r ih =>
      intro n; rw [Function.iterate_succ_apply', Polynomial.coeff_derivative, ih (n + 1),
        show n + (r + 1) = n + 1 + r by omega, Nat.descFactorial_succ,
        show n + 1 + r - r = n + 1 by omega]; push_cast; ring
  rw [le_rootMultiplicity_iff hP]
  let Q : (ZMod p)[X] := P.comp (X + C x₀)
  have hcomp : ∀ n, derivative^[n] Q = (derivative^[n] P).comp (X + C x₀) := fun n ↦ by
    induction n with | zero => rfl | succ n ih => simp [Function.iterate_succ_apply', ih, derivative_comp]
  have hQ_coeff : ∀ r < m, Q.coeff r = 0 := fun r hr ↦ by
    have hfact_ne : ((r.factorial : ℕ) : ZMod p) ≠ 0 := fun h0 ↦
      ((Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp ((ZMod.natCast_eq_zero_iff _ _).mp h0)).not_gt
        (hr.trans hmp)
    have hkey : ((r.factorial : ℕ) : ZMod p) * Q.coeff r = (derivative^[r] P).eval x₀ := by
      rw [← show (derivative^[r] Q).eval 0 = (derivative^[r] P).eval x₀ by simp [hcomp r, eval_comp],
        ← Polynomial.coeff_zero_eq_eval_zero, hcoeff Q r 0, zero_add, Nat.descFactorial_self]
    exact (mul_eq_zero.mp (hkey.trans (hderiv r hr))).resolve_left hfact_ne
  obtain ⟨R, hR⟩ := Polynomial.X_pow_dvd_iff.mpr hQ_coeff
  exact ⟨R.comp (X - C x₀), by rw [← show Q.comp (X - C x₀) = P by simp [Q, Polynomial.comp_assoc],
    hR, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]⟩

/-- Denominator-clearing step `g ↦ f * g' + c * f' * g` and iterated family recursion `(A_r, B_r)`. -/
def diffStep (f : (ZMod p)[X]) (c : ZMod p) (g : (ZMod p)[X]) : (ZMod p)[X] :=
  f * derivative g + C c * derivative f * g

def stepAB (f : (ZMod p)[X]) {K : ℕ} :
    ℕ → (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X]) →
      (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X])
  | 0, AB => AB
  | r + 1, AB =>
    let prev := stepAB f r AB
    (fun k ↦ diffStep f (-(r : ZMod p)) (prev.1 k),
     fun k ↦ diffStep f ((((p - 1) / 2 : ℕ) : ZMod p) - r) (prev.2 k))

lemma stepAB_linear (f : (ZMod p)[X]) {K : ℕ} (r : ℕ) (a : ZMod p)
    (x y : (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X])) :
    stepAB f r (a • x + y) = a • stepAB f r x + stepAB f r y := by
  have hd : ∀ c g₁ g₂, diffStep f c (a • g₁ + g₂) = a • diffStep f c g₁ + diffStep f c g₂ :=
    fun c g₁ g₂ ↦ by simp only [diffStep, smul_eq_C_mul, derivative_add, derivative_C_mul]; ring
  induction r with
  | zero => rfl
  | succ r ih => apply Prod.ext <;> funext k <;> simp only [stepAB, ih, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, hd]

lemma stepAB_natDegree_lt (f : (ZMod p)[X]) (hf : f.natDegree = 3) {K J : ℕ}
    (r : ℕ) (AB : (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X]))
    (hA : ∀ k, (AB.1 k).natDegree < J) (hB : ∀ k, (AB.2 k).natDegree < J) :
    (∀ k, ((stepAB f r AB).1 k).natDegree < 2 * r + J) ∧
    (∀ k, ((stepAB f r AB).2 k).natDegree < 2 * r + J) := by
  have hstep : ∀ (c : ZMod p) {n : ℕ} {g : (ZMod p)[X]}, g.natDegree < n →
      (diffStep f c g).natDegree < 2 + n := fun c {n g} hg ↦ (natDegree_add_le _ _).trans_lt <| max_lt
    (by by_cases hdg : derivative g = 0
        · simp [hdg]
        · have := natDegree_derivative_le g
          have : 0 < g.natDegree := Nat.pos_of_ne_zero fun h0 ↦
            hdg (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, derivative_C])
          exact natDegree_mul_le.trans_lt (by omega))
    (by have hdf : (derivative f).natDegree ≤ 2 := by have := natDegree_derivative_le f; omega
        have : (C c * derivative f).natDegree ≤ 2 := natDegree_mul_le.trans (by simp [hdf])
        exact natDegree_mul_le.trans_lt (by omega))
  induction r with
  | zero => simpa [stepAB] using And.intro hA hB
  | succ r ih =>
    constructor <;> intro k <;>
      simpa only [stepAB, show 2 * (r + 1) + J = 2 + (2 * r + J) by omega] using
        hstep _ (by first | exact ih.1 k | exact ih.2 k)

/-- Core identity of Step 1: `f^r · P^(r) = evalXXp (A_r) + evalXXp (B_r) · f^((p-1)/2)`. -/
lemma pow_mul_iterate_derivative (f : (ZMod p)[X]) {K : ℕ}
    (AB : (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X])) (r : ℕ) :
    let P := evalXXp AB.1 + evalXXp AB.2 * f ^ ((p - 1) / 2)
    f ^ r * derivative^[r] P =
      evalXXp (stepAB f r AB).1 + evalXXp (stepAB f r AB).2 * f ^ ((p - 1) / 2) := by
  intro P; induction r with
  | zero => simp [stepAB, P]
  | succ r ih =>
    have hderiv_pow : f * derivative (f ^ ((p - 1) / 2)) =
        C (((p - 1) / 2 : ℕ) : ZMod p) * derivative f * f ^ ((p - 1) / 2) := by
      cases (p - 1) / 2 with
      | zero => simp
      | succ t => rw [derivative_pow, pow_succ']; simp only [Nat.add_sub_cancel]; push_cast; ring
    have hstep_lhs : f ^ (r + 1) * derivative^[r + 1] P =
        f * derivative (f ^ r * derivative^[r] P) - C (r : ZMod p) * derivative f * (f ^ r * derivative^[r] P) := by
      rw [Function.iterate_succ_apply', derivative_mul, derivative_pow]
      cases r with | zero => simp | succ r' => simp only [pow_succ]; push_cast; ring
    have hdiff_eval : ∀ (c : ZMod p) (C0 : Fin K → (ZMod p)[X]),
        evalXXp (fun k ↦ diffStep f c (C0 k)) =
          f * evalXXp (fun k ↦ derivative (C0 k)) + C c * derivative f * evalXXp C0 := fun c C0 ↦ by
      simp only [evalXXp, diffStep, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    rw [hstep_lhs, ih, derivative_add, derivative_mul, derivative_evalXXp, derivative_evalXXp]
    simp only [stepAB, hdiff_eval, map_neg, map_sub]
    have hterm : f * (evalXXp (stepAB f r AB).2 * derivative (f ^ ((p - 1) / 2))) =
        C (((p - 1) / 2 : ℕ) : ZMod p) * derivative f * evalXXp (stepAB f r AB).2 * f ^ ((p - 1) / 2) :=
      calc _ = evalXXp (stepAB f r AB).2 * (f * derivative (f ^ ((p - 1) / 2))) := by ring
        _ = _ := by rw [hderiv_pow]; ring
    rw [mul_add, mul_add, hterm]; ring

/-- Collapsed evaluation polynomial `Q_r(X) = A_r(X, X) + B_r(X, X)`. -/
def collapsedQ (f : (ZMod p)[X]) {K : ℕ} (r : ℕ)
    (AB : (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X])) : (ZMod p)[X] :=
  ∑ k : Fin K, ((stepAB f r AB).1 k + (stepAB f r AB).2 k) * X ^ k.1

def coeffToPoly {K J : ℕ} (c : Fin K → Fin J → ZMod p) : Fin K → (ZMod p)[X] :=
  fun k ↦ ∑ j : Fin J, C (c k j) * X ^ j.1

lemma coeffToPoly_natDegree_lt {K J : ℕ} (hJ : 0 < J) (c : Fin K → Fin J → ZMod p) (k : Fin K) :
    (coeffToPoly c k).natDegree < J :=
  (natDegree_sum_le_bound fun j _ ↦ natDegree_mul_le.trans <| by
    rw [natDegree_C, natDegree_X_pow, zero_add]; exact Nat.le_sub_one_of_lt j.2).trans_lt (by omega)

lemma coeffToPoly_injective {K J : ℕ} : Function.Injective (coeffToPoly (p := p) (K := K) (J := J)) :=
  fun _ _ h ↦ funext fun k ↦ funext fun j ↦ by
    simpa [coeffToPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using
      congrArg (fun q : (ZMod p)[X] ↦ q.coeff j.1) (congrFun h k)

/-- Step 1 (auxiliary polynomial via rank–nullity): `2JK > ∑_{r<m} (2r + J + K - 1)` yields a
nonzero pair `(A, B)` of degree `< J` killing every `Q_r` (`0 ≤ r < m`). -/
lemma exists_aux_pair (f : (ZMod p)[X]) (hf : f.natDegree = 3) {m : ℕ} (hm_odd : Odd m) :
    let K := (m + 1) / 2
    let J := (3 * m ^ 2 + m) / 2 + 1
    ∃ AB : (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X]),
      AB ≠ 0 ∧ (∀ k, (AB.1 k).natDegree < J) ∧ (∀ k, (AB.2 k).natDegree < J) ∧
      ∀ r < m, collapsedQ f r AB = 0 := by
  intro K J; rcases hm_odd with ⟨u, rfl⟩
  have hK : K = u + 1 := by dsimp [K]; omega
  have hJ : J = 6 * u ^ 2 + 7 * u + 3 := by dsimp [J]; ring_nf; omega
  have hK_pos : 0 < K := by omega
  have hJ_pos : 0 < J := by omega
  let toAB : ((Fin K → Fin J → ZMod p) × (Fin K → Fin J → ZMod p)) →ₗ[ZMod p]
      (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X]) :=
    { toFun v := (coeffToPoly v.1, coeffToPoly v.2)
      map_add' x y := by apply Prod.ext <;> funext k <;> simp [coeffToPoly, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' c x := by apply Prod.ext <;> funext k <;> simp [coeffToPoly, smul_eq_C_mul, map_mul, Finset.mul_sum, mul_assoc] }
  have hQ_lin : ∀ r (a : ZMod p) (x y : (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X])),
      collapsedQ f r (a • x + y) = C a * collapsedQ f r x + collapsedQ f r y := fun r a x y ↦ by
    simp only [collapsedQ, stepAB_linear, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  let L : ((Fin K → Fin J → ZMod p) × (Fin K → Fin J → ZMod p)) →ₗ[ZMod p]
      ((r : Fin (2 * u + 1)) → Fin (2 * r.1 + J + K - 1) → ZMod p) :=
    { toFun v r d := (collapsedQ f r.1 (toAB v)).coeff d.1
      map_add' x y := funext fun r ↦ funext fun d ↦ by
        have hq := hQ_lin r.1 1 (toAB x) (toAB y); rw [one_smul, map_one, one_mul] at hq
        simp only [map_add, hq, Polynomial.coeff_add]; rfl
      map_smul' c x := funext fun r ↦ funext fun d ↦ by
        have hq := hQ_lin r.1 c (toAB x) 0
        have h0 : collapsedQ f r.1 (0 : (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X])) = 0 := by
          have h1 := hQ_lin r.1 1 0 0; rw [one_smul, map_one, one_mul, add_zero] at h1
          exact add_left_cancel (h1.symm.trans (add_zero _).symm)
        rw [add_zero, h0, add_zero] at hq
        simp only [map_smul, RingHom.id_apply, hq, Polynomial.coeff_C_mul]; rfl }
  have hdim_lt : Module.finrank (ZMod p) ((r : Fin (2 * u + 1)) → Fin (2 * r.1 + J + K - 1) → ZMod p) <
      Module.finrank (ZMod p) ((Fin K → Fin J → ZMod p) × (Fin K → Fin J → ZMod p)) := by
    have hV : Module.finrank (ZMod p) ((Fin K → Fin J → ZMod p) × (Fin K → Fin J → ZMod p)) = 2 * (K * J) := by
      simp [Module.finrank_prod, Module.finrank_pi_fintype]; ring
    have hW : Module.finrank (ZMod p) ((r : Fin (2 * u + 1)) → Fin (2 * r.1 + J + K - 1) → ZMod p) =
        ∑ r : Fin (2 * u + 1), (2 * r.1 + J + K - 1) := by simp [Module.finrank_pi_fintype]
    have hsum : ∑ r : Fin (2 * u + 1), (2 * r.1 + J + K - 1) =
        2 * (u * (2 * u + 1)) + (2 * u + 1) * (J + K - 1) := by
      rw [show (fun r : Fin (2 * u + 1) ↦ 2 * r.1 + J + K - 1) =
          (fun r : Fin (2 * u + 1) ↦ 2 * r.1 + (J + K - 1)) from funext fun r ↦ by omega,
        Finset.sum_add_distrib, ← Finset.mul_sum, show (∑ r : Fin (2 * u + 1), r.1) =
          ∑ r ∈ Finset.range (2 * u + 1), r from Fin.sum_univ_eq_sum_range id _,
        Finset.sum_range_id, Nat.add_sub_cancel, show (2 * u + 1) * (2 * u) = 2 * (u * (2 * u + 1)) by ring,
        Nat.mul_div_cancel_left _ (by norm_num), Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [hV, hW, hsum, hK, hJ, show 6 * u ^ 2 + 7 * u + 3 + (u + 1) - 1 = 6 * u ^ 2 + 8 * u + 3 by omega]
    nlinarith
  have hker_ne : LinearMap.ker L ≠ ⊥ := fun hbot ↦ by
    have hrn := LinearMap.finrank_range_add_finrank_ker L
    have := Submodule.finrank_le (LinearMap.range L); rw [hbot, finrank_bot] at hrn; omega
  obtain ⟨v, hv_ker, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  refine ⟨toAB v, fun h0 ↦ hv_ne ?_, fun k ↦ coeffToPoly_natDegree_lt hJ_pos v.1 k,
    fun k ↦ coeffToPoly_natDegree_lt hJ_pos v.2 k, fun r hr ↦ ?_⟩
  · have hz : coeffToPoly (p := p) (0 : Fin K → Fin J → ZMod p) = 0 := funext fun k ↦ by simp [coeffToPoly]
    exact Prod.ext (coeffToPoly_injective (by simpa [toAB, hz] using congrArg Prod.fst h0))
      (coeffToPoly_injective (by simpa [toAB, hz] using congrArg Prod.snd h0))
  · ext d
    by_cases hd : d < 2 * r + J + K - 1
    · simpa [L] using congrFun (congrFun (LinearMap.mem_ker.mp hv_ker) ⟨r, hr⟩) ⟨d, hd⟩
    · rcases stepAB_natDegree_lt f hf r (toAB v) (fun k ↦ coeffToPoly_natDegree_lt hJ_pos v.1 k)
        (fun k ↦ coeffToPoly_natDegree_lt hJ_pos v.2 k) with ⟨hAr, hBr⟩
      have hQ_le : (collapsedQ f r (toAB v)).natDegree ≤ 2 * r + J + K - 2 :=
        natDegree_sum_le_bound fun k _ ↦ natDegree_mul_le.trans <| by
          rw [natDegree_X_pow]; have := (natDegree_add_le _ _).trans_lt (max_lt (hAr k) (hBr k))
          have := Nat.le_sub_one_of_lt k.2; omega
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- Step 2 (nonvanishing by degree-quotient parity): `2J + 1 < p` and `(A, B) ≠ 0` of degree `< J`
force `P = A(X, X^p) + B(X, X^p) f^((p-1)/2) ≠ 0`. -/
lemma evalPoly_ne_zero (hp_odd : Odd p) (f : (ZMod p)[X]) (hf : f.natDegree = 3)
    {K J : ℕ} (h2Jp : 2 * J + 1 < p) (AB : (Fin K → (ZMod p)[X]) × (Fin K → (ZMod p)[X]))
    (hAB : AB ≠ 0) (hA : ∀ k, (AB.1 k).natDegree < J) (hB : ∀ k, (AB.2 k).natDegree < J) :
    evalXXp AB.1 + evalXXp AB.2 * f ^ ((p - 1) / 2) ≠ 0 := by
  intro hP0
  have hf_ne : f ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hf; omega
  have hJp : J ≤ p := by omega
  have hEq : evalXXp AB.1 = -evalXXp AB.2 * f ^ ((p - 1) / 2) := by
    simpa [neg_mul] using eq_neg_of_add_eq_zero_left hP0
  have hA_ne : AB.1 ≠ 0 := fun hA0 ↦ by
    have hB_eval := (evalXXp_ne_zero_and_natDegree hJp AB.2 hB (fun hB0 ↦ hAB (Prod.ext hA0 hB0))).1
    have h0 : evalXXp AB.1 = 0 := by simp [evalXXp, hA0]
    rw [h0, neg_mul] at hEq; exact mul_ne_zero hB_eval (pow_ne_zero _ hf_ne) (neg_eq_zero.mp hEq.symm)
  have hB_ne : AB.2 ≠ 0 := fun hB0 ↦ by
    have h0 : evalXXp AB.2 = 0 := by simp [evalXXp, hB0]
    rw [h0, neg_zero, zero_mul] at hEq; exact (evalXXp_ne_zero_and_natDegree hJp AB.1 hA hA_ne).1 hEq
  obtain ⟨hA_eval_ne, kA, dA, hdA, hdegA⟩ := evalXXp_ne_zero_and_natDegree hJp AB.1 hA hA_ne
  obtain ⟨hB_eval_ne, kB, dB, hdB, hdegB⟩ := evalXXp_ne_zero_and_natDegree hJp AB.2 hB hB_ne
  have hsq : f * (evalXXp AB.1) ^ 2 = f ^ p * (evalXXp AB.2) ^ 2 := by
    have h2h : 2 * ((p - 1) / 2) + 1 = p := by rcases hp_odd with ⟨q, rfl⟩; omega
    calc f * (evalXXp AB.1) ^ 2 = f * (-evalXXp AB.2 * f ^ ((p - 1) / 2)) ^ 2 := by rw [hEq]
      _ = f ^ (2 * ((p - 1) / 2) + 1) * (evalXXp AB.2) ^ 2 := by rw [mul_pow, neg_sq, ← pow_mul, pow_succ']; ring
      _ = f ^ p * (evalXXp AB.2) ^ 2 := by rw [h2h]
  have hdeg_eq := congrArg Polynomial.natDegree hsq
  rw [natDegree_mul hf_ne (pow_ne_zero 2 hA_eval_ne), natDegree_mul (pow_ne_zero p hf_ne) (pow_ne_zero 2 hB_eval_ne),
    natDegree_pow, natDegree_pow, natDegree_pow, hf, hdegA, hdegB] at hdeg_eq
  -- Dividing by `p` equates the even quotient `2 * kA` with the odd quotient `2 * kB + 3`.
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hL : (3 + 2 * (kA.1 * p + dA)) / p = 2 * kA.1 := by
    rw [show 3 + 2 * (kA.1 * p + dA) = (2 * dA + 3) + p * (2 * kA.1) by ring,
      Nat.add_mul_div_left _ _ hp_pos, Nat.div_eq_of_lt (by omega), zero_add]
  have hR : (p * 3 + 2 * (kB.1 * p + dB)) / p = 2 * kB.1 + 3 := by
    rw [show p * 3 + 2 * (kB.1 * p + dB) = (2 * dB) + p * (2 * kB.1 + 3) by ring,
      Nat.add_mul_div_left _ _ hp_pos, Nat.div_eq_of_lt (by omega), zero_add]
  have hquot := congrArg (· / p) hdeg_eq; rw [hL, hR] at hquot; omega

/-- Step 3 (one-sided Stepanov bound on `S_+`): `2m · |S_+| ≤ (m + 2) p + 3m² + m - 3`. -/
theorem stepanov_S_plus_bound (hp_odd : Odd p) (f : (ZMod p)[X]) (hf : f.natDegree = 3)
    {m : ℕ} (hm_odd : Odd m) (hmp : 3 * m ^ 2 + m + 5 ≤ p) :
    let S_plus := Finset.univ.filter fun x : ZMod p ↦ f.eval x ^ ((p - 1) / 2) = 1
    2 * m * S_plus.card ≤ (m + 2) * p + (3 * m ^ 2 + m - 3) := by
  intro S_plus
  let K := (m + 1) / 2; let J := (3 * m ^ 2 + m) / 2 + 1
  have h2Jp : 2 * J + 1 < p := by
    rcases hm_odd with ⟨u, rfl⟩; have : J = 6 * u ^ 2 + 7 * u + 3 := by dsimp [J]; ring_nf; omega
    nlinarith
  obtain ⟨AB, hAB_ne, hA_deg, hB_deg, hQ0⟩ := exists_aux_pair f hf hm_odd
  let P : (ZMod p)[X] := evalXXp AB.1 + evalXXp AB.2 * f ^ ((p - 1) / 2)
  have hP_ne : P ≠ 0 := evalPoly_ne_zero hp_odd f hf h2Jp AB hAB_ne hA_deg hB_deg
  have hmult : ∀ x₀ ∈ S_plus, m ≤ P.rootMultiplicity x₀ := fun x₀ hx₀ ↦ by
    have hfx_pow : f.eval x₀ ^ ((p - 1) / 2) = 1 := (Finset.mem_filter.mp hx₀).2
    have hfx_ne : f.eval x₀ ≠ 0 := fun h0 ↦ by
      have hp2 := (Fact.out : p.Prime).two_le
      have hpos : (p - 1) / 2 ≠ 0 := by rcases hp_odd with ⟨q, rfl⟩; omega
      rw [h0, zero_pow hpos] at hfx_pow; exact zero_ne_one hfx_pow
    refine le_rootMultiplicity_of_iterate_derivative_eval hP_ne (by nlinarith) fun r hr ↦ ?_
    have hpow := congrArg (Polynomial.eval x₀) (pow_mul_iterate_derivative f AB r)
    simp only [eval_mul, eval_pow, eval_add, eval_evalXXp, hfx_pow, mul_one] at hpow
    have hsum_Q : (∑ k : Fin K, (stepAB f r AB).1 k * X ^ k.1).eval x₀ +
        (∑ k : Fin K, (stepAB f r AB).2 k * X ^ k.1).eval x₀ = (collapsedQ f r AB).eval x₀ := by
      simp only [collapsedQ, add_mul, Finset.sum_add_distrib, eval_add]; rfl
    rw [hsum_Q, hQ0 r hr, eval_zero] at hpow
    exact (mul_eq_zero.mp hpow).resolve_left (pow_ne_zero r hfx_ne)
  have hcount : m * S_plus.card ≤ P.natDegree := calc
    m * S_plus.card = ∑ _x₀ ∈ S_plus, m := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ x₀ ∈ S_plus, P.rootMultiplicity x₀ := Finset.sum_le_sum hmult
    _ ≤ P.natDegree := sum_rootMultiplicity_le_natDegree P S_plus
  have hdegP : P.natDegree ≤ (K - 1) * p + (J - 1) + 3 * ((p - 1) / 2) := by
    have h1 : (evalXXp AB.1).natDegree ≤ (K - 1) * p + (J - 1) := natDegree_evalXXp_le AB.1 hA_deg
    have h2 : (evalXXp AB.2).natDegree ≤ (K - 1) * p + (J - 1) := natDegree_evalXXp_le AB.2 hB_deg
    have hfp : (f ^ ((p - 1) / 2)).natDegree ≤ 3 * ((p - 1) / 2) :=
      natDegree_pow_le.trans (by rw [hf]; ring_nf; rfl)
    exact (natDegree_add_le _ _).trans (max_le (h1.trans (Nat.le_add_right _ _)) (natDegree_mul_le.trans (by omega)))
  have hfinal := hcount.trans hdegP
  rcases hm_odd with ⟨u, rfl⟩; rcases hp_odd with ⟨q, rfl⟩
  have hK' : K - 1 = u := by dsimp [K]; omega
  have hJ' : J - 1 = 6 * u ^ 2 + 7 * u + 2 := by dsimp [J]; ring_nf; omega
  have hhalf : (2 * q + 1 - 1) / 2 = q := by omega
  have h3sub : 3 * (2 * u + 1) ^ 2 + (2 * u + 1) - 3 = 12 * u ^ 2 + 14 * u + 1 := by
    have : 3 * (2 * u + 1) ^ 2 + (2 * u + 1) = 12 * u ^ 2 + 14 * u + 4 := by ring
    omega
  rw [hK', hJ', hhalf] at hfinal; rw [h3sub]; nlinarith

/-- Euler's criterion partitions `𝔽_p` into `S_0 ⊔ S_+ ⊔ S_-`. -/
lemma card_partition_euler (hp_odd : Odd p) (f : (ZMod p)[X]) :
    (Finset.univ.filter fun x : ZMod p ↦ f.eval x = 0).card +
    (Finset.univ.filter fun x : ZMod p ↦ f.eval x ^ ((p - 1) / 2) = 1).card +
    (Finset.univ.filter fun x : ZMod p ↦ f.eval x ^ ((p - 1) / 2) = -1).card = p := by
  let χ : ZMod p → ZMod p := fun x ↦ f.eval x ^ ((p - 1) / 2)
  have hge2 := (Fact.out : p.Prime).two_le
  have hpos : (p - 1) / 2 ≠ 0 := by rcases hp_odd with ⟨q, rfl⟩; omega
  have hS0 : (Finset.univ.filter fun x : ZMod p ↦ f.eval x = 0) =
      Finset.univ.filter fun x : ZMod p ↦ χ x = 0 := by ext x; simp [χ, pow_eq_zero_iff hpos]
  have h1m1 : (1 : ZMod p) ≠ -1 := fun h ↦ by
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast; calc (2 : ZMod p) = 1 + 1 := by ring
        _ = 1 + -1 := by rw [← h]
        _ = 0 := by ring
    have := Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).mp h2)
    rcases hp_odd with ⟨q, hq⟩; omega
  have hmem : ∀ x ∈ (Finset.univ : Finset (ZMod p)), χ x ∈ ({0, 1, -1} : Finset (ZMod p)) := fun x _ ↦ by
    by_cases h0 : f.eval x = 0
    · simp [χ, h0, zero_pow hpos]
    · have hsq : (χ x) ^ 2 = 1 := by
        dsimp [χ]; rw [← pow_mul, show (p - 1) / 2 * 2 = p - 1 by rcases hp_odd with ⟨q, rfl⟩; omega]
        exact ZMod.pow_card_sub_one_eq_one h0
      rcases sq_eq_one_iff.mp hsq with h | h <;> simp [h]
  have hfib := Finset.card_eq_sum_card_fiberwise hmem
  rw [Finset.sum_insert (by simp [one_ne_zero.symm]), Finset.sum_insert (by simp [h1m1]),
    Finset.sum_singleton, Finset.card_univ, ZMod.card] at hfib
  rw [hS0]; linarith

/-- **Theorem 2.1 of Paper C (`Readable.StepanovWarmup.stepanov_warmup`).** -/
theorem stepanov_warmup (hp_odd : Odd p) (f : (ZMod p)[X]) (hf : f.natDegree = 3)
    {m : ℕ} (hm_odd : Odd m) (hmp : 3 * m ^ 2 + m + 5 ≤ p) :
    let S_0 := Finset.univ.filter fun x : ZMod p ↦ f.eval x = 0
    let S_plus := Finset.univ.filter fun x : ZMod p ↦ f.eval x ^ ((p - 1) / 2) = 1
    let N : ℕ := 1 + S_0.card + 2 * S_plus.card
    (S_plus.card : ℝ) ≤ (p : ℝ) / 2 + (p : ℝ) / m + (3 * m + 1 : ℝ) / 2 ∧
    |(N : ℝ) - (p + 1 : ℝ)| ≤ 2 * (p : ℝ) / m + 3 * (m : ℝ) + 4 := by
  intro S_0 S_plus N
  have hm_pos : (0 : ℝ) < m := by rcases hm_odd with ⟨u, rfl⟩; positivity
  have to_real : ∀ k : ℕ, 2 * m * k ≤ (m + 2) * p + (3 * m ^ 2 + m - 3) →
      (k : ℝ) ≤ (p : ℝ) / 2 + (p : ℝ) / m + (3 * m + 1 : ℝ) / 2 := fun k hk ↦ by
    have hcast : (2 * m * k : ℝ) ≤ ((m + 2) * p + (3 * m ^ 2 + m) : ℝ) := by
      exact_mod_cast (by omega : 2 * m * k ≤ (m + 2) * p + (3 * m ^ 2 + m))
    nlinarith [div_mul_cancel₀ (p : ℝ) hm_pos.ne']
  have hS_plus_real := to_real S_plus.card (stepanov_S_plus_bound hp_odd f hf hm_odd hmp)
  let S_minus := Finset.univ.filter fun x : ZMod p ↦ f.eval x ^ ((p - 1) / 2) = -1
  have hp2 : ringChar (ZMod p) ≠ 2 := by rcases hp_odd with ⟨q, rfl⟩; rw [ZMod.ringChar_zmod_n]; omega
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare (F := ZMod p) hp2
  have hc0 : c ≠ 0 := fun h0 ↦ hc (h0 ▸ IsSquare.zero)
  have hcpow : c ^ ((p - 1) / 2) = -1 := (sq_eq_one_iff.mp <| by
    rw [← pow_mul, show (p - 1) / 2 * 2 = p - 1 by rcases hp_odd with ⟨q, rfl⟩; omega]
    exact ZMod.pow_card_sub_one_eq_one hc0).resolve_left fun h1 ↦ hc <|
    (FiniteField.isSquare_iff hp2 hc0).mpr <| by
      have hdiv : p / 2 = (p - 1) / 2 := by rcases hp_odd with ⟨q, rfl⟩; omega
      simpa [ZMod.card, hdiv] using h1
  have hS_minus_eq : S_minus =
      Finset.univ.filter fun x : ZMod p ↦ (C c * f).eval x ^ ((p - 1) / 2) = 1 := by
    ext x; simp only [S_minus, Finset.mem_filter, Finset.mem_univ, true_and, eval_mul, eval_C,
      mul_pow, hcpow, neg_one_mul]
    exact ⟨fun h ↦ by rw [h, neg_neg], neg_eq_iff_eq_neg.mp⟩
  have hS_minus_real := to_real S_minus.card
    (hS_minus_eq ▸ stepanov_S_plus_bound hp_odd (C c * f) (by rw [natDegree_C_mul hc0, hf]) hm_odd hmp)
  have hpart : S_0.card + S_plus.card + S_minus.card = p := card_partition_euler hp_odd f
  have hpartR : (S_0.card : ℝ) + S_plus.card + S_minus.card = p := by exact_mod_cast hpart
  have hS0_le : (S_0.card : ℝ) ≤ 3 := by
    have hf_ne : f ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hf; omega
    exact_mod_cast (Finset.card_le_card fun x hx ↦ Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hf_ne).mpr (Finset.mem_filter.mp hx).2)).trans
      ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' f).trans_eq hf))
  have hN_eq : (N : ℝ) - (p + 1 : ℝ) = (S_plus.card : ℝ) - (S_minus.card : ℝ) := by
    dsimp [N]; push_cast; linarith
  have hmul_div : 2 * ((p : ℝ) / m) = 2 * (p : ℝ) / m := (mul_div_assoc 2 (p : ℝ) (m : ℝ)).symm
  refine ⟨hS_plus_real, ?_⟩
  rw [hN_eq, abs_le]; constructor <;> linarith

end Readable.StepanovWarmup
