import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Step 2: Behrend's Sphere Construction for Weighted 3-Term Ratios

Standalone Mathlib-only proof of **Proposition 4.7 of Paper C** (Behrend, 1946):
1. No-carry base-`B` encoding (`baseEncode_lt_pow`, `baseEncode_injective`, `baseEncode_linear`).
2. Dense sphere (`exists_dense_sphere`): some sphere in `{0, ..., M - 1}^n` has `≥ M^n / (n M²)` points.
3. Strict convexity (`sphere_no_weighted_midpoint`): weighted parallelogram identity forces collinear points on a sphere to coincide.
4. Group embedding (`behrend_three_term_free`): eliminates nontrivial weighted ratios `φ(τ / σ)^j = φ(ρ / σ)^i` (`0 < i < j ≤ L`).
-/

open Finset
namespace Readable.BehrendSphere

/-- Base-`B` encoding `∑_{i < n} d_i · B^i` of a digit vector `d : Fin n → ℕ`. -/
def baseEncode (B : ℕ) {n : ℕ} (d : Fin n → ℕ) : ℕ := ∑ i : Fin n, d i * B ^ i.1

lemma baseEncode_lt_pow (B : ℕ) :
    ∀ {n : ℕ} (d : Fin n → ℕ), (∀ i, d i < B) → baseEncode B d < B ^ n
  | 0, _, _ => by simp [baseEncode]
  | n + 1, d, hd => by
    have hlow := baseEncode_lt_pow B (fun i : Fin n ↦ d i.castSucc) (fun i ↦ hd i.castSucc)
    have hmul := Nat.mul_le_mul_right (B ^ n) (hd (Fin.last n))
    rw [baseEncode, Fin.sum_univ_castSucc, pow_succ']
    change baseEncode B (fun i : Fin n ↦ d i.castSucc) + d (Fin.last n) * B ^ n < B * B ^ n
    nlinarith

lemma baseEncode_injective (B : ℕ) :
    ∀ {n : ℕ} {d₁ d₂ : Fin n → ℕ},
      (∀ i, d₁ i < B) → (∀ i, d₂ i < B) → baseEncode B d₁ = baseEncode B d₂ → d₁ = d₂
  | 0, _, _, _, _, _ => funext fun i ↦ Fin.elim0 i
  | n + 1, d₁, d₂, h₁, h₂, heq => by
    have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (h₁ 0)
    have hsplit : ∀ d : Fin (n + 1) → ℕ,
        baseEncode B d = d 0 + B * baseEncode B (fun i : Fin n ↦ d i.succ) := fun d ↦ by
      simp only [baseEncode, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
        pow_succ', Finset.mul_sum]; congr 1; exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsplit d₁, hsplit d₂] at heq
    have h0 : d₁ 0 = d₂ 0 := by
      have := congrArg (· % B) heq
      rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (h₁ 0), Nat.mod_eq_of_lt (h₂ 0)] at this
    have htail : baseEncode B (fun i : Fin n ↦ d₁ i.succ) = baseEncode B (fun i : Fin n ↦ d₂ i.succ) := by
      have := congrArg (· / B) heq
      rwa [Nat.add_mul_div_left _ _ hB, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (h₁ 0), Nat.div_eq_of_lt (h₂ 0), zero_add, zero_add] at this
    exact funext <| Fin.cases h0 fun j ↦
      congrFun (baseEncode_injective B (fun i ↦ h₁ i.succ) (fun i ↦ h₂ i.succ) htail) j

lemma baseEncode_linear (B : ℕ) {n : ℕ} (a b : ℕ) (u v : Fin n → ℕ) :
    baseEncode B (fun i ↦ a * u i + b * v i) = a * baseEncode B u + b * baseEncode B v := by
  simp only [baseEncode, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- Squared Euclidean norm `∑ i, (d i)²` of a digit vector `d : Fin n → Fin H`. -/
def sqNorm {n H : ℕ} (d : Fin n → Fin H) : ℕ := ∑ i : Fin n, (d i).1 ^ 2

/-- Pigeonhole on squared radii: some sphere in `{0, ..., H - 1}^n` has `≥ H^n / (n H²)` points. -/
lemma exists_dense_sphere (n H : ℕ) :
    ∃ R : ℕ, ((H : ℝ) ^ n / (n * (H : ℝ) ^ 2)) ≤
      ((Finset.univ.filter fun d : Fin n → Fin H ↦ sqNorm d = R).card : ℝ) := by
  by_cases hn : n = 0; · subst hn; exact ⟨0, by simp⟩
  by_cases hH : H = 0; · subst hH; exact ⟨0, by simp⟩
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hH_pos : 0 < H := Nat.pos_of_ne_zero hH
  let M : ℕ := n * H ^ 2
  have hsq_lt : ∀ d ∈ (Finset.univ : Finset (Fin n → Fin H)), sqNorm d ∈ Finset.range M := fun d _ ↦ by
    rw [Finset.mem_range]
    have hle : sqNorm d ≤ n * (H - 1) ^ 2 := calc
      sqNorm d ≤ ∑ _i : Fin n, (H - 1) ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ Nat.pow_le_pow_left (Nat.le_sub_one_of_lt (d i).2) 2
      _ = n * (H - 1) ^ 2 := by simp
    have hlt : (H - 1) ^ 2 < H ^ 2 := by have := Nat.sub_lt hH_pos zero_lt_one; nlinarith
    exact lt_of_le_of_lt hle (Nat.mul_lt_mul_of_pos_left hlt hn_pos)
  have hcard_sum : ∑ R ∈ Finset.range M,
      (Finset.univ.filter fun d : Fin n → Fin H ↦ sqNorm d = R).card = H ^ n := by
    simpa [Fintype.card_pi, Fintype.card_fin] using (Finset.card_eq_sum_card_fiberwise hsq_lt).symm
  obtain ⟨R, _, hRmax⟩ := Finset.exists_max_image (Finset.range M)
    (fun R ↦ (Finset.univ.filter fun d : Fin n → Fin H ↦ sqNorm d = R).card)
    (Finset.nonempty_range_iff.mpr (Nat.mul_pos hn_pos (pow_pos hH_pos 2)).ne')
  refine ⟨R, (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * (H : ℝ) ^ 2)).mpr ?_⟩
  have hbound : H ^ n ≤ M * (Finset.univ.filter fun d : Fin n → Fin H ↦ sqNorm d = R).card := by
    rw [← hcard_sum]; simpa using Finset.sum_le_sum fun r hr ↦ hRmax r hr
  have : ((H : ℝ) ^ n) ≤ ((n : ℝ) * (H : ℝ) ^ 2) *
      ((Finset.univ.filter fun d : Fin n → Fin H ↦ sqNorm d = R).card : ℝ) := by exact_mod_cast hbound
  linarith

/-- Weighted parallelogram identity: collinear lattice points `u, v, w` on a sphere coincide. -/
lemma sphere_no_weighted_midpoint {n : ℕ} {α α' R : ℕ} (hα : 0 < α) (hα' : 0 < α')
    {u v w : Fin n → ℕ} (hu : ∑ i, u i ^ 2 = R) (hv : ∑ i, v i ^ 2 = R) (hw : ∑ i, w i ^ 2 = R)
    (hcol : ∀ i, (α + α') * v i = α * u i + α' * w i) : u = v := by
  have hpoint : ∀ i : Fin n,
      (α : ℤ) * ((u i : ℤ) - v i) ^ 2 + (α' : ℤ) * ((w i : ℤ) - v i) ^ 2 =
      (α : ℤ) * (u i : ℤ) ^ 2 + (α' : ℤ) * (w i : ℤ) ^ 2 - ((α : ℤ) + α') * (v i : ℤ) ^ 2 := fun i ↦ by
    have hci : ((α : ℤ) + α') * (v i : ℤ) = (α : ℤ) * u i + (α' : ℤ) * w i := by exact_mod_cast hcol i
    calc (α : ℤ) * ((u i : ℤ) - v i) ^ 2 + (α' : ℤ) * ((w i : ℤ) - v i) ^ 2
        = (α : ℤ) * (u i : ℤ) ^ 2 + (α' : ℤ) * (w i : ℤ) ^ 2 -
            2 * (v i : ℤ) * ((α : ℤ) * u i + (α' : ℤ) * w i) + ((α : ℤ) + α') * (v i : ℤ) ^ 2 := by ring
      _ = (α : ℤ) * (u i : ℤ) ^ 2 + (α' : ℤ) * (w i : ℤ) ^ 2 -
            2 * (v i : ℤ) * (((α : ℤ) + α') * (v i : ℤ)) + ((α : ℤ) + α') * (v i : ℤ) ^ 2 := by rw [← hci]
      _ = _ := by ring
  have hsum_zero : ∑ i : Fin n, ((α : ℤ) * ((u i : ℤ) - v i) ^ 2 + (α' : ℤ) * ((w i : ℤ) - v i) ^ 2) = 0 := by
    simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have huZ : ∑ i : Fin n, (u i : ℤ) ^ 2 = R := by exact_mod_cast hu
    have hvZ : ∑ i : Fin n, (v i : ℤ) ^ 2 = R := by exact_mod_cast hv
    have hwZ : ∑ i : Fin n, (w i : ℤ) ^ 2 = R := by exact_mod_cast hw
    rw [huZ, hvZ, hwZ]; ring
  have heach := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ by
    have := sq_nonneg ((u i : ℤ) - v i); have := sq_nonneg ((w i : ℤ) - v i); nlinarith).mp hsum_zero
  funext i; have hi := heach i (Finset.mem_univ i)
  have hsq1 := sq_nonneg ((u i : ℤ) - v i); have hsq2 := sq_nonneg ((w i : ℤ) - v i)
  have hαZ : (0 : ℤ) < α := by exact_mod_cast hα
  have hα'Z : (0 : ℤ) < α' := by exact_mod_cast hα'
  exact_mod_cast sub_eq_zero.mp (sq_eq_zero_iff.mp (by nlinarith : ((u i : ℤ) - v i) ^ 2 = 0))

/-- **Proposition 4.7 of Paper C (`Readable.BehrendSphere.behrend_three_term_free`).** -/
theorem behrend_three_term_free {G H : Type*} [CommGroup G] [CommGroup H]
    (φ : G →* H) (c g : G) (n M L : ℕ) (hL : 0 < L) (hord : (L * M) ^ n ≤ orderOf (φ g)) :
    ∃ T : Finset G, (∀ σ ∈ T, ∃ e : ℕ, σ = c * g ^ e) ∧
      ((M : ℝ) ^ n / (n * (M : ℝ) ^ 2)) ≤ (T.card : ℝ) ∧
      ∀ i j, 0 < i → i < j → j ≤ L → ∀ σ ∈ T, ∀ τ ∈ T, ∀ ρ ∈ T,
        φ (τ / σ) ^ j = φ (ρ / σ) ^ i → φ (τ / σ) = 1 := by
  classical
  obtain ⟨R, hR⟩ := exists_dense_sphere n M
  let S : Finset (Fin n → Fin M) := Finset.univ.filter fun d ↦ sqNorm d = R
  let encode : (Fin n → Fin M) → ℕ := fun d ↦ baseEncode (L * M) (fun k ↦ (d k).1)
  have hdigit_lt : ∀ (d : Fin n → Fin M) k, (d k).1 < L * M := fun d k ↦
    lt_of_lt_of_le (d k).2 (Nat.le_mul_of_pos_left M hL)
  have hinj : Set.InjOn (fun d : Fin n → Fin M ↦ c * g ^ encode d) (S : Set (Fin n → Fin M)) := by
    intro d₁ _ d₂ _ hcg
    have hφ_eq : (φ g) ^ encode d₁ = (φ g) ^ encode d₂ := by rw [← map_pow, ← map_pow, mul_left_cancel hcg]
    have hval := baseEncode_injective (L * M) (hdigit_lt d₁) (hdigit_lt d₂)
      (pow_injOn_Iio_orderOf (lt_of_lt_of_le (baseEncode_lt_pow (L * M) _ (hdigit_lt d₁)) hord)
        (lt_of_lt_of_le (baseEncode_lt_pow (L * M) _ (hdigit_lt d₂)) hord) hφ_eq)
    exact funext fun k ↦ Fin.ext (congrFun hval k)
  refine ⟨S.image fun d ↦ c * g ^ encode d, fun σ hσ ↦ ?_,
    by rw [Finset.card_image_of_injOn hinj]; exact hR, ?_⟩
  · rcases Finset.mem_image.mp hσ with ⟨d, _, rfl⟩; exact ⟨encode d, rfl⟩
  · intro i j hi hij hjL σ hσ τ hτ ρ hρ hrel
    rcases Finset.mem_image.mp hσ with ⟨u, huS, rfl⟩
    rcases Finset.mem_image.mp hτ with ⟨v, hvS, rfl⟩
    rcases Finset.mem_image.mp hρ with ⟨w, hwS, rfl⟩
    obtain ⟨a, ha_pos, rfl⟩ : ∃ a, 0 < a ∧ j = i + a := ⟨j - i, Nat.sub_pos_of_lt hij, by omega⟩
    simp only [mul_div_mul_left_eq_div, map_div, map_pow, div_pow, div_eq_iff_eq_mul] at hrel
    have hpow_eq : (φ g) ^ baseEncode (L * M) (fun k ↦ (i + a) * (v k).1) =
        (φ g) ^ baseEncode (L * M) (fun k ↦ a * (u k).1 + i * (w k).1) := by
      have hlhs : baseEncode (L * M) (fun k ↦ (i + a) * (v k).1) = (i + a) * encode v := by
        simpa [encode] using baseEncode_linear (L * M) (i + a) 0 (fun k ↦ (v k).1) (fun _ ↦ 0)
      have hrhs : baseEncode (L * M) (fun k ↦ a * (u k).1 + i * (w k).1) = a * encode u + i * encode w := by
        simpa [encode] using baseEncode_linear (L * M) a i (fun k ↦ (u k).1) (fun k ↦ (w k).1)
      rw [hlhs, hrhs]; refine mul_right_cancel (b := (φ g) ^ (i * encode u)) ?_
      calc (φ g) ^ ((i + a) * encode v) * (φ g) ^ (i * encode u)
          = ((φ g) ^ encode v) ^ (i + a) * ((φ g) ^ encode u) ^ i := by
              rw [← pow_mul, ← pow_mul, mul_comm (encode v), mul_comm (encode u)]
        _ = ((φ g) ^ encode w) ^ i / ((φ g) ^ encode u) ^ i * ((φ g) ^ encode u) ^ i *
              ((φ g) ^ encode u) ^ (i + a) := by rw [hrel, mul_right_comm]
        _ = (φ g) ^ (i * encode w) * (φ g) ^ (a * encode u + i * encode u) := by
              rw [div_mul_cancel, ← pow_mul, ← pow_mul, mul_comm (encode w), mul_comm (encode u)]
              congr 2; ring
        _ = (φ g) ^ (a * encode u + i * encode w) * (φ g) ^ (i * encode u) := by rw [pow_add, pow_add]; ac_rfl
    have hlhs_lt : ∀ k : Fin n, (i + a) * (v k).1 < L * M := fun k ↦ by nlinarith [(v k).2]
    have hrhs_lt : ∀ k : Fin n, a * (u k).1 + i * (w k).1 < L * M := fun k ↦ by nlinarith [(u k).2, (w k).2]
    have hdigits_eq : ∀ k, (a + i) * (v k).1 = a * (u k).1 + i * (w k).1 := fun k ↦ by
      have hk := congrFun (baseEncode_injective (L * M) hlhs_lt hrhs_lt
        (pow_injOn_Iio_orderOf (lt_of_lt_of_le (baseEncode_lt_pow (L * M) _ hlhs_lt) hord)
          (lt_of_lt_of_le (baseEncode_lt_pow (L * M) _ hrhs_lt) hord) hpow_eq)) k
      linarith
    have huv := sphere_no_weighted_midpoint ha_pos hi
      (Finset.mem_filter.mp huS).2 (Finset.mem_filter.mp hvS).2 (Finset.mem_filter.mp hwS).2 hdigits_eq
    have huv' : u = v := funext fun k ↦ Fin.ext (congrFun huv k)
    subst huv'; simp

end Readable.BehrendSphere
