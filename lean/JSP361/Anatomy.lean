import JSP361.Defs
import JSP361.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# JSP-000361 — elementary counting anatomy

Counting infrastructure for the Erdős–Sárközy product construction.

* `omegaG y n` / `omegaI y z n`: counts of distinct prime factors of `n`
  above `y` / inside `(y, z]`.
* `card_le_of_sq_dvd`: at most `x · ∑_{j=J+1}^{x} j⁻² ≤ x / J` of the
  nonzero `n ≤ x` are divisible by the square of some `j > J`.
* `exists_dA_ge_of_repr`: a factorisation `n = (∏_{a ∈ s} a) · m` with all
  `a ∈ A` gives `s.card ≤ dA A n`.
* `card_tuples_dvd`: the type of `k`-tuples of elements of `A` dividing
  `n` has cardinality `(dA A n)^k`.
* `primeFactors_prod_card_le`: `ω(∏_{a ∈ s} a) ≤ ∑_{a ∈ s} ω(a)`.
-/

namespace JSP361

open Finset
open Classical

/-- `omegaG y n` = number of DISTINCT prime factors of `n` that are `> y`. -/
def omegaG (y n : ℕ) : ℕ := (n.primeFactors.filter (y < ·)).card

/-- `omegaI y z n` = number of DISTINCT prime factors of `n` in `(y, z]`. -/
def omegaI (y z n : ℕ) : ℕ := (n.primeFactors.filter (fun p ↦ y < p ∧ p ≤ z)).card

/-- Every prime factor of `n` is `≤ n`, so `(y, n]` captures all large
prime factors. -/
theorem omegaG_eq_omegaI (y n : ℕ) : omegaG y n = omegaI y n n := by
  unfold omegaG omegaI
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · congr 1
    apply Finset.filter_congr
    intro p hp
    exact and_iff_left (Nat.le_of_mem_primeFactors hp)

/-- Counting over a smaller range only makes the count smaller. -/
theorem omegaI_le_omegaG (y z n : ℕ) : omegaI y z n ≤ omegaG y n := by
  unfold omegaI omegaG
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- Monotonicity of `omegaI` in the upper endpoint. -/
theorem omegaI_mono_right {y n : ℕ} {z z' : ℕ} (hzz : z ≤ z') :
    omegaI y z n ≤ omegaI y z' n := by
  unfold omegaI
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hp.2.2.trans hzz⟩

/-- `omegaG` counts a subset of all prime factors. -/
theorem omegaG_le_primeFactors_card (y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    omegaG y n ≤ n.primeFactors.card := by
  unfold omegaG
  exact Finset.card_filter_le _ _

/-- Prime factors of a product lie in the union of the prime factors. -/
theorem omegaG_mul_le (y : ℕ) {a b : ℕ} :
    omegaG y (a * b) ≤ omegaG y a + omegaG y b := by
  unfold omegaG
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  rw [Nat.primeFactors_mul ha hb, Finset.filter_union]
  exact Finset.card_union_le _ _

/-- The `j² ∣ n` counting bound: the number of nonzero `n ≤ x` divisible
by the square of some `j > J` is at most `x · ∑_{j=J+1}^{x} 1/j²`. -/
theorem card_le_of_sq_dvd (x J : ℕ) :
    (((Finset.range (x + 1)).filter
      (fun n ↦ n ≠ 0 ∧ ∃ j : ℕ, J < j ∧ j ^ 2 ∣ n)).card : ℝ)
      ≤ x * ∑ j ∈ Finset.Icc (J + 1) x, (1 : ℝ) / j ^ 2 := by
  -- The filtered set is covered by the multiples of `j²` for `J < j ≤ x`.
  have hsub : (Finset.range (x + 1)).filter
        (fun n ↦ n ≠ 0 ∧ ∃ j : ℕ, J < j ∧ j ^ 2 ∣ n)
      ⊆ (Finset.Icc (J + 1) x).biUnion
        (fun j ↦ (Finset.range (x + 1)).filter (fun n ↦ n ≠ 0 ∧ j ^ 2 ∣ n)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnx, hn0, j, hjJ, hjdvd⟩ := hn
    rw [Finset.mem_range] at hnx
    have hj2 : j ^ 2 ≠ 0 := by
      intro h0
      rw [h0] at hjdvd
      exact hn0 (zero_dvd_iff.mp hjdvd)
    have hj0 : j ≠ 0 := by
      rintro rfl
      simp at hj2
    have hjj : j ≤ j ^ 2 := le_self_pow₀ (Nat.one_le_iff_ne_zero.mpr hj0) two_ne_zero
    have hjx : j ≤ x := by
      have hle : j ^ 2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hjdvd
      omega
    rw [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_Icc.mpr ⟨hjJ, hjx⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnx, hn0, hjdvd⟩⟩
  -- Each `j`-slice consists of the `x / j²` multiples of `j²` below `x + 1`.
  have hcard : ∀ j : ℕ,
      ((Finset.range (x + 1)).filter (fun n ↦ n ≠ 0 ∧ j ^ 2 ∣ n)).card = x / j ^ 2 :=
    fun j ↦ Nat.card_multiples' x (j ^ 2)
  calc (((Finset.range (x + 1)).filter
        (fun n ↦ n ≠ 0 ∧ ∃ j : ℕ, J < j ∧ j ^ 2 ∣ n)).card : ℝ)
      ≤ (((Finset.Icc (J + 1) x).biUnion
        (fun j ↦ (Finset.range (x + 1)).filter (fun n ↦ n ≠ 0 ∧ j ^ 2 ∣ n))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (∑ j ∈ Finset.Icc (J + 1) x,
        ((Finset.range (x + 1)).filter (fun n ↦ n ≠ 0 ∧ j ^ 2 ∣ n)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.Icc (J + 1) x, ((x / j ^ 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [hcard j]
    _ ≤ ∑ j ∈ Finset.Icc (J + 1) x, (x : ℝ) / j ^ 2 :=
        Finset.sum_le_sum fun j _ ↦ Nat.cast_div_le
    _ = x * ∑ j ∈ Finset.Icc (J + 1) x, (1 : ℝ) / j ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ (mul_one_div _ _).symm

/-- Telescoping bound `∑_{j=J+1}^{x} j⁻² ≤ J⁻¹` for `J ≥ 1`, via
`1/j² ≤ 1/(j-1) - 1/j`. -/
theorem sum_Icc_inv_sq_le (J x : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.Icc (J + 1) x, (1 : ℝ) / j ^ 2 ≤ (J : ℝ)⁻¹ := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show x + 1 - (J + 1) = x - J from by omega]
  calc ∑ k ∈ Finset.range (x - J), (1 : ℝ) / (J + 1 + k : ℕ) ^ 2
      ≤ ∑ k ∈ Finset.range (x - J),
        (((J + k : ℕ) : ℝ)⁻¹ - ((J + (k + 1) : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro k _
        have hJ' : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
        have hm : (0 : ℝ) < (J : ℝ) + (k : ℝ) :=
          add_pos_of_pos_of_nonneg hJ' (Nat.cast_nonneg _)
        have hcast : ((J + 1 + k : ℕ) : ℝ) = (J : ℝ) + (k : ℝ) + 1 := by
          push_cast; ring
        have hcast2 : ((J + k : ℕ) : ℝ) = (J : ℝ) + (k : ℝ) := by
          push_cast; ring
        have hcast3 : ((J + (k + 1) : ℕ) : ℝ) = (J : ℝ) + (k : ℝ) + 1 := by
          push_cast; ring
        rw [hcast, hcast2, hcast3]
        set m := (J : ℝ) + (k : ℝ) with hm_def
        have hm0 : m ≠ 0 := ne_of_gt hm
        have hm1 : m + 1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < m + 1)
        have hstep : (m : ℝ)⁻¹ - (m + 1)⁻¹ = (m * (m + 1))⁻¹ := by
          field_simp
          ring
        rw [hstep, one_div]
        have hle : m * (m + 1) ≤ (m + 1) ^ 2 := by nlinarith
        exact one_div_le_one_div_of_le (mul_pos hm (by linarith)) hle
    _ = ((J : ℝ))⁻¹ - ((J + (x - J) : ℕ) : ℝ)⁻¹ := by
        rw [Finset.sum_range_sub']
        simp
    _ ≤ (J : ℝ)⁻¹ := by
        have hnn : 0 ≤ ((J + (x - J) : ℕ) : ℝ)⁻¹ :=
          inv_nonneg.mpr (Nat.cast_nonneg _)
        linarith

/-- Closed form of `card_le_of_sq_dvd`: the count is at most `x / J`. -/
theorem card_le_of_sq_dvd' (x J : ℕ) (hJ : 1 ≤ J) :
    (((Finset.range (x + 1)).filter
      (fun n ↦ n ≠ 0 ∧ ∃ j : ℕ, J < j ∧ j ^ 2 ∣ n)).card : ℝ) ≤ x / J := by
  calc (((Finset.range (x + 1)).filter
        (fun n ↦ n ≠ 0 ∧ ∃ j : ℕ, J < j ∧ j ^ 2 ∣ n)).card : ℝ)
      ≤ x * ∑ j ∈ Finset.Icc (J + 1) x, (1 : ℝ) / j ^ 2 := card_le_of_sq_dvd x J
    _ ≤ x * (J : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le J x hJ) (Nat.cast_nonneg _)
    _ = x / J := by rw [div_eq_mul_inv]

/-- A factorisation `n = (∏_{a ∈ s} a) · m` with all `a ∈ A` nonzero and
`m ≠ 0` gives `s.card ≤ dA A n`: each `a ∈ s` is an element of `A`
dividing `n`. -/
theorem exists_dA_ge_of_repr (A : Set ℕ) {s : Finset ℕ} {m n : ℕ}
    (hFA : ∀ a ∈ s, a ∈ A) (h0 : ∀ a ∈ s, a ≠ 0)
    (hn : n = (∏ a ∈ s, a) * m) (hm : m ≠ 0) : s.card ≤ dA A n := by
  apply card_le_dA
  · intro a ha
    exact ⟨hFA a ha,
      (Finset.dvd_prod_of_mem (fun x ↦ x) ha).trans (dvd_mul_right _ m)⟩
  · rw [hn]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr h0) hm

/-- The type of `k`-tuples of elements of `A` dividing `n` has cardinality
exactly `(dA A n)^k`. -/
theorem card_tuples_dvd (A : Set ℕ) (n k : ℕ) :
    Fintype.card (Fin k → (n.divisors.filter (· ∈ A))) = dA A n ^ k := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  rfl

/-- The injective `k`-tuples (ordered distinct `k`-tuples of elements of
`A` dividing `n`) number at most `(dA A n)^k`. -/
theorem card_injective_tuples_dvd_le (A : Set ℕ) (n k : ℕ) :
    Fintype.card {f : Fin k → (n.divisors.filter (· ∈ A)) // Function.Injective f}
      ≤ dA A n ^ k := by
  rw [← card_tuples_dvd]
  exact Fintype.card_subtype_le _

/-- Prime factors of a product over a finset of nonzero naturals lie in
the union of the individual prime factor sets. -/
theorem primeFactors_prod_subset_biUnion {s : Finset ℕ} (hs : ∀ a ∈ s, a ≠ 0) :
    (∏ a ∈ s, a).primeFactors ⊆ s.biUnion (·.primeFactors) := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpP, hpdvd, _⟩ := hp
  obtain ⟨a, ha, hpa⟩ := (hpP.prime.dvd_finsetProd_iff id).mp hpdvd
  rw [Finset.mem_biUnion]
  exact ⟨a, ha, hpP.mem_primeFactors hpa (hs a ha)⟩

/-- `ω(∏_{a ∈ s} a) ≤ ∑_{a ∈ s} ω(a)`. -/
theorem primeFactors_prod_card_le {s : Finset ℕ} (hs : ∀ a ∈ s, a ≠ 0) :
    (∏ a ∈ s, a).primeFactors.card ≤ ∑ a ∈ s, a.primeFactors.card :=
  (Finset.card_le_card (primeFactors_prod_subset_biUnion hs)).trans
    Finset.card_biUnion_le

end JSP361
