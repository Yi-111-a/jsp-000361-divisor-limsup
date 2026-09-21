import JSP361.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# JSP-000361 — basic lemmas about `dA` and `recipSum`.
-/

namespace JSP361

open Finset
open scoped Classical

private theorem basic_term_nonneg (A : Set ℕ) (a : ℕ) :
    0 ≤ (if a ∈ A then (1 : ℝ) / a else 0) := by
  split_ifs with ha
  · exact one_div_nonneg.mpr (Nat.cast_nonneg a)
  · exact le_rfl

theorem recipSum_nonneg (A : Set ℕ) (x : ℕ) : 0 ≤ recipSum A x := by
  show 0 ≤ ∑ a ∈ Finset.range x, if a ∈ A then (1 : ℝ) / a else 0
  exact Finset.sum_nonneg fun a _ => basic_term_nonneg A a

theorem recipSum_mono (A : Set ℕ) : Monotone (recipSum A) := by
  intro x y hxy
  show (∑ a ∈ Finset.range x, if a ∈ A then (1 : ℝ) / a else 0) ≤
    ∑ a ∈ Finset.range y, if a ∈ A then (1 : ℝ) / a else 0
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr hxy
  · intro a _ _
    exact basic_term_nonneg A a

/-- NOTE (spec issue): as literally specified,
`∀ a ∈ F, a ∈ A ∧ a ∣ n ⊢ F.card ≤ dA A n` is FALSE when `n = 0`: every `a`
satisfies `a ∣ 0`, but `dA A 0 = 0` since `Nat.divisors 0 = ∅`
(counterexample: `A = {1}`, `F = {1}`, `n = 0`). The hypothesis `hn : n ≠ 0`
is therefore added so that `a ∣ n` implies `a ∈ n.divisors`. -/
theorem card_le_dA (A : Set ℕ) {n : ℕ} {F : Finset ℕ}
    (hF : ∀ a ∈ F, a ∈ A ∧ a ∣ n) (hn : n ≠ 0) : F.card ≤ dA A n := by
  have hsub : F ⊆ n.divisors.filter (· ∈ A) := by
    intro a ha
    obtain ⟨hAa, han⟩ := hF a ha
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨han, hn⟩, hAa⟩
  exact Finset.card_le_card hsub

theorem dA_prod_ge (A : Set ℕ) {F : Finset ℕ}
    (hA : ∀ a ∈ F, a ∈ A) (h0 : 0 ∉ F) : F.card ≤ dA A (∏ a ∈ F, a) := by
  have hprod : (∏ a ∈ F, a) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro b hb hb0
    exact h0 ((show b = 0 from hb0) ▸ hb)
  have hsub : F ⊆ (∏ a ∈ F, a).divisors.filter (· ∈ A) := by
    intro a ha
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨Finset.dvd_prod_of_mem (fun x ↦ x) ha, hprod⟩, hA a ha⟩
  exact Finset.card_le_card hsub

theorem one_le_dA (A : Set ℕ) {a : ℕ} (ha : a ∈ A) (ha0 : a ≠ 0) : 1 ≤ dA A a := by
  have ha' : a ∈ a.divisors.filter (· ∈ A) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors_self a ha0, ha⟩
  exact Finset.one_le_card.mpr ⟨a, ha'⟩

end JSP361
