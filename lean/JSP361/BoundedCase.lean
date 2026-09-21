import JSP361.Defs

/-!
# JSP-000361 — bounded reciprocal-sum case

If `A ⊆ ℕ` is infinite but its reciprocal sum is bounded, then for every `k`
and every real `C` there exist `x` and `n < x` with
`C * recipSum A x ^ k < dA A n`.

Proof sketch: `recipSum A x` is nonnegative and bounded by `M' = max M 0`, so
`C * recipSum A x ^ k ≤ C * M' ^ k` (when `C > 0`).  Since `A` is infinite,
`dA` is unbounded: pick `n` with `dA A n > C * M' ^ k` and take `x = n + 1`.
For `C ≤ 0` the left side is nonpositive while `dA A a ≥ 1` for any nonzero
`a ∈ A`.
-/

namespace JSP361

open Finset
open Classical

/-- `recipSum` is a sum of nonnegative terms, hence nonnegative. -/
private theorem bnd_recipSum_nonneg (A : Set ℕ) (x : ℕ) : 0 ≤ recipSum A x := by
  unfold recipSum
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
  · exact le_refl 0

/-- For infinite `A`, `dA` is unbounded: for every real `C` there is some `n`
with `C < dA A n`.  Private copy of the unbounded component. -/
private theorem bnd_dA_unbounded (A : Set ℕ) (hA : A.Infinite) (C : ℝ) :
    ∃ n : ℕ, C < (dA A n : ℝ) := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_gt C
  have hA' : (A \ {0}).Infinite := hA.sdiff (Set.finite_singleton 0)
  obtain ⟨F, hFsub, hFcard⟩ := hA'.exists_subset_card_eq m
  refine ⟨∏ b ∈ F, b, ?_⟩
  have hne : (∏ b ∈ F, b) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro b hb
    have hmem := hFsub hb
    rw [Set.mem_sdiff, Set.mem_singleton_iff] at hmem
    exact hmem.2
  have hcard : m ≤ dA A (∏ b ∈ F, b) := by
    rw [← hFcard]
    apply Finset.card_le_card
    intro b hb
    have hmem := hFsub hb
    rw [Set.mem_sdiff, Set.mem_singleton_iff] at hmem
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨Finset.dvd_prod_of_mem (fun x => x) hb, hne⟩, hmem.1⟩
  exact lt_of_lt_of_le hm (Nat.cast_le.mpr hcard)

theorem divisor_set_limsup_of_bounded (A : Set ℕ) (hA : A.Infinite)
    (hB : ∃ M : ℝ, ∀ x : ℕ, recipSum A x ≤ M) (k : ℕ) (C : ℝ) :
    ∃ x : ℕ, ∃ n : ℕ, n < x ∧ C * recipSum A x ^ k < (dA A n : ℝ) := by
  classical
  obtain ⟨M, hM⟩ := hB
  set M' := max M 0 with hM'def
  have hbound : ∀ x : ℕ, recipSum A x ≤ M' := fun x => (hM x).trans (le_max_left M 0)
  have hnn : ∀ x : ℕ, 0 ≤ recipSum A x := fun x => bnd_recipSum_nonneg A x
  rcases le_or_gt C 0 with hC | hC
  · -- C ≤ 0: the left side is nonpositive, and `dA A a ≥ 1` for nonzero `a ∈ A`.
    obtain ⟨a, ha⟩ := (hA.sdiff (Set.finite_singleton 0)).nonempty
    rw [Set.mem_sdiff, Set.mem_singleton_iff] at ha
    refine ⟨a + 1, a, Nat.lt_succ_self a, ?_⟩
    have hdA : (0 : ℝ) < dA A a := by
      apply Nat.cast_pos.mpr
      apply Finset.card_pos.mpr
      refine ⟨a, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_divisors_self a ha.2, ha.1⟩
    have hnonpos : C * recipSum A (a + 1) ^ k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC (pow_nonneg (hnn _) k)
    exact lt_of_le_of_lt hnonpos hdA
  · -- C > 0: bound `recipSum A x ^ k ≤ M' ^ k` and use unboundedness of `dA`.
    obtain ⟨n, hn⟩ := bnd_dA_unbounded A hA (C * M' ^ k)
    refine ⟨n + 1, n, Nat.lt_succ_self n, ?_⟩
    have hpow : recipSum A (n + 1) ^ k ≤ M' ^ k :=
      pow_le_pow_left₀ (hnn _) (hbound _) k
    have hmul : C * recipSum A (n + 1) ^ k ≤ C * M' ^ k :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
    exact lt_of_le_of_lt hmul hn

end JSP361
