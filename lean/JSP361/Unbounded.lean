import JSP361.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.NumberTheory.Divisors

/-!
# JSP-000361 — `dA` is unbounded for infinite `A`

For an infinite `A ⊆ ℕ` and any real `C`, there is `n` with `C < dA A n`:
take `m` elements of `A \ {0}` with `C < m` and let `n` be their product.
Each of the `m` elements is a nonzero element of `A` dividing `n`.
-/

namespace JSP361

open Finset
open Classical

/-- For an infinite `A`, `dA A ·` takes arbitrarily large finite values:
for every `m : ℕ` there is `n` with `m ≤ dA A n`. -/
private theorem unb_card_le_dA (A : Set ℕ) (hA : A.Infinite) (m : ℕ) :
    ∃ n : ℕ, m ≤ dA A n := by
  obtain ⟨F, hFsub, hFcard⟩ :=
    (hA.sdiff (Set.finite_singleton 0)).exists_subset_card_eq m
  refine ⟨F.prod fun a ↦ a, ?_⟩
  have hn0 : (F.prod fun a ↦ a) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro a ha
    -- `a ∈ A \ {0}`, so `a ≠ 0`
    simpa using (hFsub ha).2
  have key : F.card ≤ dA A (F.prod fun a ↦ a) := by
    apply Finset.card_le_card
    intro b hb
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨Finset.dvd_prod_of_mem (fun a ↦ a) hb, hn0⟩,
        (hFsub hb).1⟩
  rwa [hFcard] at key

theorem dA_unbounded (A : Set ℕ) (hA : A.Infinite) (C : ℝ) :
    ∃ n : ℕ, C < (dA A n : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt C
  obtain ⟨n, hn⟩ := unb_card_le_dA A hA m
  exact ⟨n, lt_of_lt_of_le hm (Nat.cast_le.mpr hn)⟩

theorem dA_unbounded' (A : Set ℕ) (hA : A.Infinite) (C : ℝ) :
    ∃ n x : ℕ, n < x ∧ C < (dA A n : ℝ) := by
  obtain ⟨n, hn⟩ := dA_unbounded A hA C
  exact ⟨n, n + 1, Nat.lt_succ_self n, hn⟩

end JSP361
