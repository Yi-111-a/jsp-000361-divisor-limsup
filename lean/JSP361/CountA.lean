import JSP361.Counting
import Mathlib.Data.Nat.Count

/-!
# JSP-000361 — counting function `countA`

`countA A x` = number of positive elements of `A` strictly below `x`
(the `N_A(x)` of Erdős–Sárközy).  Defined via `Nat.count` so that the
Galois connection `Nat.gc_count_nth` with `Nat.nth` applies.

**Interface contract:** `countA` is a FIXED signature used by
`Density.lean`, `ThmTwo.lean`, `RoughLcm.lean`, `PrimeCount.lean`.
Do not restate it; add lemmas in your own file.
-/

namespace JSP361

open Finset
open Classical

/-- `N_A(x)` = `#{a ∈ A \ {0} : a < x}` via `Nat.count`. -/
noncomputable def countA (A : Set ℕ) (x : ℕ) : ℕ :=
  Nat.count (· ∈ A \ {0}) x

theorem countA_eq_card (A : Set ℕ) (x : ℕ) :
    countA A x = ((Finset.range x).filter (· ∈ A \ {0})).card :=
  Nat.count_eq_card_filter_range _ x

theorem countA_le (A : Set ℕ) (x : ℕ) : countA A x ≤ x := by
  rw [countA_eq_card]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range x)

theorem countA_zero (A : Set ℕ) : countA A 0 = 0 := by
  rw [countA_eq_card]
  simp

theorem countA_mono (A : Set ℕ) : Monotone (countA A) := by
  intro x y hxy
  rw [countA_eq_card, countA_eq_card]
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter] at ha ⊢
  exact ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ha.1) hxy), ha.2⟩

theorem countA_pos_iff (A : Set ℕ) (x : ℕ) :
    0 < countA A x ↔ ∃ a, a < x ∧ a ∈ A ∧ a ≠ 0 := by
  rw [countA_eq_card, Finset.card_pos]
  constructor
  · rintro ⟨a, ha⟩
    rw [Finset.mem_filter] at ha
    exact ⟨a, Finset.mem_range.mp ha.1, ha.2.1,
      fun h0 => ha.2.2 (Set.mem_singleton_iff.mpr h0)⟩
  · rintro ⟨a, hax, haA, ha0⟩
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hax, ?_⟩⟩
    exact ⟨haA, fun hs => ha0 (Set.mem_singleton_iff.mp hs)⟩

/-- Elements counted by `countA` are positive. -/
theorem mem_of_mem_countA {A : Set ℕ} {a x : ℕ}
    (ha : a ∈ (Finset.range x).filter (· ∈ A \ {0})) :
    a < x ∧ a ∈ A ∧ a ≠ 0 := by
  rw [Finset.mem_filter] at ha
  exact ⟨Finset.mem_range.mp ha.1, ha.2.1,
    fun h0 => ha.2.2 (Set.mem_singleton_iff.mpr h0)⟩

end JSP361
