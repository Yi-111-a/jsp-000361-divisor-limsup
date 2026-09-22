import JSP361.Basic
import JSP361.CountA
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Finset.Card

/-!
# JSP-000361 — the lcm-window win condition

Every positive `a ∈ A` with `a ≤ t` divides `Nat.lcmUpto t`, so
`countA A (t + 1) ≤ dA A (Nat.lcmUpto t)`.  Hence a single large `t`
where `countA A (t + 1)` beats `C * recipSum A (lcmUpto t + 1)^k`
already produces a pair `n < x` witnessing the goal.
-/

namespace JSP361

open Finset
open scoped Classical

/-- Every positive `a ∈ A` with `a ≤ t` divides `Nat.lcmUpto t`, so
`countA A (t + 1) ≤ dA A (Nat.lcmUpto t)`. -/
theorem countA_le_dA_lcmUpto (A : Set ℕ) (t : ℕ) :
    countA A (t + 1) ≤ dA A (Nat.lcmUpto t) := by
  rw [countA_eq_card]
  apply card_le_dA A _ (Nat.lcmUpto_ne_zero t)
  intro a ha
  rw [Finset.mem_filter] at ha
  have hax : a ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha.1)
  have ha0 : a ≠ 0 := fun h0 => ha.2.2 (Set.mem_singleton_iff.mpr h0)
  refine ⟨ha.2.1, ?_⟩
  have hmem : a ∈ Finset.Icc 1 t :=
    Finset.mem_Icc.mpr ⟨Nat.pos_iff_ne_zero.mpr ha0, hax⟩
  exact Finset.dvd_lcm hmem

/-- The lcm-window win condition: if for arbitrarily large `t` the count of
`A`-elements below `t` exceeds `C * recipSum A (lcmUpto t + 1)^k`, then the
JSP-000361 goal holds. -/
theorem divisor_limsup_of_lcm_win (A : Set ℕ) (k : ℕ) (C : ℝ)
    (hwin : ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧
      C * recipSum A (Nat.lcmUpto t + 1) ^ k < (countA A (t + 1) : ℝ)) :
    ∃ x : ℕ, ∃ n : ℕ, n < x ∧ C * recipSum A x ^ k < (dA A n : ℝ) := by
  obtain ⟨t, -, hwin'⟩ := hwin 0
  refine ⟨Nat.lcmUpto t + 1, Nat.lcmUpto t, Nat.lt_succ_self _, ?_⟩
  exact lt_of_lt_of_le hwin' (Nat.cast_le.mpr (countA_le_dA_lcmUpto A t))

end JSP361
