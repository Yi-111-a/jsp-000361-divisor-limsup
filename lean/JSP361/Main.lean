import Mathlib
import JSP361.Defs

/-!
# JSP-000361 — ErSa80 generalized divisor limsup
-/

namespace JSP361

open Filter Finset

/-- `d_A(n)` = number of elements of `A` dividing `n`. -/
noncomputable def dA (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.card {a : ℕ // a ∈ A ∧ a ≠ 0 ∧ a ∣ n}

/-- Reciprocal sum of elements of `A` strictly below `x`. -/
noncomputable def recipSum (A : Set ℕ) (x : ℕ) : ℝ :=
  ∑ a ∈ Finset.range x, if a ∈ A ∧ 0 < a then (1 : ℝ) / a else 0

/-- ErSa80: for every infinite A and every k, limsup of max d_A / (recipSum)^k is ∞. -/
theorem divisor_set_limsup :
    ∀ (A : Set ℕ), A.Infinite → ∀ (k : ℕ) (C : ℝ),
      ∃ x : ℕ, ∃ n < x, (dA A n : ℝ) > C * (recipSum A x) ^ k := by
  sorry

end JSP361
