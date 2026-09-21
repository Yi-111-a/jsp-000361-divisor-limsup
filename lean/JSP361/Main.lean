import JSP361.Defs
import JSP361.Basic
import JSP361.Unbounded
import JSP361.BoundedCase
import JSP361.Average
import JSP361.Divergent

/-!
# JSP-000361 — Erdős–Sárközy (ErSa80) generalized divisor limsup

For every infinite `A ⊆ ℕ` and every `k`,
`limsup_{x→∞} (max_{n<x} d_A(n)) / (∑_{a ∈ A ∩ [1,x)} 1/a)^k = ∞`.

For a nonnegative `ℕ`-indexed sequence, `limsup = ∞` iff it is unbounded,
i.e. `∀ C, ∃ x ∃ n < x, dA A n > C * recipSum A x ^ k` — the form proved here.

Proof split:
- `divisor_set_limsup_of_bounded` — convergent-reciprocal-sum case (proved).
- `divisor_set_limsup_divergent` — divergent case, the ErSa80 core.
-/

namespace JSP361

open Finset

/-- **JSP-000361 (ErSa80).** For every infinite `A ⊆ ℕ` and every `k`,
the ratio `max_{n<x} d_A(n) / recipSum A x ^ k` is unbounded in `x`,
equivalently `limsup = ∞`. -/
theorem divisor_set_limsup (A : Set ℕ) (hA : A.Infinite) (k : ℕ) (C : ℝ) :
    ∃ x : ℕ, ∃ n : ℕ, n < x ∧ C * recipSum A x ^ k < (dA A n : ℝ) := by
  by_cases hB : ∃ M : ℝ, ∀ x : ℕ, recipSum A x ≤ M
  · exact divisor_set_limsup_of_bounded A hA hB k C
  · push_neg at hB
    exact divisor_set_limsup_divergent A hA hB k C

end JSP361
