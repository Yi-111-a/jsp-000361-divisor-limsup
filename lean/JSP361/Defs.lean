import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Monotonicity
import Mathlib.Tactic.Says
import Mathlib.Tactic.Subsingleton
import Mathlib.Tactic.Relation.Symm
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Use

/-!
# JSP-000361 definitions

`dA A n` = number of elements of `A` dividing `n`.
`recipSum A x` = `∑_{a ∈ A, 0 < a < x} 1/a`.

Note: `if a ∈ A then …` in a *statement* needs `open Classical` (or
`Classical.decPred`) at the top of YOUR file; inside proofs use `classical`.
If a tactic or lemma is missing, add the `import Mathlib.*` to YOUR OWN file.
-/

namespace JSP361

open Finset

/-- `d_A(n)` = number of elements of `A` that divide `n`.
Defined via `Nat.divisors`, so `dA A 0 = 0` and for `n ≠ 0` it counts
`{a ∈ A : a ∣ n}` (such `a` are automatically nonzero). -/
noncomputable def dA (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred (· ∈ A)
  (n.divisors.filter (· ∈ A)).card

/-- Reciprocal sum of positive elements of `A` strictly below `x`. -/
noncomputable def recipSum (A : Set ℕ) (x : ℕ) : ℝ :=
  letI := Classical.decPred (· ∈ A)
  ∑ a ∈ Finset.range x, if a ∈ A then (1 : ℝ) / a else 0

end JSP361
