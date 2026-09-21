import JSP361.Counting
import Mathlib

open Finset
open Classical

namespace JSP361

-- name checks
example (f : ℕ → ℝ) {m n : ℕ} (h : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (f (i + 1) - f i) = f n - f m :=
  Finset.sum_Ico_eq_sub f h

example (f : ℕ → ℝ) {m n : ℕ} (h : m ≤ n) :
    ∑ i ∈ Finset.range m, f i + ∑ i ∈ Finset.Ico m n, f i = ∑ i ∈ Finset.range n, f i :=
  Finset.sum_range_add_sum_Ico f h

example : True := by trivial

end JSP361
