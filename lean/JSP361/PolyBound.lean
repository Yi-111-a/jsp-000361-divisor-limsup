import JSP361.LcmWin
import JSP361.RoughElem
import JSP361.ChebBound
import JSP361.Basic

/-!
# JSP-000361 — polynomial bounds from the global `hcon` hypothesis

If `dA A n ≤ C * recipSum A x ^ k` holds for every `n < x`, then
`countA A (t + 1)` (and the `s`-powSmooth count) is bounded by
`C * (2 + (log 4 + 4) * t) ^ k`, via `Nat.lcmUpto t` and the Chebyshev
bound on `recipSum` above `lcmUpto t`.
-/

namespace JSP361

open Finset
open scoped Classical

theorem countA_poly_of_hcon (A : Set ℕ) {k : ℕ} {C : ℝ} (hC : 0 < C)
    (hcon : ∀ x n : ℕ, n < x → (dA A n : ℝ) ≤ C * recipSum A x ^ k) (t : ℕ) :
    (countA A (t + 1) : ℝ) ≤ C * (2 + (Real.log 4 + 4) * t) ^ k :=
  calc (countA A (t + 1) : ℝ)
      ≤ (dA A (Nat.lcmUpto t) : ℝ) :=
        Nat.cast_le.mpr (countA_le_dA_lcmUpto A t)
    _ ≤ C * recipSum A (Nat.lcmUpto t + 1) ^ k :=
        hcon _ _ (Nat.lt_succ_self _)
    _ ≤ C * (2 + (Real.log 4 + 4) * t) ^ k :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (recipSum_nonneg A _) (recipSum_lcmUpto_le A t) k)
          hC.le

theorem powSmooth_poly_of_hcon (A : Set ℕ) {k : ℕ} {C : ℝ} (hC : 0 < C)
    (hcon : ∀ x n : ℕ, n < x → (dA A n : ℝ) ≤ C * recipSum A x ^ k) (s y : ℕ) :
    (((Finset.range y).filter (fun a ↦ a ∈ A \ {0} ∧
        ∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e → p ^ e ∣ a → p ^ e ≤ s)).card : ℝ)
      ≤ C * (2 + (Real.log 4 + 4) * s) ^ k :=
  calc (((Finset.range y).filter (fun a ↦ a ∈ A \ {0} ∧
          ∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e → p ^ e ∣ a → p ^ e ≤ s)).card : ℝ)
      ≤ (dA A (Nat.lcmUpto s) : ℝ) :=
        Nat.cast_le.mpr (countA_powSmooth_le A s y)
    _ ≤ C * recipSum A (Nat.lcmUpto s + 1) ^ k :=
        hcon _ _ (Nat.lt_succ_self _)
    _ ≤ C * (2 + (Real.log 4 + 4) * s) ^ k :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (recipSum_nonneg A _) (recipSum_lcmUpto_le A s) k)
          hC.le

end JSP361
