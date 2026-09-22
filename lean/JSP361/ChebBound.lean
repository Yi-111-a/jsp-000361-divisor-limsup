import JSP361.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# JSP-000361 — Chebyshev-type bounds for `recipSum` above `lcmUpto t`.

Self-contained: the two auxiliary private lemmas below reproduce the
harmonic bound `recipSum A x ≤ 1 + log x` so this file does not need any
project imports beyond `JSP361.Basic`.
-/

namespace JSP361

open Finset
open scoped Classical

/-- `recipSum A x` equals the sum over positive elements of `A` below `x`
(the `a = 0` term vanishes since `1/0 = 0` in `ℝ`). -/
private theorem recipSum_eq_sum_filter_aux (A : Set ℕ) (x : ℕ) :
    recipSum A x = ∑ a ∈ (Finset.range x).filter (· ∈ A \ {0}), (1 : ℝ) / a := by
  classical
  show (∑ a ∈ Finset.range x, if a ∈ A then (1 : ℝ) / a else 0) = _
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h0 : a = 0
  · subst h0
    simp [Set.mem_sdiff]
  · by_cases ha : a ∈ A <;> simp [h0, ha, Set.mem_sdiff]

/-- Universal harmonic bound: `recipSum A x ≤ 1 + log x`. -/
private theorem recipSum_le_log_aux (A : Set ℕ) (x : ℕ) :
    recipSum A x ≤ 1 + Real.log x := by
  classical
  have hlog : Real.log ↑(x - 1) ≤ Real.log (x : ℝ) := by
    cases x with
    | zero => simp
    | succ m =>
      cases m with
      | zero => simp
      | succ n =>
        exact Real.log_le_log
          (by exact_mod_cast (by omega : 0 < n + 2 - 1))
          (by exact_mod_cast Nat.sub_le _ _)
  have hset : (Finset.range x).filter (· ≠ 0) = Finset.Icc 1 (x - 1) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hsub : (Finset.range x).filter (· ∈ A \ {0}) ⊆
      (Finset.range x).filter (· ≠ 0) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, fun h0 => ha.2.2 (Set.mem_singleton_iff.mpr h0)⟩
  have hsum : ∑ a ∈ (Finset.range x).filter (· ≠ 0), (1 : ℝ) / a =
      (harmonic (x - 1) : ℝ) := by
    rw [hset, harmonic_eq_sum_Icc, Rat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rat.cast_inv, Rat.cast_natCast, one_div]
  calc recipSum A x = ∑ a ∈ (Finset.range x).filter (· ∈ A \ {0}), (1 : ℝ) / a :=
        recipSum_eq_sum_filter_aux A x
    _ ≤ ∑ a ∈ (Finset.range x).filter (· ≠ 0), (1 : ℝ) / a :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)
    _ = (harmonic (x - 1) : ℝ) := hsum
    _ ≤ 1 + Real.log ↑(x - 1) := harmonic_le_one_add_log (x - 1)
    _ ≤ 1 + Real.log ↑x := add_le_add_left hlog 1

/-- `Nat.lcmUpto t ≤ exp((log 4 + 4) · t)` via Chebyshev's `ψ` bound. -/
theorem lcmUpto_le_exp (t : ℕ) :
    (Nat.lcmUpto t : ℝ) ≤ Real.exp ((Real.log 4 + 4) * t) := by
  have hpsi : Real.log (Nat.lcmUpto t : ℝ) ≤ (Real.log 4 + 4) * t := by
    have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg t)
    rwa [Chebyshev.psi_eq_log_lcmUpto t] at h
  calc (Nat.lcmUpto t : ℝ)
      = Real.exp (Real.log (Nat.lcmUpto t : ℝ)) := by
        rw [Real.exp_log (by exact_mod_cast Nat.lcmUpto_pos t)]
    _ ≤ Real.exp ((Real.log 4 + 4) * t) := Real.exp_le_exp.mpr hpsi

/-- `recipSum` evaluated just above `lcmUpto t` is dominated by `recipSum`
just above `⌈exp((log4+4)·t)⌉`. -/
theorem recipSum_lcmUpto_le_exp (A : Set ℕ) (t : ℕ) :
    recipSum A (Nat.lcmUpto t + 1) ≤
      recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) := by
  apply recipSum_mono
  have h : (Nat.lcmUpto t : ℝ) ≤ (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ : ℝ) :=
    (lcmUpto_le_exp t).trans (Nat.le_ceil _)
  exact Nat.succ_le_succ (Nat.cast_le.mp h)

/-- Crude corollary: `recipSum` above `lcmUpto t` is `≤ 2 + (log4+4)·t`. -/
theorem recipSum_lcmUpto_le (A : Set ℕ) (t : ℕ) :
    recipSum A (Nat.lcmUpto t + 1) ≤ 2 + (Real.log 4 + 4) * t := by
  have hLpos : (0:ℝ) < Nat.lcmUpto t := by exact_mod_cast Nat.lcmUpto_pos t
  have hpsi : Real.log (Nat.lcmUpto t : ℝ) ≤ (Real.log 4 + 4) * t := by
    have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg t)
    rwa [Chebyshev.psi_eq_log_lcmUpto t] at h
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hstep : Real.log ((Nat.lcmUpto t : ℝ) + 1) ≤
      Real.log (2 * (Nat.lcmUpto t : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hmul : Real.log (2 * (Nat.lcmUpto t : ℝ)) =
      Real.log 2 + Real.log (Nat.lcmUpto t : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hLpos)
  have h := recipSum_le_log_aux A (Nat.lcmUpto t + 1)
  push_cast at h
  linarith

end JSP361
