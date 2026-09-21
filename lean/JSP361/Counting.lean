import JSP361.Defs
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Count
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Image

/-!
# JSP-000361 — enumeration/counting bridge for `A ⊆ ℕ`

`nthA A i` = the `i`-th positive element of `A` (elements of `A \ {0}` in
increasing order).  These lemmas connect `recipSum` to the sequence
`1 / nthA A i` and give the universal harmonic bound
`recipSum A x ≤ 1 + log x`.

**Interface contract:** the signatures below are FIXED — other files
(`SmallF.lean`, `Divergent.lean`) code against them.  Do not rename or
restate; only replace `sorry` proofs.
-/

namespace JSP361

open Finset
open Classical

/-- The `i`-th element of `A \ {0}` in increasing order. -/
noncomputable def nthA (A : Set ℕ) (i : ℕ) : ℕ :=
  Nat.nth (· ∈ A \ {0}) i

theorem nthA_mem (hA : (A \ {0}).Infinite) (i : ℕ) :
    nthA A i ∈ A ∧ nthA A i ≠ 0 := by
  have h : nthA A i ∈ A \ {0} :=
    Nat.nth_mem_of_infinite (p := (· ∈ A \ {0})) hA i
  exact ⟨h.1, fun h0 => h.2 (Set.mem_singleton_iff.mpr h0)⟩

theorem nthA_strictMono (hA : (A \ {0}).Infinite) : StrictMono (nthA A) :=
  Nat.nth_strictMono (p := (· ∈ A \ {0})) hA

theorem nthA_pos (hA : (A \ {0}).Infinite) (i : ℕ) : 0 < nthA A i :=
  Nat.pos_of_ne_zero (nthA_mem hA i).2

/-- The `i`-th positive element of `A` is at least `i + 1`. -/
theorem nthA_ge (hA : (A \ {0}).Infinite) (i : ℕ) : i + 1 ≤ nthA A i := by
  have hmono := nthA_strictMono hA
  have h0 : 1 ≤ nthA A 0 := nthA_pos hA 0
  induction i with
  | zero => exact h0
  | succ k ih =>
    have hlt : nthA A k < nthA A (k + 1) := hmono (Nat.lt_succ_self k)
    omega

/-- Every positive element of `A` appears in the enumeration. -/
theorem nthA_surj (hA : (A \ {0}).Infinite) {a : ℕ} (ha : a ∈ A \ {0}) :
    ∃ i, nthA A i = a := by
  have h : a ∈ Set.range (nthA A) :=
    Nat.subset_range_nth (p := (· ∈ A \ {0})) (show a ∈ Set.ofPred (· ∈ A \ {0}) from ha)
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi⟩

/-- `recipSum A x` equals the sum over positive elements of `A` below `x`
(the `a = 0` term vanishes since `1/0 = 0` in `ℝ`). -/
theorem recipSum_eq_sum_filter (A : Set ℕ) (x : ℕ) :
    recipSum A x = ∑ a ∈ (Finset.range x).filter (· ∈ A \ {0}), (1 : ℝ) / a := by
  classical
  show (∑ a ∈ Finset.range x, if a ∈ A then (1 : ℝ) / a else 0) = _
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h0 : a = 0
  · subst h0
    simp [Set.mem_sdiff]
  · by_cases ha : a ∈ A <;> simp [h0, ha, Set.mem_sdiff]

/-- The elements of `A \ {0}` below `x` are among `nthA A i` for `i < x`,
hence the reciprocal sum is dominated by the first `x` terms. -/
theorem recipSum_le_sum_nthA (hA : (A \ {0}).Infinite) (x : ℕ) :
    recipSum A x ≤ ∑ i ∈ Finset.range x, (1 : ℝ) / nthA A i := by
  classical
  rw [recipSum_eq_sum_filter]
  have hsub : (Finset.range x).filter (· ∈ A \ {0}) ⊆ (Finset.range x).image (nthA A) := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨hax, haA⟩ := ha
    obtain ⟨i, hi⟩ := nthA_surj hA haA
    have hix : i < x := by
      have hge := nthA_ge hA i
      omega
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hix, hi⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_).trans_eq ?_
  · intro a _ _
    positivity
  · rw [Finset.sum_image (fun i _ j _ hij => (nthA_strictMono hA).injective hij)]

/-- Universal harmonic bound: `recipSum A x ≤ 1 + log x`. -/
theorem recipSum_le_log (A : Set ℕ) (x : ℕ) :
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
  have hsub : (Finset.range x).filter (· ∈ A \ {0}) ⊆ (Finset.range x).filter (· ≠ 0) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, fun h0 => ha.2.2 (Set.mem_singleton_iff.mpr h0)⟩
  have hsum : ∑ a ∈ (Finset.range x).filter (· ≠ 0), (1 : ℝ) / a = (harmonic (x - 1) : ℝ) := by
    rw [hset, harmonic_eq_sum_Icc, Rat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rat.cast_inv, Rat.cast_natCast, one_div]
  calc recipSum A x = ∑ a ∈ (Finset.range x).filter (· ∈ A \ {0}), (1 : ℝ) / a :=
        recipSum_eq_sum_filter A x
    _ ≤ ∑ a ∈ (Finset.range x).filter (· ≠ 0), (1 : ℝ) / a :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)
    _ = (harmonic (x - 1) : ℝ) := hsum
    _ ≤ 1 + Real.log ↑(x - 1) := harmonic_le_one_add_log (x - 1)
    _ ≤ 1 + Real.log ↑x := add_le_add_left hlog 1

end JSP361
