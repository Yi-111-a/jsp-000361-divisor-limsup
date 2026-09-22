import JSP361.Basic
import JSP361.CountA
import JSP361.Counting
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Count

/-!
# JSP-000361 — band density / window counting

Window counting lemma: the elements of `A` in the band `(t, u]` number
at least `t · (recipSum A (u+1) − recipSum A (t+1))`, since each such
element contributes `1/a ≤ 1/t` to the reciprocal sum.

Explosion consequence (`recipSum_exp_ge_of_countA`): if the counting
function is everywhere dominated by `C · recipSum(⌈e^{ct}⌉+1)^k` with
`c = log 4 + 4`, then at every dense scale `t` the reciprocal sum at the
exponential scale is at least `(t / (C (log t)²))^{1/k}`.

`band_count_ge` combines: at a dense scale `t`, the band
`(t, ⌈e^{ct}⌉]` carries a large window count of `A`.
-/

namespace JSP361

open Finset
open Classical

/-- Window count vs window reciprocal mass: elements of `A` in `(t, u]`
number at least `t · (recipSum A (u+1) − recipSum A (t+1))`. -/
theorem window_count_ge (A : Set ℕ) {t u : ℕ} (ht : 1 ≤ t) (htu : t ≤ u) :
    t * (recipSum A (u + 1) - recipSum A (t + 1)) ≤
      (countA A (u + 1) - countA A (t + 1) : ℝ) := by
  classical
  rw [recipSum_eq_sum_filter, recipSum_eq_sum_filter]
  have hsub : (Finset.range (t + 1)).filter (· ∈ A \ {0}) ⊆
      (Finset.range (u + 1)).filter (· ∈ A \ {0}) :=
    Finset.filter_subset_filter _
      (Finset.range_subset_range.mpr (Nat.add_le_add_right htu 1))
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hcard : ((Finset.range (u + 1)).filter (· ∈ A \ {0}) \
      (Finset.range (t + 1)).filter (· ∈ A \ {0})).card =
      countA A (u + 1) - countA A (t + 1) := by
    rw [Finset.card_sdiff_of_subset hsub, ← countA_eq_card, ← countA_eq_card]
  rw [← hcard, Finset.mul_sum]
  calc ∑ a ∈ (Finset.range (u + 1)).filter (· ∈ A \ {0}) \
          (Finset.range (t + 1)).filter (· ∈ A \ {0}), (t : ℝ) * (1 / a)
      ≤ ∑ _a ∈ (Finset.range (u + 1)).filter (· ∈ A \ {0}) \
          (Finset.range (t + 1)).filter (· ∈ A \ {0}), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at ha
        obtain ⟨⟨_, haA⟩, hnot⟩ := ha
        have hge : t + 1 ≤ a := by
          by_contra hlt
          push_neg at hlt
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, haA⟩)
        have hapos : (0 : ℝ) < (a : ℝ) := by
          have h0 : 0 < a := by omega
          exact_mod_cast h0
        rw [mul_one_div, div_le_one hapos]
        exact_mod_cast (by omega : t ≤ a)
    _ = (((Finset.range (u + 1)).filter (· ∈ A \ {0}) \
          (Finset.range (t + 1)).filter (· ∈ A \ {0})).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- If `countA A (t+1) ≤ C · recipSum A (⌈e^{ct}⌉+1)^k` for ALL `t`
(with `c := Real.log 4 + 4`), then at every scale `t ≥ 8` where
`countA A t ≥ t / (log t)²`, the reciprocal sum at `⌈e^{ct}⌉+1` is at
least `(t / (C · (log t)²))^{1/k}`. -/
theorem recipSum_exp_ge_of_countA (A : Set ℕ) {k : ℕ} (hk : 1 ≤ k) {C : ℝ} (hC : 0 < C)
    (hfail : ∀ t : ℕ, (countA A (t + 1) : ℝ) ≤
      C * recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) ^ k)
    {t : ℕ} (ht : 8 ≤ t)
    (hdense : (t : ℝ) / (Real.log t)^2 ≤ countA A t) :
    ((t : ℝ) / (C * (Real.log t)^2)) ^ ((1 : ℝ) / k) ≤
      recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) := by
  have hlogpos : 0 < Real.log t :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hlog2pos : 0 < (Real.log t)^2 := pow_pos hlogpos 2
  have hchain : (t : ℝ) / (Real.log t)^2 ≤
      C * recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) ^ k := by
    calc (t : ℝ) / (Real.log t)^2
        ≤ countA A t := hdense
      _ ≤ countA A (t + 1) := by
          exact_mod_cast countA_mono A (Nat.le_succ t)
      _ ≤ C * recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) ^ k :=
          hfail t
  have hX : (t : ℝ) / (C * (Real.log t)^2) ≤
      recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) ^ k := by
    rw [div_le_iff₀ (mul_pos hC hlog2pos)]
    have h2 : (t : ℝ) ≤
        C * recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) ^ k *
          (Real.log t)^2 := by
      rwa [div_le_iff₀ hlog2pos] at hchain
    calc (t : ℝ) ≤
          C * recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) ^ k *
            (Real.log t)^2 := h2
      _ = recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) ^ k *
            (C * (Real.log t)^2) := by ring
  have hXnonneg : 0 ≤ (t : ℝ) / (C * (Real.log t)^2) :=
    div_nonneg (Nat.cast_nonneg t) (mul_nonneg hC.le (sq_nonneg _))
  have hfnonneg : 0 ≤ recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) :=
    recipSum_nonneg A _
  have hknz : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc ((t : ℝ) / (C * (Real.log t)^2)) ^ ((1 : ℝ) / k)
      ≤ (recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) ^ k) ^
          ((1 : ℝ) / k) :=
        Real.rpow_le_rpow hXnonneg hX (by positivity)
    _ = recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) := by
        rw [← Real.rpow_natCast _ k, ← Real.rpow_mul hfnonneg,
          mul_one_div_cancel hknz, Real.rpow_one]

/-- At dense scales, the band `(t, ⌈e^{ct}⌉]` contains at least
`t · (recipSum A (⌈e^{ct}⌉+1) − recipSum A (t+1))` elements of `A` —
the window version of the band estimate. -/
theorem band_count_ge (A : Set ℕ) {k : ℕ} (hk : 1 ≤ k) {C : ℝ} (hC : 0 < C)
    (hfail : ∀ t : ℕ, (countA A (t + 1) : ℝ) ≤
      C * recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1) ^ k)
    {t : ℕ} (ht : 8 ≤ t)
    (hdense : (t : ℝ) / (Real.log t)^2 ≤ countA A t) :
    t * (recipSum A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1)
          - recipSum A (t + 1)) ≤
      (countA A (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ + 1)
        - countA A (t + 1) : ℝ) := by
  have htu : t ≤ ⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ := by
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have htR : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    have h1 : (t : ℝ) ≤ Real.exp ((Real.log 4 + 4) * t) := by
      have h2 := Real.add_one_le_exp ((Real.log 4 + 4) * t)
      nlinarith [mul_nonneg hlog4 htR]
    have h3 : (t : ℝ) ≤ (⌈Real.exp ((Real.log 4 + 4) * t)⌉₊ : ℝ) :=
      h1.trans (Nat.le_ceil _)
    exact_mod_cast h3
  exact window_count_ge A (by omega) htu

end JSP361
