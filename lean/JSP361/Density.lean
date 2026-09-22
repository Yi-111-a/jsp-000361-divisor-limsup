import JSP361.CountA
import JSP361.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# JSP-000361 — partial summation density lemma

Dyadic partial summation for `recipSum`: the reciprocal sum over the
block `[2^j, 2^{j+1})` is at most `countA A (2^{j+1}) / 2^j`.  Telescoping
gives `recipSum A (2^J) ≤ ∑_{j < J} countA A (2^{j+1}) / 2^j`.

Main result (`exists_countA_ge_div_log_sq`): if `recipSum A` is unbounded
then for arbitrarily large `y` one has `countA A y ≥ y / (log y)²`.
The proof is by contradiction: if `countA A y < y / (log y)²` for all
`y ≥ B`, then every dyadic block `j ≥ J₀ := Nat.log 2 B + 1` contributes
at most `2 / ((j+1) log 2)²`, whose sum is bounded by `4 / (log 2)²`,
while the `J₀` early blocks contribute at most `2` each — so `recipSum`
is bounded, contradiction.
-/

namespace JSP361

open Finset
open Classical

/-- Elements of `A` counted in the dyadic block `[2^j, 2^{j+1})` each
contribute `≤ 1/2^j` to `recipSum`. -/
theorem recipSum_block_le (A : Set ℕ) (j : ℕ) :
    recipSum A (2 ^ (j + 1)) - recipSum A (2 ^ j) ≤
      (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j := by
  classical
  rw [recipSum_eq_sum_filter, recipSum_eq_sum_filter]
  have hsub : (Finset.range (2 ^ j)).filter (· ∈ A \ {0}) ⊆
      (Finset.range (2 ^ (j + 1))).filter (· ∈ A \ {0}) :=
    Finset.filter_subset_filter _
      (Finset.range_subset_range.mpr
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)))
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hcard : ((Finset.range (2 ^ (j + 1))).filter (· ∈ A \ {0}) \
      (Finset.range (2 ^ j)).filter (· ∈ A \ {0})).card ≤
      countA A (2 ^ (j + 1)) := by
    rw [countA_eq_card]
    exact Finset.card_le_card Finset.sdiff_subset
  calc ∑ a ∈ (Finset.range (2 ^ (j + 1))).filter (· ∈ A \ {0}) \
          (Finset.range (2 ^ j)).filter (· ∈ A \ {0}), (1 : ℝ) / a
      ≤ ∑ _a ∈ (Finset.range (2 ^ (j + 1))).filter (· ∈ A \ {0}) \
          (Finset.range (2 ^ j)).filter (· ∈ A \ {0}),
          (1 : ℝ) / (2 ^ j : ℕ) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at ha
        obtain ⟨⟨_, haA⟩, hnot⟩ := ha
        have hge : 2 ^ j ≤ a := by
          by_contra hlt
          push_neg at hlt
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, haA⟩)
        have hpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by
          exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 2) j
        exact one_div_le_one_div_of_le hpos (by exact_mod_cast hge)
    _ = (((Finset.range (2 ^ (j + 1))).filter (· ∈ A \ {0}) \
          (Finset.range (2 ^ j)).filter (· ∈ A \ {0})).card : ℝ) *
          (1 / (2 ^ j : ℕ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (countA A (2 ^ (j + 1)) : ℝ) * (1 / (2 ^ j : ℕ)) := by
        apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr (Nat.cast_nonneg _))
        exact_mod_cast hcard
    _ = (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j := by
        rw [mul_one_div, Nat.cast_pow, Nat.cast_ofNat]

/-- Telescoped: `recipSum A (2^J) ≤ ∑_{j<J} countA A (2^{j+1})/2^j`
(`recipSum A 1 = 0` since only `a = 0` is below `1` and `1/0 = 0`). -/
theorem recipSum_two_pow_le (A : Set ℕ) (J : ℕ) :
    recipSum A (2 ^ J) ≤
      ∑ j ∈ Finset.range J, (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j := by
  classical
  have h0 : recipSum A 1 = 0 := by
    rw [recipSum_eq_sum_filter]
    apply Finset.sum_eq_zero
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range, Nat.lt_one_iff] at ha
    obtain ⟨rfl, -, h0⟩ := ha
    exact absurd (Set.mem_singleton_iff.mpr rfl) h0
  calc recipSum A (2 ^ J)
      = recipSum A (2 ^ J) - recipSum A (2 ^ 0) := by
        rw [pow_zero, h0, sub_zero]
    _ = ∑ j ∈ Finset.range J,
          (recipSum A (2 ^ (j + 1)) - recipSum A (2 ^ j)) :=
        (Finset.sum_range_sub (fun j => recipSum A (2 ^ j)) J).symm
    _ ≤ ∑ j ∈ Finset.range J, (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j :=
        Finset.sum_le_sum fun j _ => recipSum_block_le A j

/-- Telescoping bound `∑_{j < J} 1/(j+1)² ≤ 2 - 1/J` for `J ≥ 1`, via
`1/(j+1)² ≤ 1/j - 1/(j+1)`. -/
private theorem sum_range_inv_sq_le_aux (J : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 - (J : ℝ)⁻¹ := by
  induction J, hJ using Nat.le_induction with
  | base =>
      rw [Finset.sum_range_one]
      norm_num
  | succ n hn ih =>
      rw [Finset.sum_range_succ]
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hne1 : (n : ℝ) ≠ 0 := ne_of_gt hn'
      have hne2 : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
      have hstep : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ (n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹ := by
        have h1 : (n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹ = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
          field_simp
          ring
        rw [h1]
        exact one_div_le_one_div_of_le
          (mul_pos hn' (by positivity)) (by nlinarith [hn'])
      have hcast : ((n + 1 : ℕ) : ℝ)⁻¹ = ((n : ℝ) + 1)⁻¹ := by push_cast
      rw [hcast]
      linarith [ih, hstep]

/-- `∑_{j < J} 1/(j+1)² ≤ 2`. -/
private theorem sum_range_inv_sq_le (J : ℕ) :
    ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos J with h0 | hpos
  · subst h0
    simp
  · have h := sum_range_inv_sq_le_aux J hpos
    have hnn : (0 : ℝ) ≤ (J : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    linarith

/-- **Density lemma** (partial summation): if `recipSum A` is unbounded,
then for arbitrarily large `y`, `countA A y ≥ y/(log y)^2`. -/
theorem exists_countA_ge_div_log_sq (A : Set ℕ)
    (hU : ∀ M : ℝ, ∃ x : ℕ, M < recipSum A x) (B : ℕ) :
    ∃ y : ℕ, B ≤ y ∧ (y : ℝ) / (Real.log y) ^ 2 ≤ countA A y := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ y, B ≤ y → ↑(countA A y) < ↑y / (Real.log ↑y) ^ 2`
  set J₀ := Nat.log 2 B + 1 with hJ₀
  have hc_pos : (0 : ℝ) < (Real.log 2) ^ 2 :=
    pow_pos (Real.log_pos (by norm_num)) 2
  -- Early blocks: `countA / 2^j ≤ 2^{j+1}/2^j = 2`.
  have hf_early : ∀ j : ℕ, (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j ≤ 2 := by
    intro j
    have h1 : (countA A (2 ^ (j + 1)) : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast countA_le A (2 ^ (j + 1))
    have h2 : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos (by norm_num) j
    calc (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j
        ≤ ((2 ^ (j + 1) : ℕ) : ℝ) / 2 ^ j := div_le_div_of_nonneg_right h1 h2.le
      _ = 2 := by
        rw [div_eq_iff (ne_of_gt h2)]
        push_cast
        rw [← pow_succ']
  -- Late blocks (`j ≥ J₀`): the density bound gives
  -- `countA A (2^{j+1}) < 2^{j+1}/((j+1) log 2)^2`.
  have hf_late : ∀ j : ℕ, ¬ j < J₀ →
      (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j ≤
        (2 / (Real.log 2) ^ 2) * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j hj
    have hjB : B ≤ 2 ^ (j + 1) := by
      have h1 : B < 2 ^ J₀ := by
        rw [hJ₀]
        exact Nat.lt_pow_succ_log_self (by norm_num) B
      have h2 : 2 ^ J₀ ≤ 2 ^ (j + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hlt := hcon (2 ^ (j + 1)) hjB
    have hlog : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) =
        ((j + 1 : ℕ) : ℝ) * Real.log 2 := by
      have hc1 : ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by
        push_cast
        ring
      rw [hc1, Real.log_pow]
    rw [hlog] at hlt
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos (by norm_num) j
    have hle := div_le_div_of_nonneg_right hlt.le h2j.le
    refine hle.trans_eq ?_
    have hne2 : (2 : ℝ) ^ j ≠ 0 := ne_of_gt h2j
    have e1 : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ']
    have e2 : (((j + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 =
        ((j : ℝ) + 1) ^ 2 * (Real.log 2) ^ 2 := by
      push_cast
      ring
    rw [e1, e2, div_div, mul_div_mul_right _ _ hne2,
      mul_comm ((j : ℝ) + 1) ^ 2 (Real.log 2) ^ 2, div_mul_div_comm, mul_one]
  -- Uniform bound on `recipSum A (2^J)` for every `J`.
  have hbound : ∀ J : ℕ, recipSum A (2 ^ J) ≤
      2 * J₀ + (2 / (Real.log 2) ^ 2) * 2 := by
    intro J
    have hcard : ((Finset.range J).filter (· < J₀)).card ≤ J₀ := by
      calc ((Finset.range J).filter (· < J₀)).card
          ≤ (Finset.range J₀).card := by
            apply Finset.card_le_card
            intro i hi
            rw [Finset.mem_filter, Finset.mem_range] at hi
            exact Finset.mem_range.mpr hi.2
        _ = J₀ := Finset.card_range J₀
    have hearly : ∑ j ∈ (Finset.range J).filter (· < J₀),
        (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j ≤ 2 * J₀ := by
      calc ∑ j ∈ (Finset.range J).filter (· < J₀),
            (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j
          ≤ ∑ _j ∈ (Finset.range J).filter (· < J₀), (2 : ℝ) :=
            Finset.sum_le_sum fun j _ => hf_early j
        _ = (((Finset.range J).filter (· < J₀)).card : ℝ) * 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ J₀ * 2 := by
            apply mul_le_mul_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
            exact_mod_cast hcard
        _ = 2 * J₀ := by ring
    have hlate : ∑ j ∈ (Finset.range J).filter (fun j => ¬ j < J₀),
        (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j ≤
          (2 / (Real.log 2) ^ 2) *
            ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 := by
      calc ∑ j ∈ (Finset.range J).filter (fun j => ¬ j < J₀),
            (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j
          ≤ ∑ j ∈ (Finset.range J).filter (fun j => ¬ j < J₀),
            (2 / (Real.log 2) ^ 2) * (1 / ((j : ℝ) + 1) ^ 2) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [Finset.mem_filter] at hj
            exact hf_late j hj.2
        _ ≤ ∑ j ∈ Finset.range J,
            (2 / (Real.log 2) ^ 2) * (1 / ((j : ℝ) + 1) ^ 2) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro j _ _
            exact mul_nonneg (div_nonneg (by norm_num) hc_pos.le)
              (one_div_nonneg.mpr (sq_nonneg _))
        _ = (2 / (Real.log 2) ^ 2) *
            ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 := by
            rw [Finset.mul_sum]
    calc recipSum A (2 ^ J)
        ≤ ∑ j ∈ Finset.range J, (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j :=
          recipSum_two_pow_le A J
      _ = ∑ j ∈ (Finset.range J).filter (· < J₀),
            (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j
          + ∑ j ∈ (Finset.range J).filter (fun j => ¬ j < J₀),
            (countA A (2 ^ (j + 1)) : ℝ) / 2 ^ j :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ 2 * J₀ + (2 / (Real.log 2) ^ 2) *
          ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 :=
          add_le_add hearly hlate
      _ ≤ 2 * J₀ + (2 / (Real.log 2) ^ 2) * 2 :=
          add_le_add_left
            (mul_le_mul_of_nonneg_left (sum_range_inv_sq_le J)
              (div_nonneg (by norm_num) hc_pos.le)) _
  -- But `recipSum` is unbounded, contradiction.
  obtain ⟨x', hx'⟩ := hU (2 * J₀ + (2 / (Real.log 2) ^ 2) * 2)
  have hJx : x' < 2 ^ (Nat.log 2 x' + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) x'
  have hle1 := recipSum_mono A (le_of_lt hJx)
  have hle2 := hbound (Nat.log 2 x' + 1)
  linarith

end JSP361
