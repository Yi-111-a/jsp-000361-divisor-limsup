import Mathlib
import JSP361.Defs

namespace JSP361

open Finset
open scoped Classical

/-- `dA A n` as a sum over all divisors of `n`. -/
private theorem avg_dA_eq_sum (A : Set ℕ) (n : ℕ) :
    (dA A n : ℝ) = ∑ a ∈ n.divisors, (if a ∈ A then (1 : ℝ) else 0) := by
  classical
  rw [show dA A n = (n.divisors.filter (· ∈ A)).card from rfl]
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ A <;> simp [ha]

/-- Extending a sum over `n.divisors` to a sum over `Finset.range x` (for `n < x`). -/
private theorem avg_sum_divisors_eq_sum_range (A : Set ℕ) {n x : ℕ} (hn : n < x) :
    (∑ a ∈ n.divisors, (if a ∈ A then (1 : ℝ) else 0))
      = ∑ a ∈ Finset.range x,
          (if a ∈ n.divisors then (if a ∈ A then (1 : ℝ) else 0) else 0) := by
  classical
  have hsub : n.divisors ⊆ Finset.range x := by
    intro a ha
    rw [Nat.mem_divisors] at ha
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero ha.2) ha.1) hn
  calc ∑ a ∈ n.divisors, (if a ∈ A then (1 : ℝ) else 0)
      = ∑ a ∈ n.divisors,
          (if a ∈ n.divisors then (if a ∈ A then (1 : ℝ) else 0) else 0) :=
        Finset.sum_congr rfl (fun a ha => (if_pos ha).symm)
    _ = ∑ a ∈ Finset.range x,
          (if a ∈ n.divisors then (if a ∈ A then (1 : ℝ) else 0) else 0) :=
        Finset.sum_subset hsub (fun a _ ha2 => if_neg ha2)

/-- The inner sum (over `n`) evaluated: it counts multiples. -/
private theorem avg_inner_sum (A : Set ℕ) (a x : ℕ) :
    (∑ n ∈ Finset.range x,
        (if a ∈ n.divisors then (if a ∈ A then (1 : ℝ) else 0) else 0))
      = if a ∈ A then
          ((((Finset.range x).filter (fun n => a ∈ n.divisors)).card : ℕ) : ℝ)
          else 0 := by
  classical
  by_cases haA : a ∈ A
  · simp only [if_pos haA]
    rw [Finset.card_filter]
    push_cast
    rfl
  · simp only [if_neg haA]
    apply Finset.sum_eq_zero
    intro n _
    split_ifs <;> rfl

/-- The number of `n < x` with `a ∈ n.divisors` is at least `x / a - 1`. -/
private theorem avg_count_ge (a x : ℕ) :
    (x : ℝ) / a - 1
      ≤ (((Finset.range x).filter (fun n => a ∈ n.divisors)).card : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · rw [Nat.cast_zero, div_zero]
    have hnonneg : (0 : ℝ)
        ≤ (((Finset.range x).filter (fun n => (0 : ℕ) ∈ n.divisors)).card : ℝ) :=
      Nat.cast_nonneg _
    linarith
  · -- inject `j ↦ j * a` from `Icc 1 ((x-1)/a)` into the filtered set
    have himg : (Finset.Icc 1 ((x - 1) / a)).image (· * a)
        ⊆ (Finset.range x).filter (fun n => a ∈ n.divisors) := by
      intro m hm
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
      simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · have h3 : j * a ≤ x - 1 :=
          le_trans (Nat.mul_le_mul hj2 le_rfl) (Nat.div_mul_le_self _ _)
        have hpos : 1 ≤ j * a := Nat.mul_pos hj1 ha1
        omega
      · exact ⟨j, mul_comm j a⟩
      · exact (Nat.mul_pos hj1 ha1).ne'
    have hcardle : (x - 1) / a
        ≤ ((Finset.range x).filter (fun n => a ∈ n.divisors)).card := by
      have h := Finset.card_le_card himg
      rw [Finset.card_image_of_injective _
        (fun i j hij => Nat.mul_right_cancel ha1 hij), Nat.card_Icc,
        Nat.add_sub_cancel] at h
      exact h
    -- `(x-1)/a ≥ x/a - 1` over ℝ since `a * ((x-1)/a + 1) ≥ x`
    have h1n : x ≤ a * ((x - 1) / a + 1) := by
      rw [mul_add, mul_one]
      have h2 := Nat.div_add_mod (x - 1) a
      have h3 : (x - 1) % a < a := Nat.mod_lt _ ha1
      omega
    have hqr : (x : ℝ) / a ≤ (((x - 1) / a : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ (show (0 : ℝ) < a by exact_mod_cast ha1)]
      calc (x : ℝ) ≤ ((a * ((x - 1) / a + 1) : ℕ) : ℝ) := by exact_mod_cast h1n
        _ = ((((x - 1) / a : ℕ) : ℝ) + 1) * (a : ℝ) := by push_cast; ring
    have hcardr : (((x - 1) / a : ℕ) : ℝ)
        ≤ (((Finset.range x).filter (fun n => a ∈ n.divisors)).card : ℝ) := by
      exact_mod_cast hcardle
    linarith

/-- `x * recipSum A x - x ≤ ∑ a ∈ range x, (if a ∈ A then x / a - 1 else 0)`. -/
private theorem avg_step_one (A : Set ℕ) (x : ℕ) :
    x * recipSum A x - x
      ≤ ∑ a ∈ Finset.range x, (if a ∈ A then ((x : ℝ) / a - 1) else 0) := by
  classical
  have hrec : recipSum A x
      = ∑ a ∈ (Finset.range x).filter (· ∈ A), (1 : ℝ) / a := by
    rw [Finset.sum_filter]
    rfl
  have hfcard : (((Finset.range x).filter (· ∈ A)).card : ℝ) ≤ x := by
    have h := Finset.card_le_card
      (Finset.filter_subset (fun a => a ∈ A) (Finset.range x))
    rw [Finset.card_range] at h
    exact_mod_cast h
  have hsumA : ∑ a ∈ (Finset.range x).filter (· ∈ A), ((x : ℝ) / a)
      = x * recipSum A x := by
    rw [hrec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_one_div]
  have hsum1 : ∑ a ∈ (Finset.range x).filter (· ∈ A), (1 : ℝ)
      = (((Finset.range x).filter (· ∈ A)).card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have heq : ∑ a ∈ Finset.range x, (if a ∈ A then ((x : ℝ) / a - 1) else 0)
      = x * recipSum A x - (((Finset.range x).filter (· ∈ A)).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_sub_distrib, hsumA, hsum1]
  rw [heq]
  linarith

theorem sum_range_dA_ge (A : Set ℕ) (x : ℕ) :
    x * recipSum A x - x ≤ ∑ n ∈ Finset.range x, (dA A n : ℝ) := by
  classical
  -- swap the order of summation
  have hswap : (∑ n ∈ Finset.range x, (dA A n : ℝ))
      = ∑ a ∈ Finset.range x, ∑ n ∈ Finset.range x,
          (if a ∈ n.divisors then (if a ∈ A then (1 : ℝ) else 0) else 0) := by
    trans ∑ n ∈ Finset.range x, ∑ a ∈ Finset.range x,
        (if a ∈ n.divisors then (if a ∈ A then (1 : ℝ) else 0) else 0)
    · apply Finset.sum_congr rfl
      intro n hn
      rw [avg_dA_eq_sum A n]
      exact avg_sum_divisors_eq_sum_range A (Finset.mem_range.mp hn)
    · exact Finset.sum_comm
  calc x * recipSum A x - x
      ≤ ∑ a ∈ Finset.range x, (if a ∈ A then ((x : ℝ) / a - 1) else 0) :=
        avg_step_one A x
    _ ≤ ∑ a ∈ Finset.range x,
          (if a ∈ A then
            ((((Finset.range x).filter (fun n => a ∈ n.divisors)).card : ℕ) : ℝ)
            else 0) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases haA : a ∈ A
        · rw [if_pos haA, if_pos haA]
          exact avg_count_ge a x
        · rw [if_neg haA, if_neg haA]
    _ = ∑ a ∈ Finset.range x, ∑ n ∈ Finset.range x,
          (if a ∈ n.divisors then (if a ∈ A then (1 : ℝ) else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (avg_inner_sum A a x).symm
    _ = ∑ n ∈ Finset.range x, (dA A n : ℝ) := hswap.symm

theorem exists_dA_ge (A : Set ℕ) (x : ℕ) (hx : 0 < x) :
    ∃ n : ℕ, n < x ∧ recipSum A x - 1 ≤ (dA A n : ℝ) := by
  classical
  have hge := sum_range_dA_ge A x
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ n, n < x → (dA A n : ℝ) < recipSum A x - 1
  have hlt : ∑ n ∈ Finset.range x, (dA A n : ℝ)
      < ∑ _n ∈ Finset.range x, (recipSum A x - 1) := by
    apply Finset.sum_lt_sum
    · intro n hn
      exact le_of_lt (hcon n (Finset.mem_range.mp hn))
    · exact ⟨0, Finset.mem_range.mpr hx, hcon 0 hx⟩
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  have hkey : (x : ℝ) * (recipSum A x - 1) = x * recipSum A x - x := by ring
  rw [hkey] at hlt
  linarith

end JSP361
