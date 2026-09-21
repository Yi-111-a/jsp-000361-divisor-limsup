import JSP361.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Ring

/-!
# JSP-000361 — the "super-gap" milestone (ErSa80)

If `A ⊆ ℕ` has arbitrarily large "prefixes" `s` whose product lies below
the next element of `A` (multiplicative super-gaps), then for every `k`
and every real `C` there exist `x` and `n < x` with
`C * recipSum A x ^ k < dA A n`.

Proof outline:
* `gap_eventually_large`: `m` eventually dominates `C * (1 + log m) ^ k`
  (via `Real.isLittleO_pow_log_id_atTop`).
* `gap_sum_inv_le`: a set `s` of `m` distinct positive integers satisfies
  `∑_{b ∈ s} 1/b ≤ H_m ≤ 1 + log m` (rank argument +
  `harmonic_le_one_add_log`).
* `gap_recipSum_eq`: at a super-gap `a'`, `recipSum A a' = ∑_{b ∈ s} 1/b`
  since `s` is exactly the positive part of `A` below `a'` (the `a = 0`
  term contributes `0` anyway).
* `gap_card_le_dA`: `s` injects into the `A`-divisors of `∏ s`.
-/

namespace JSP361

open Finset

/-- For any `k` and `C`, `m` eventually exceeds `C * (1 + log m)^k`. -/
private theorem gap_eventually_large (k : ℕ) (C : ℝ) :
    ∃ j : ℕ, 1 ≤ j ∧ ∀ m : ℕ, j ≤ m → C * (1 + Real.log m) ^ k < m := by
  by_cases hC : C ≤ 0
  · refine ⟨1, le_refl 1, fun m hm => ?_⟩
    have hm1 : (0 : ℝ) < m := by exact_mod_cast hm
    have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
    have hpow : 0 ≤ (1 + Real.log m) ^ k := pow_nonneg (by linarith) k
    calc C * (1 + Real.log m) ^ k ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hC hpow
      _ < m := hm1
  · have hC : 0 < C := not_le.mp hC
    have hC1 : (0 : ℝ) < |C| + 1 := by positivity
    set c : ℝ := (|C| + 1)⁻¹ with hc_def
    have hc : 0 < c := by positivity
    have h2 := (Real.isLittleO_pow_log_id_atTop (n := k)).const_mul_left ((2 : ℝ) ^ k)
    have h2' := h2.congr_left (fun x => (mul_pow 2 (Real.log x) k).symm)
    have hb := h2'.bound hc
    have hev : ∀ᶠ x : ℝ in Filter.atTop, C * (1 + Real.log x) ^ k < x := by
      filter_upwards [hb, Filter.eventually_ge_atTop (Real.exp 1),
        Filter.eventually_ge_atTop (0 : ℝ)] with x hbn hxge hx0
      have hlog1 : 1 ≤ Real.log x := by
        have h := Real.log_le_log (Real.exp_pos 1) hxge
        rwa [Real.log_exp] at h
      have hlogx0 : 0 ≤ Real.log x := by linarith
      have h2logx0 : 0 ≤ 2 * Real.log x := by linarith
      have hpow : (1 + Real.log x) ^ k ≤ (2 * Real.log x) ^ k :=
        pow_le_pow_left₀ (by linarith) (by linarith) k
      have hnorm : |(2 * Real.log x) ^ k| ≤ c * |x| := by
        have h := hbn
        rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
      rw [abs_of_nonneg (pow_nonneg h2logx0 k), abs_of_nonneg hx0] at hnorm
      have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxge
      calc C * (1 + Real.log x) ^ k
          ≤ C * (2 * Real.log x) ^ k :=
            mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
        _ ≤ C * (c * x) :=
            mul_le_mul_of_nonneg_left hnorm (le_of_lt hC)
        _ = (C / (|C| + 1)) * x := by
            rw [hc_def, div_eq_mul_inv]; ring
        _ < 1 * x := by
            apply mul_lt_mul_of_pos_right _ hxpos
            rw [div_lt_one hC1]
            linarith [le_abs_self C]
        _ = x := one_mul x
    rw [Filter.eventually_atTop] at hev
    obtain ⟨x0, hx0⟩ := hev
    refine ⟨⌈max x0 1⌉₊, ?_, fun m hm => hx0 m ?_⟩
    · exact Nat.ceil_pos.mpr (lt_of_lt_of_le one_pos (le_max_right x0 1))
    · have h2 : max x0 1 ≤ (⌈max x0 1⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : (⌈max x0 1⌉₊ : ℝ) ≤ m := by exact_mod_cast hm
      linarith [le_max_left x0 1]

/-- `∑_{b ∈ s} 1/b ≤ 1 + log |s|` for a finset `s` of positive naturals.
The `i`-th smallest element of `s` is at least `i + 1`, so the sum is at
most the `|s|`-th harmonic number. -/
private theorem gap_sum_inv_le (s : Finset ℕ) (h0 : 0 ∉ s) :
    ∑ b ∈ s, (1 : ℝ) / b ≤ 1 + Real.log s.card := by
  classical
  have hs_pos : ∀ b ∈ s, 0 < b :=
    fun b hb => Nat.pos_of_ne_zero (fun h => h0 (h ▸ hb))
  -- rank of `b` inside `s` lands in `Icc 1 s.card`
  have hr_mem : ∀ b ∈ s, (s.filter (· ≤ b)).card ∈ Finset.Icc 1 s.card := by
    intro b hb
    rw [Finset.mem_Icc]
    exact ⟨Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, le_refl b⟩⟩,
      Finset.card_le_card (Finset.filter_subset _ _)⟩
  -- the rank is strictly increasing on `s`
  have hr_lt : ∀ a ∈ s, ∀ b ∈ s, a < b →
      (s.filter (· ≤ a)).card < (s.filter (· ≤ b)).card := by
    intro a ha b hb hab
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    refine ⟨b, ?_, ?_⟩
    · simp only [Finset.mem_filter, not_and, Nat.not_le]
      exact fun _ => hab
    · intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨hb, le_refl _⟩
      · rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, le_trans hx.2 (le_of_lt hab)⟩
  have hr_inj : ∀ x ∈ s, ∀ y ∈ s,
      (s.filter (· ≤ x)).card = (s.filter (· ≤ y)).card → x = y := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd hab (hr_lt a ha b hb hlt).ne
    · exact heq
    · exact absurd hab.symm (hr_lt b hb a ha hgt).ne
  -- the rank of `b` is at most `b` (ranks are distinct positive integers ≤ b)
  have hr_le : ∀ b ∈ s, (s.filter (· ≤ b)).card ≤ b := by
    intro b hb
    have hsub : s.filter (· ≤ b) ⊆ Finset.Icc 1 b := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_Icc]
      exact ⟨hs_pos a ha.1, ha.2⟩
    calc (s.filter (· ≤ b)).card ≤ (Finset.Icc 1 b).card :=
          Finset.card_le_card hsub
      _ = b := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  calc ∑ b ∈ s, (1 : ℝ) / b
      ≤ ∑ b ∈ s, (1 : ℝ) / ((s.filter (· ≤ b)).card : ℕ) := by
        apply Finset.sum_le_sum
        intro b hb
        have hrb : 0 < (s.filter (· ≤ b)).card :=
          Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, le_refl b⟩⟩
        apply one_div_le_one_div_of_le (by exact_mod_cast hrb)
        exact_mod_cast hr_le b hb
    _ = ∑ i ∈ s.image (fun b => (s.filter (· ≤ b)).card), (1 : ℝ) / i := by
        rw [Finset.sum_image (fun x hx y hy h => hr_inj x hx y hy h)]
    _ ≤ ∑ i ∈ Finset.Icc 1 s.card, (1 : ℝ) / i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          rw [Finset.mem_image] at hi
          obtain ⟨b, hb, rfl⟩ := hi
          exact hr_mem b hb
        · intro i _ _
          positivity
    _ = (harmonic s.card : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        apply Finset.sum_congr rfl
        intro i _
        rw [one_div]
    _ ≤ 1 + Real.log s.card := harmonic_le_one_add_log _

/-- At a super-gap `a'`, `recipSum A a'` is exactly `∑_{b ∈ s} 1/b`:
every positive element of `A` below `a'` lies in `s`, every `b ∈ s` lies
in `A` and below `a'` (as `b ≤ ∏ s < a'`), and the `a = 0` term of the
sum is `0` anyway. -/
private theorem gap_recipSum_eq (A : Set ℕ) {s : Finset ℕ} {a' : ℕ}
    (hsub : (↑s : Set ℕ) ⊆ A) (h0 : 0 ∉ s)
    (hprod : (∏ b ∈ s, b) < a')
    (hfull : ∀ a ∈ A, 0 < a → a < a' → a ∈ s) :
    recipSum A a' = ∑ b ∈ s, (1 : ℝ) / b := by
  classical
  have hs_pos : ∀ b ∈ s, 0 < b :=
    fun b hb => Nat.pos_of_ne_zero (fun h => h0 (h ▸ hb))
  have hPpos : 0 < ∏ b ∈ s, b := Finset.prod_pos hs_pos
  have hs_range : s ⊆ Finset.range a' := by
    intro b hb
    rw [Finset.mem_range]
    exact lt_of_le_of_lt
      (Nat.le_of_dvd hPpos (Finset.dvd_prod_of_mem _ hb)) hprod
  have hrec : recipSum A a' =
      ∑ a ∈ Finset.range a', (if a ∈ A then (1 : ℝ) / a else 0) := rfl
  rw [hrec, ← Finset.sum_subset hs_range _]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [ite_eq_left (hsub (Finset.mem_coe.mpr hb))]
  · intro a harange has
    by_cases hA : a ∈ A
    · rcases Nat.eq_zero_or_pos a with h | h
      · subst h
        rw [ite_eq_left hA]
        norm_num
      · exact absurd (hfull a hA h (Finset.mem_range.mp harange)) has
    · rw [ite_eq_right hA]

/-- Every element of `s` is a nonzero element of `A` dividing `∏ s`. -/
private theorem gap_card_le_dA (A : Set ℕ) {F : Finset ℕ}
    (hA : ∀ a ∈ F, a ∈ A) (h0 : 0 ∉ F) : F.card ≤ dA A (∏ a ∈ F, a) := by
  have hprod : (∏ a ∈ F, a) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro b hb hb0
    exact h0 ((show b = 0 from hb0) ▸ hb)
  classical
  unfold dA
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨Finset.dvd_prod_of_mem (fun x ↦ x) ha, hprod⟩, hA a ha⟩

private theorem gap_recipSum_nonneg (A : Set ℕ) (x : ℕ) :
    0 ≤ recipSum A x := by
  unfold recipSum
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_refl 0

/-- **Super-gap case of JSP-000361 (ErSa80).** If `A` has arbitrarily
large prefixes whose product lies below the next element of `A`, then
`C * recipSum A x ^ k < dA A n` for some `n < x`. -/
theorem divisor_set_limsup_of_gap (A : Set ℕ)
    (hgap : ∀ J : ℕ, ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ A ∧ 0 ∉ s ∧ J ≤ s.card ∧
      ∃ a' : ℕ, a' ∈ A ∧ (∏ b ∈ s, b) < a' ∧
        (∀ a ∈ A, 0 < a → a < a' → a ∈ s))
    (k : ℕ) (C : ℝ) :
    ∃ x : ℕ, ∃ n : ℕ, n < x ∧ C * recipSum A x ^ k < (dA A n : ℝ) := by
  obtain ⟨j, hj1, hj⟩ := gap_eventually_large k C
  obtain ⟨s, hsub, h0, hcard, a', _haA, hprod, hfull⟩ := hgap j
  refine ⟨a', ∏ b ∈ s, b, hprod, ?_⟩
  have hdA : s.card ≤ dA A (∏ b ∈ s, b) :=
    gap_card_le_dA A (fun a ha => hsub (Finset.mem_coe.mpr ha)) h0
  have hrec : recipSum A a' = ∑ b ∈ s, (1 : ℝ) / b :=
    gap_recipSum_eq A hsub h0 hprod hfull
  have hle : recipSum A a' ≤ 1 + Real.log s.card := by
    rw [hrec]
    exact gap_sum_inv_le s h0
  have hR0 : 0 ≤ recipSum A a' := gap_recipSum_nonneg A a'
  have hmlt : C * (1 + Real.log s.card) ^ k < s.card := hj s.card hcard
  have hmpos : (0 : ℝ) < s.card := by
    have : 1 ≤ s.card := le_trans hj1 hcard
    exact_mod_cast this
  by_cases hC : C ≤ 0
  · calc C * recipSum A a' ^ k ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC (pow_nonneg hR0 k)
      _ < s.card := hmpos
      _ ≤ dA A (∏ b ∈ s, b) := by exact_mod_cast hdA
  · have hC : 0 < C := not_le.mp hC
    calc C * recipSum A a' ^ k ≤ C * (1 + Real.log s.card) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR0 hle k) (le_of_lt hC)
      _ < s.card := hmlt
      _ ≤ dA A (∏ b ∈ s, b) := by exact_mod_cast hdA

end JSP361
