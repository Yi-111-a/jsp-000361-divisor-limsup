import JSP361.Defs
import JSP361.MassSplit
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# JSP-000361 — tail bound for large-prime `Ω` (with multiplicity)

For `1 ≤ z` and `2z ≤ Y`:

  `#{n ≤ u : s ≤ Ω_{>Y}(n)} ≤ u·z^{-s}·(∏_{p≤Y}(1-1/p)⁻¹)·exp(2z·E'')`,

where `Ω_{>Y}(n) = ∑_{p ∈ n.primeFactors, Y < p} n.factorization p` and
`E'' = ∑_{Y < p ≤ u} 1/p`.

Proof route (Rankin trick, weight `z^{Ω_{>Y}(n)}/n`):

* `∑_{n≤u} z^{Ω_{>Y}(n)}/n ≤ ∏_{p≤Y}(1-1/p)⁻¹ · ∏_{Y<p≤u}(1-z/p)⁻¹`
  via `MassSplit.sum_factorization_prod_le` with
  `w p = if Y < p then z/p else 1/p`.
* `∏_{Y<p≤u}(1-z/p)⁻¹ ≤ exp(2z·E'')` since `p > Y ≥ 2z` gives
  `z/p ≤ 1/2` and `-log(1-w) ≤ 2w` for `w ≤ 1/2`
  (see `MassSplit.inv_one_sub_le_exp_two_mul`).
* Markov: on the filtered set `z^{Ω}/n ≥ z^s/u`, so
  `card·z^s/u ≤ ∑_{n≤u} z^{Ω}/n`.
-/

namespace JSP361

open Finset
open scoped Classical

/-- Tail bound for the number of `n ≤ u` whose `Y`-rough prime-factor
count *with multiplicity* exceeds `s`, valid for `s ≥ 1` (for `s = 0` the
filtered set has `u + 1` elements and the bound can fail, e.g. `u = 0`). -/
theorem card_bigOmega_ge_le (Y u s : ℕ) {z : ℝ} (hz : 1 ≤ z)
    (hzy : 2 * z ≤ (Y : ℝ)) (hs : 1 ≤ s) :
    (((Finset.range (u + 1)).filter (fun n ↦ s ≤
        ∑ p ∈ n.primeFactors.filter (fun p ↦ Y < p),
          n.factorization p)).card : ℝ)
      ≤ (u : ℝ) * z ^ (-(s : ℝ)) *
          (∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1 : ℝ) / p)⁻¹) *
          Real.exp (2 * z *
            (∑ p ∈ (Nat.primesBelow (u + 1)).filter (fun p ↦ Y < p),
              (1 : ℝ) / p)) := by
  classical
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · -- `u = 0`: `s ≥ 1` forces `n ≠ 0`, so the filtered set is empty.
    have hF : (Finset.range (0 + 1)).filter (fun n ↦ s ≤
        ∑ p ∈ n.primeFactors.filter (fun p ↦ Y < p),
          n.factorization p) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro n hn
      have hnm := Finset.mem_filter.mp hn
      have hn0 : n = 0 := by
        have := Finset.mem_range.mp hnm.1
        omega
      subst hn0
      rw [Nat.primeFactors_zero, Finset.filter_empty, Finset.sum_empty] at hnm
      omega
    rw [hF, Finset.card_empty, Nat.cast_zero]
    positivity
  -- `u ≥ 1`.  Set up the prime split `P = P₁ ∪ P₂` as in `MassSplit`.
  set P₂ : Finset ℕ := (Nat.primesBelow (u + 1)).filter (fun p ↦ Y < p) with hP₂
  set P₁ : Finset ℕ := Nat.primesBelow (Y + 1) with hP₁
  set P : Finset ℕ := P₁ ∪ P₂ with hP
  set Filt : Finset ℕ := (Finset.range (u + 1)).filter (fun n ↦ s ≤
    ∑ p ∈ n.primeFactors.filter (fun p ↦ Y < p), n.factorization p) with hFilt
  have hz0 : (0 : ℝ) < z := one_pos.trans_le hz
  have hP₁mem : ∀ p ∈ P₁, p.Prime ∧ p ≤ Y := by
    intro p hp
    have h := Nat.mem_primesBelow.mp (hP₁ ▸ hp)
    exact ⟨h.2, by omega⟩
  have hP₂mem : ∀ p ∈ P₂, p.Prime ∧ Y < p ∧ p < u + 1 := by
    intro p hp
    have h := Finset.mem_filter.mp (hP₂ ▸ hp)
    have h' := Nat.mem_primesBelow.mp h.1
    exact ⟨h'.2, h.2, h'.1⟩
  have hdisj : Disjoint P₁ P₂ := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (hP₁mem p hp1).2
    have h2 := (hP₂mem p hp2).2.1
    omega
  have hprimeP : ∀ p ∈ P, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp (hP ▸ hp) with hp1 | hp2
    · exact (hP₁mem p hp1).1
    · exact (hP₂mem p hp2).1
  have hsupp : ∀ a ∈ Finset.range (u + 1), a ≠ 0 →
      ∀ p ∈ a.primeFactors, p ∈ P := by
    intro a haX ha0 p hp
    have hpa : p ≤ a :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) (Nat.dvd_of_mem_primeFactors hp)
    have hpX : p < u + 1 := lt_of_le_of_lt hpa (Finset.mem_range.mp haX)
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [hP]
    rcases le_or_gt p Y with h | h
    · exact Finset.mem_union_left _
        (hP₁ ▸ Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩)
    · exact Finset.mem_union_right _
        (hP₂ ▸ Finset.mem_filter.mpr
          ⟨Nat.mem_primesBelow.mpr ⟨hpX, hprime⟩, h⟩)
  have hwP₁ : ∀ p ∈ P₁, massWeight Y z p = 1 / (p : ℝ) :=
    fun p hp ↦ if_pos (hP₁mem p hp).2
  have hwP₂ : ∀ p ∈ P₂, massWeight Y z p = z / (p : ℝ) := fun p hp ↦ by
    have h := (hP₂mem p hp).2.1
    exact if_neg (by omega)
  have hw_nonneg : ∀ p ∈ P, 0 ≤ massWeight Y z p := by
    intro p hp
    rcases Finset.mem_union.mp (hP ▸ hp) with hp1 | hp2
    · rw [hwP₁ p hp1]; positivity
    · rw [hwP₂ p hp2]; exact div_nonneg hz0.le (Nat.cast_nonneg _)
  have hw_lt : ∀ p ∈ P, massWeight Y z p < 1 := by
    intro p hp
    rcases Finset.mem_union.mp (hP ▸ hp) with hp1 | hp2
    · rw [hwP₁ p hp1]
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (hP₁mem p hp1).1.two_le
      calc (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
        _ < 1 := by norm_num
    · rw [hwP₂ p hp2]
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (hP₂mem p hp2).1.two_le
      have hpos : (0 : ℝ) < (p : ℝ) := by linarith
      rw [div_lt_iff₀ hpos, one_mul]
      have hYp : (Y : ℝ) < (p : ℝ) := by
        exact_mod_cast (hP₂mem p hp2).2.1
      linarith
  have hsum := sum_factorization_prod_le (u + 1) P (massWeight Y z)
    hprimeP hw_nonneg hw_lt
  -- `∑_{p ∈ P₂} a.factorization p` equals the `Y`-rough `Ω`-sum of `a`.
  have hS₂ : ∀ a ∈ Finset.range (u + 1), a ≠ 0 →
      (∑ p ∈ P₂, a.factorization p) =
        ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p), a.factorization p := by
    intro a haX ha0
    have haX' : a < u + 1 := Finset.mem_range.mp haX
    symm
    apply Finset.sum_subset
    · intro p hp
      rw [Finset.mem_filter] at hp
      rw [hP₂, Finset.mem_filter]
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp.1
      have hpa : p ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0)
        (Nat.dvd_of_mem_primeFactors hp.1)
      exact ⟨Nat.mem_primesBelow.mpr ⟨lt_of_le_of_lt hpa haX', hprime⟩, hp.2⟩
    · intro p hp2 hpn
      have hprime : p.Prime := (hP₂mem p hp2).1
      have hYp : Y < p := (hP₂mem p hp2).2.1
      have hnpf : p ∉ a.primeFactors := fun hpf ↦
        hpn (Finset.mem_filter.mpr ⟨hpf, hYp⟩)
      exact Nat.factorization_eq_zero_of_not_dvd (fun hdvd ↦
        hnpf (Nat.mem_primeFactors.mpr ⟨hprime, hdvd, ha0⟩))
  -- Key identity: `∏_{p ∈ P} w p ^ (a.factorization p) = z^{Ω_{>Y}(a)} / a`.
  have hkey : ∀ a ∈ (Finset.range (u + 1)).filter (fun a ↦ a ≠ 0),
      ∏ p ∈ P, massWeight Y z p ^ a.factorization p =
        z ^ (∑ p ∈ P₂, a.factorization p) / (a : ℝ) := by
    intro a ha
    have haX : a < u + 1 := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have ha0 : a ≠ 0 := (Finset.mem_filter.mp ha).2
    have hsupp_a : ∀ p ∈ a.primeFactors, p ∈ P :=
      hsupp a (Finset.mem_range.mpr haX) ha0
    have hself : ∏ p ∈ a.primeFactors, p ^ a.factorization p = a :=
      Nat.prod_factorization_pow_eq_self ha0
    have hprodP : ∏ p ∈ P, (p : ℝ) ^ a.factorization p = (a : ℝ) := by
      have hsub2 : ∏ p ∈ a.primeFactors, (p : ℝ) ^ a.factorization p =
          ∏ p ∈ P, (p : ℝ) ^ a.factorization p :=
        Finset.prod_subset hsupp_a fun p hpP hpn ↦ by
          rw [Nat.factorization_eq_zero_of_not_dvd
            (fun hdvd ↦ hpn (Nat.mem_primeFactors.mpr
              ⟨hprimeP p hpP, hdvd, ha0⟩)), pow_zero]
      rw [← hsub2, ← hself]
      norm_cast
    have hA : ∏ p ∈ P₁, massWeight Y z p ^ a.factorization p =
        (∏ p ∈ P₁, (p : ℝ) ^ a.factorization p)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [hwP₁ p hp, one_div, inv_pow]
    have hB : ∏ p ∈ P₂, massWeight Y z p ^ a.factorization p =
        z ^ (∑ p ∈ P₂, a.factorization p) /
          (∏ p ∈ P₂, (p : ℝ) ^ a.factorization p) := by
      calc ∏ p ∈ P₂, massWeight Y z p ^ a.factorization p
          = ∏ p ∈ P₂, (z / (p : ℝ)) ^ a.factorization p :=
            Finset.prod_congr rfl fun p hp ↦ by rw [hwP₂ p hp]
        _ = ∏ p ∈ P₂, z ^ a.factorization p / (p : ℝ) ^ a.factorization p :=
            Finset.prod_congr rfl fun p hp ↦ by rw [div_pow]
        _ = (∏ p ∈ P₂, z ^ a.factorization p) /
              ∏ p ∈ P₂, (p : ℝ) ^ a.factorization p :=
            Finset.prod_div_distrib
        _ = z ^ (∑ p ∈ P₂, a.factorization p) /
              ∏ p ∈ P₂, (p : ℝ) ^ a.factorization p := by
            rw [Finset.prod_pow_eq_pow_sum]
    have huv : (∏ p ∈ P₁, (p : ℝ) ^ a.factorization p) *
        ∏ p ∈ P₂, (p : ℝ) ^ a.factorization p = (a : ℝ) := by
      have h := hprodP
      rw [hP, Finset.prod_union hdisj] at h
      exact h
    rw [hP, Finset.prod_union hdisj, hA, hB]
    calc (∏ p ∈ P₁, (p : ℝ) ^ a.factorization p)⁻¹ *
          (z ^ (∑ p ∈ P₂, a.factorization p) /
            ∏ p ∈ P₂, (p : ℝ) ^ a.factorization p)
        = z ^ (∑ p ∈ P₂, a.factorization p) *
            ((∏ p ∈ P₁, (p : ℝ) ^ a.factorization p)⁻¹ *
              (∏ p ∈ P₂, (p : ℝ) ^ a.factorization p)⁻¹) := by
          rw [div_eq_mul_inv]; ring
      _ = z ^ (∑ p ∈ P₂, a.factorization p) /
            ((∏ p ∈ P₁, (p : ℝ) ^ a.factorization p) *
              ∏ p ∈ P₂, (p : ℝ) ^ a.factorization p) := by
          rw [← mul_inv, ← div_eq_mul_inv]
      _ = z ^ (∑ p ∈ P₂, a.factorization p) / (a : ℝ) := by rw [huv]
  -- Members of `Filt` are nonzero (their `Ω_{>Y}` is `≥ s ≥ 1`).
  have hn_ne : ∀ n ∈ Filt, n ≠ 0 := by
    intro n hn hn0
    have hle := (Finset.mem_filter.mp (hFilt ▸ hn)).2
    subst hn0
    rw [Nat.primeFactors_zero, Finset.filter_empty, Finset.sum_empty] at hle
    omega
  -- Pointwise Markov bound: `z^s / u ≤ z^{Ω_{>Y}(n)} / n` on `Filt`.
  have hpt : ∀ n ∈ Filt, z ^ s / (u : ℝ) ≤
      ∏ p ∈ P, massWeight Y z p ^ n.factorization p := by
    intro n hn
    have hnm := Finset.mem_filter.mp (hFilt ▸ hn)
    have hnX : n < u + 1 := Finset.mem_range.mp hnm.1
    have hle := hnm.2
    have hn0 : n ≠ 0 := hn_ne n hn
    have hkeyn := hkey n (Finset.mem_filter.mpr ⟨hnm.1, hn0⟩)
    rw [hkeyn, hS₂ n hnm.1 hn0]
    have hpow : z ^ s ≤ z ^ (∑ p ∈ n.primeFactors.filter (fun p ↦ Y < p),
        n.factorization p) := pow_le_pow_right₀ hz hle
    have hnpos : (0 : ℝ) < (n : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hnu : (n : ℝ) ≤ (u : ℝ) := by
      have : n ≤ u := by omega
      exact_mod_cast this
    calc z ^ s / (u : ℝ) ≤ z ^ s / (n : ℝ) :=
          div_le_div_of_nonneg_left (pow_nonneg hz0.le s) hnpos hnu
      _ ≤ z ^ (∑ p ∈ n.primeFactors.filter (fun p ↦ Y < p),
            n.factorization p) / (n : ℝ) :=
          (div_le_div_iff_of_pos_right hnpos).mpr hpow
  -- Sum the pointwise bound and apply the finite Euler-product bound.
  have hle_prod : ∑ n ∈ Filt,
      ∏ p ∈ P, massWeight Y z p ^ n.factorization p ≤
      ∏ p ∈ P, (1 - massWeight Y z p)⁻¹ := by
    refine le_trans ?_ hsum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      have hnm := Finset.mem_filter.mp (hFilt ▸ hn)
      exact Finset.mem_filter.mpr ⟨hnm.1, hn_ne n hn, hsupp n hnm.1 (hn_ne n hn)⟩
    · intro n _ _
      exact Finset.prod_nonneg fun p hp ↦ pow_nonneg (hw_nonneg p hp) _
  have hupos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hlow : (Filt.card : ℝ) * (z ^ s / (u : ℝ)) ≤
      ∏ p ∈ P, (1 - massWeight Y z p)⁻¹ := by
    calc (Filt.card : ℝ) * (z ^ s / (u : ℝ))
        = ∑ n ∈ Filt, z ^ s / (u : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Filt, ∏ p ∈ P, massWeight Y z p ^ n.factorization p :=
          Finset.sum_le_sum hpt
      _ ≤ _ := hle_prod
  have hcard : (Filt.card : ℝ) * z ^ s ≤
      (u : ℝ) * ∏ p ∈ P, (1 - massWeight Y z p)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hlow hupos.le
    rw [← mul_assoc, div_mul_cancel₀ _ hupos.ne'] at h
    exact h.trans_eq (mul_comm _ _)
  have hcard' : (Filt.card : ℝ) ≤
      (u : ℝ) * (z ^ s)⁻¹ * ∏ p ∈ P, (1 - massWeight Y z p)⁻¹ := by
    have hspos : (0 : ℝ) < z ^ s := pow_pos hz0 s
    calc (Filt.card : ℝ)
        = Filt.card * z ^ s * (z ^ s)⁻¹ := by
          rw [mul_inv_cancel_right₀ hspos.ne']
      _ ≤ ((u : ℝ) * ∏ p ∈ P, (1 - massWeight Y z p)⁻¹) * (z ^ s)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hspos.le)
      _ = (u : ℝ) * (z ^ s)⁻¹ * ∏ p ∈ P, (1 - massWeight Y z p)⁻¹ := by ring
  -- Factor `∏_{p ∈ P} (1 - w p)⁻¹` over `P₁` and `P₂`.
  have hprod : ∏ p ∈ P, (1 - massWeight Y z p)⁻¹ =
      (∏ p ∈ P₁, (1 - (1 : ℝ) / p)⁻¹) *
        ∏ p ∈ P₂, (1 - z / (p : ℝ))⁻¹ := by
    rw [hP, Finset.prod_union hdisj]
    congr 1
    · exact Finset.prod_congr rfl fun p hp ↦ by rw [hwP₁ p hp]
    · exact Finset.prod_congr rfl fun p hp ↦ by rw [hwP₂ p hp]
  -- `z/p ≤ 1/2` on `P₂` since `2z ≤ Y < p`, giving the exponential bound.
  have hprod2 : ∏ p ∈ P₂, (1 - z / (p : ℝ))⁻¹ ≤
      Real.exp (2 * z * ∑ p ∈ P₂, (1 : ℝ) / p) := by
    calc ∏ p ∈ P₂, (1 - z / (p : ℝ))⁻¹
        ≤ ∏ p ∈ P₂, Real.exp (2 * (z / (p : ℝ))) := by
          apply Finset.prod_le_prod
          · intro p hp
            apply inv_nonneg.mpr
            have h2 : (2 : ℝ) ≤ (p : ℝ) := by
              exact_mod_cast (hP₂mem p hp).1.two_le
            have hpos : (0 : ℝ) < (p : ℝ) := by linarith
            have hYp : (Y : ℝ) < (p : ℝ) := by
              exact_mod_cast (hP₂mem p hp).2.1
            rw [sub_nonneg, div_le_one₀ hpos]
            linarith
          · intro p hp
            have h2 : (2 : ℝ) ≤ (p : ℝ) := by
              exact_mod_cast (hP₂mem p hp).1.two_le
            have hpos : (0 : ℝ) < (p : ℝ) := by linarith
            have hYp : (Y : ℝ) < (p : ℝ) := by
              exact_mod_cast (hP₂mem p hp).2.1
            apply inv_one_sub_le_exp_two_mul (div_nonneg hz0.le
              (Nat.cast_nonneg _))
            rw [div_le_iff₀ hpos]
            linarith
        _ = Real.exp (∑ p ∈ P₂, 2 * (z / (p : ℝ))) := by
          rw [← Real.exp_sum]
        _ = Real.exp (2 * z * ∑ p ∈ P₂, (1 : ℝ) / p) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
  have hP₁nonneg : 0 ≤ ∏ p ∈ P₁, (1 - (1 : ℝ) / p)⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (hP₁mem p hp).1.two_le
    apply inv_nonneg.mpr
    have hpos : (0 : ℝ) < (p : ℝ) := by linarith
    have h1p : (1 : ℝ) / p ≤ 1 := by
      rw [div_le_one₀ hpos]
      linarith
    linarith
  have hQle : ∏ p ∈ P, (1 - massWeight Y z p)⁻¹ ≤
      (∏ p ∈ P₁, (1 - (1 : ℝ) / p)⁻¹) *
        Real.exp (2 * z * ∑ p ∈ P₂, (1 : ℝ) / p) := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_left hprod2 hP₁nonneg
  have hzs : (z ^ s)⁻¹ = z ^ (-(s : ℝ)) := by
    rw [Real.rpow_neg hz0.le, Real.rpow_natCast]
  calc (Filt.card : ℝ)
      ≤ (u : ℝ) * (z ^ s)⁻¹ * ∏ p ∈ P, (1 - massWeight Y z p)⁻¹ := hcard'
    _ ≤ (u : ℝ) * (z ^ s)⁻¹ * ((∏ p ∈ P₁, (1 - (1 : ℝ) / p)⁻¹) *
          Real.exp (2 * z * ∑ p ∈ P₂, (1 : ℝ) / p)) :=
        mul_le_mul_of_nonneg_left hQle
          (mul_nonneg (Nat.cast_nonneg _)
            (inv_nonneg.mpr (pow_pos hz0 s).le))
    _ = (u : ℝ) * z ^ (-(s : ℝ)) * (∏ p ∈ P₁, (1 - (1 : ℝ) / p)⁻¹) *
          Real.exp (2 * z * ∑ p ∈ P₂, (1 : ℝ) / p) := by
        rw [← hzs]; ring

#print axioms card_bigOmega_ge_le

end JSP361
