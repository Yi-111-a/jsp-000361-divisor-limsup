import JSP361.Defs
import JSP361.Mertens
import JSP361.MassSplit
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# JSP-000361 — elementary Mertens bounds for `∑ 1/p` and `∏ (1-1/p)⁻¹`

* `sum_one_div_le_prod_primesBelow`: the Euler-product inequality
  `∑_{n<x} 1/n ≤ ∏_{p<x}(1-1/p)⁻¹` (a corollary of
  `MassSplit.sum_factorization_prod_le` with `w p = 1/p`, since
  `∏_{p∈P} (1/p)^{a.factorization p} = 1/a`).
* `sum_prime_recip_ge`: `∑_{p<x} 1/p ≥ log log x − 6`
  (take logs of the Euler product and use
  `-log(1-1/p) ≤ 1/p + 1/(p(p-1))`, with `∑ 1/(p(p-1)) ≤ 1`).
* `prod_primesBelow_le`: `∏_{p≤Y}(1-1/p)⁻¹ ≤ e^25·(log Y)^4` from the existing
  upper bound `Mertens.sum_prime_recip_le_loglog`.
-/

namespace JSP361

open Finset

/-- `1/(n(n-1)) = 1/(n-1) - 1/n` for `2 ≤ n`, in `ℝ`. -/
private lemma one_div_mul_pred_eq {n : ℕ} (hn : 2 ≤ n) :
    (1:ℝ)/(n*(n-1)) = ((n:ℝ) - 1)⁻¹ - (n:ℝ)⁻¹ := by
  have hnn : (n:ℝ) ≠ 0 := by
    have h : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact h.ne'
  have hnm1 : (n:ℝ) - 1 ≠ 0 := by
    have h : (2:ℝ) ≤ n := by exact_mod_cast hn
    exact (by linarith : (0:ℝ) < (n:ℝ) - 1).ne'
  have hnm : (n:ℝ)*((n:ℝ) - 1) ≠ 0 := mul_ne_zero hnn hnm1
  field_simp
  ring

/-- Telescoping: `∑_{n ∈ Ico 2 (k+2)} 1/(n(n-1)) = 1 - 1/(k+1)`. -/
private lemma sum_Ico_pred_mul_eq (k : ℕ) :
    ∑ n ∈ Finset.Ico 2 (k+2), (1:ℝ)/(n*(n-1)) = 1 - (1:ℝ)/((k+1:ℕ):ℝ) := by
  induction k with
  | zero =>
    have he : Finset.Ico 2 (0+2) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    rw [he, Finset.sum_empty]
    norm_num
  | succ k ih =>
    have hsplit : ∑ n ∈ Finset.Ico 2 (k+1+2), (1:ℝ)/(n*(n-1))
        = ∑ n ∈ Finset.Ico 2 (k+2), (1:ℝ)/(n*(n-1))
          + (1:ℝ)/(((k+2 : ℕ) : ℝ)*(((k+2 : ℕ) : ℝ)-1)) := by
      have heq : k + 1 + 2 = (k+2)+1 := by omega
      rw [heq]
      exact Finset.sum_Ico_succ_top (by omega : 2 ≤ k+2)
        (fun n ↦ (1:ℝ)/(n*(n-1)))
    rw [hsplit, ih]
    have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
    have hk2 : ((k:ℝ)+2) ≠ 0 := by positivity
    push_cast
    rw [show ((k:ℝ)+2) - 1 = (k:ℝ) + 1 by ring,
        show ((k:ℝ)+1) + 1 = (k:ℝ) + 2 by ring]
    field_simp
    ring

/-- `∑_{n ∈ Ico 2 M} 1/(n(n-1)) ≤ 1`. -/
private lemma sum_Ico_pred_mul_le_one (M : ℕ) :
    ∑ n ∈ Finset.Ico 2 M, (1:ℝ)/(n*(n-1)) ≤ 1 := by
  rcases Nat.lt_or_ge M 2 with hM | hM
  · rw [Finset.Ico_eq_empty_of_le hM.le, Finset.sum_empty]
    norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
    rw [sum_Ico_pred_mul_eq]
    have hpos : (0:ℝ) ≤ (1:ℝ)/((k+1:ℕ):ℝ) := by positivity
    linarith

/-- `∑_{p ∈ P} 1/(p(p-1)) ≤ 1` when all elements of `P` lie in `[2, N]`. -/
private lemma sum_pred_mul_le_one {P : Finset ℕ} (N : ℕ)
    (h2 : ∀ p ∈ P, 2 ≤ p) (hN : ∀ p ∈ P, p ≤ N) :
    ∑ p ∈ P, (1:ℝ)/(p*(p-1)) ≤ 1 := by
  calc ∑ p ∈ P, (1:ℝ)/(p*(p-1))
      ≤ ∑ n ∈ Finset.Icc 2 N, (1:ℝ)/(n*(n-1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_Icc]
          exact ⟨h2 n hn, hN n hn⟩
        · intro n hn _
          rw [Finset.mem_Icc] at hn
          have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
          exact div_nonneg zero_le_one
            (mul_nonneg (Nat.cast_nonneg n) (by linarith))
    _ = ∑ n ∈ Finset.Ico 2 (N+1), (1:ℝ)/(n*(n-1)) := by
        rw [Finset.Ico_add_one_right_eq_Icc]
    _ ≤ 1 := sum_Ico_pred_mul_le_one (N+1)

/-- For `2 ≤ p`, `-log(1 - 1/p) ≤ 1/p + 1/(p(p-1))`. -/
private lemma neg_log_one_sub_le {p : ℕ} (hp : 2 ≤ p) :
    -Real.log (1 - (1:ℝ)/p) ≤ (1:ℝ)/p + 1/(p*(p-1)) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp
  have hp0 : (p:ℝ) ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hne : (p:ℝ) - 1 ≠ 0 := (sub_pos.mpr hp1).ne'
  have hpos : (0:ℝ) < 1 - (1:ℝ)/p := by
    rw [sub_pos, div_lt_one (zero_lt_one.trans hp1)]
    exact hp1
  have e1 : (1:ℝ) - 1/p = ((p:ℝ) - 1)/p := by
    rw [eq_div_iff hp0, sub_mul, one_mul, one_div, inv_mul_cancel₀ hp0]
  have e2 : (1 - (1:ℝ)/p)⁻¹ = 1 + ((p:ℝ)-1)⁻¹ := by
    rw [e1, inv_div, div_eq_iff hne, add_mul, one_mul, inv_mul_cancel₀ hne]
    ring
  have harg : (0:ℝ) < 1 + ((p:ℝ)-1)⁻¹ :=
    add_pos_of_pos_of_nonneg zero_lt_one (inv_nonneg.mpr (sub_pos.mpr hp1).le)
  have h := Real.log_le_sub_one_of_pos harg
  rw [← e2, Real.log_inv] at h
  -- h : -log(1-1/p) ≤ (1-1/p)⁻¹ - 1
  have e2m1 : (1 - (1:ℝ)/p)⁻¹ - 1 = ((p:ℝ)-1)⁻¹ := by rw [e2]; ring
  rw [e2m1] at h
  -- h : -log(1-1/p) ≤ (↑p-1)⁻¹
  have e3 : ((p:ℝ) - 1)⁻¹ = (1:ℝ)/p + 1/(p*(p-1)) := by
    have hpm : (p:ℝ)*((p:ℝ)-1) ≠ 0 := mul_ne_zero hp0 hne
    field_simp
    ring
  rwa [e3] at h

/-- For `a ≠ 0` whose prime factors all lie in the prime finset `P`,
`∏_{p ∈ P} (1/p)^{a.factorization p} = 1/a`. -/
private lemma prod_one_div_pow_factorization_eq {a : ℕ} (ha : a ≠ 0) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hPa : ∀ p ∈ a.primeFactors, p ∈ P) :
    ∏ p ∈ P, ((1:ℝ)/p) ^ a.factorization p = (1:ℝ)/a := by
  have hself : ∏ p ∈ a.primeFactors, p ^ a.factorization p = a :=
    Nat.prod_factorization_pow_eq_self ha
  rw [← Finset.prod_subset hPa (fun p hpP hpn ↦ by
    rw [Nat.factorization_eq_zero_of_not_dvd
      (fun hdvd ↦ hpn (Nat.mem_primeFactors.mpr ⟨hP p hpP, hdvd, ha⟩)), pow_zero])]
  have hcast : ∏ p ∈ a.primeFactors, ((p:ℝ)) ^ a.factorization p = (a:ℝ) := by
    exact_mod_cast hself
  calc ∏ p ∈ a.primeFactors, ((1:ℝ)/p) ^ a.factorization p
      = ∏ p ∈ a.primeFactors, ((p:ℝ) ^ a.factorization p)⁻¹ := by
        apply Finset.prod_congr rfl
        intro p _
        rw [one_div, inv_pow]
    _ = (∏ p ∈ a.primeFactors, (p:ℝ) ^ a.factorization p)⁻¹ :=
        Finset.prod_inv_distrib (fun p : ℕ ↦ (p:ℝ) ^ a.factorization p)
    _ = ((a:ℝ))⁻¹ := by rw [hcast]
    _ = (1:ℝ)/a := (one_div _).symm

/-- Euler-product lower bound for the harmonic sum. -/
theorem sum_one_div_le_prod_primesBelow (x : ℕ) :
    ∑ n ∈ Finset.range x, (1 : ℝ) / n
      ≤ ∏ p ∈ Nat.primesBelow x, (1 - (1 : ℝ) / p)⁻¹ := by
  classical
  have hP : ∀ p ∈ Nat.primesBelow x, p.Prime :=
    fun p hp ↦ Nat.prime_of_mem_primesBelow hp
  have hw0 : ∀ p ∈ Nat.primesBelow x, 0 ≤ (1:ℝ)/p :=
    fun p _ ↦ div_nonneg zero_le_one (Nat.cast_nonneg p)
  have hw1 : ∀ p ∈ Nat.primesBelow x, (1:ℝ)/p < 1 := by
    intro p hp
    have h2 : (1:ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    rwa [div_lt_one (zero_lt_one.trans h2)]
  have hmem : ∀ a ∈ Finset.range x, a ≠ 0 →
      a ∈ (Finset.range x).filter
        (fun a ↦ a ≠ 0 ∧ ∀ p ∈ a.primeFactors, p ∈ Nat.primesBelow x) := by
    intro a ha ha0
    rw [Finset.mem_filter]
    refine ⟨ha, ha0, fun p hp ↦ ?_⟩
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpdvd, _⟩ := hp
    exact Nat.mem_primesBelow.mpr
      ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hpdvd)
        (Finset.mem_range.mp ha), hpp⟩
  have hmain := sum_factorization_prod_le x (Nat.primesBelow x)
    (fun p ↦ (1:ℝ)/p) hP hw0 hw1
  have hsum : ∑ n ∈ Finset.range x, (1:ℝ)/n
      = ∑ a ∈ (Finset.range x).filter
          (fun a ↦ a ≠ 0 ∧ ∀ p ∈ a.primeFactors, p ∈ Nat.primesBelow x),
        (1:ℝ)/a := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) _).symm
    intro a ha haS
    have ha0 : a = 0 := by
      by_contra h0
      exact haS (hmem a ha h0)
    rw [ha0]
    norm_num
  rw [hsum]
  refine le_trans ?_ hmain
  apply Finset.sum_le_sum
  intro a ha
  obtain ⟨ha_range, ha0, hPa⟩ := Finset.mem_filter.mp ha
  exact le_of_eq (prod_one_div_pow_factorization_eq ha0 hP hPa).symm

/-- Lower Mertens bound: `∑_{p<x} 1/p ≥ log log x − 6`. -/
theorem sum_prime_recip_ge (x : ℕ) (hx : 16 ≤ x) :
    Real.log (Real.log (x : ℝ)) - 6
      ≤ ∑ p ∈ Nat.primesBelow x, (1 : ℝ) / p := by
  have hx1 : 1 ≤ x := by omega
  have hxR : (1:ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hlogx_pos : 0 < Real.log (x:ℝ) := Real.log_pos hxR
  have hlogx : Real.log (x:ℝ) ≤ ∑ n ∈ Finset.range x, (1:ℝ)/n := by
    have h := log_add_one_le_harmonic (x - 1)
    rw [Nat.sub_add_cancel hx1, harmonic_eq_sum_Icc] at h
    push_cast at h
    simp only [inv_eq_one_div] at h
    refine h.trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_Icc] at hn
      exact Finset.mem_range.mpr (by omega)
    · intro n _ _
      positivity
  have hprod := sum_one_div_le_prod_primesBelow x
  have hne : ∀ p ∈ Nat.primesBelow x, (1 - (1:ℝ)/p)⁻¹ ≠ 0 := by
    intro p hp
    have h1 : (1:ℝ) < p := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have h2 : (0:ℝ) < 1 - 1/p := by
      rw [sub_pos, div_lt_one (zero_lt_one.trans h1)]
      exact h1
    exact (inv_pos.mpr h2).ne'
  have hll : Real.log (Real.log (x:ℝ))
      ≤ ∑ p ∈ Nat.primesBelow x, -Real.log (1 - (1:ℝ)/p) := by
    have h1 : Real.log (Real.log (x:ℝ))
        ≤ Real.log (∏ p ∈ Nat.primesBelow x, (1 - (1:ℝ)/p)⁻¹) :=
      Real.log_le_log hlogx_pos (hlogx.trans hprod)
    rw [Real.log_prod hne] at h1
    simp only [Real.log_inv] at h1
    exact h1
  have hneg : ∑ p ∈ Nat.primesBelow x, -Real.log (1 - (1:ℝ)/p)
      ≤ ∑ p ∈ Nat.primesBelow x, (1:ℝ)/p + 1 := by
    calc ∑ p ∈ Nat.primesBelow x, -Real.log (1 - (1:ℝ)/p)
        ≤ ∑ p ∈ Nat.primesBelow x, ((1:ℝ)/p + 1/(p*(p-1))) := by
          apply Finset.sum_le_sum
          intro p hp
          exact neg_log_one_sub_le (Nat.prime_of_mem_primesBelow hp).two_le
      _ = ∑ p ∈ Nat.primesBelow x, (1:ℝ)/p
            + ∑ p ∈ Nat.primesBelow x, (1:ℝ)/(p*(p-1)) :=
          Finset.sum_add_distrib
      _ ≤ ∑ p ∈ Nat.primesBelow x, (1:ℝ)/p + 1 := by
          have h := sum_pred_mul_le_one (P := Nat.primesBelow x) (x - 1)
            (fun p hp ↦ (Nat.prime_of_mem_primesBelow hp).two_le)
            (fun p hp ↦ by
              have h := Nat.lt_of_mem_primesBelow hp
              omega)
          linarith
  linarith [hll, hneg]

/-- Upper Mertens product bound: `∏_{p≤Y}(1-1/p)⁻¹ ≤ e^25·(log Y)^4`. -/
theorem prod_primesBelow_le (Y : ℕ) (hY : 16 ≤ Y) :
    ∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1 : ℝ) / p)⁻¹
      ≤ Real.exp 25 * (Real.log (Y:ℝ))^4 := by
  have hY1 : (1:ℝ) < Y := by exact_mod_cast (by omega : 1 < Y)
  have hlogY : 0 < Real.log (Y:ℝ) := Real.log_pos hY1
  have hfact : ∀ p ∈ Nat.primesBelow (Y+1), (0:ℝ) < (1 - (1:ℝ)/p)⁻¹ := by
    intro p hp
    have h1 : (1:ℝ) < p := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    apply inv_pos.mpr
    rw [sub_pos, div_lt_one (zero_lt_one.trans h1)]
    exact h1
  have hprod_pos : 0 < ∏ p ∈ Nat.primesBelow (Y+1), (1 - (1:ℝ)/p)⁻¹ :=
    Finset.prod_pos (fun p hp ↦ hfact p hp)
  have hlog : Real.log (∏ p ∈ Nat.primesBelow (Y+1), (1 - (1:ℝ)/p)⁻¹)
      = ∑ p ∈ Nat.primesBelow (Y+1), -Real.log (1 - (1:ℝ)/p) := by
    rw [Real.log_prod (fun p hp ↦ (hfact p hp).ne')]
    apply Finset.sum_congr rfl
    intro p _
    rw [Real.log_inv]
  have hbound : ∑ p ∈ Nat.primesBelow (Y+1), -Real.log (1 - (1:ℝ)/p)
      ≤ ∑ p ∈ Nat.primesBelow (Y+1), (1:ℝ)/p + 1 := by
    calc ∑ p ∈ Nat.primesBelow (Y+1), -Real.log (1 - (1:ℝ)/p)
        ≤ ∑ p ∈ Nat.primesBelow (Y+1), ((1:ℝ)/p + 1/(p*(p-1))) := by
          apply Finset.sum_le_sum
          intro p hp
          exact neg_log_one_sub_le (Nat.prime_of_mem_primesBelow hp).two_le
      _ = ∑ p ∈ Nat.primesBelow (Y+1), (1:ℝ)/p
            + ∑ p ∈ Nat.primesBelow (Y+1), (1:ℝ)/(p*(p-1)) :=
          Finset.sum_add_distrib
      _ ≤ ∑ p ∈ Nat.primesBelow (Y+1), (1:ℝ)/p + 1 := by
          have h := sum_pred_mul_le_one (P := Nat.primesBelow (Y+1)) Y
            (fun p hp ↦ (Nat.prime_of_mem_primesBelow hp).two_le)
            (fun p hp ↦ by
              have h := Nat.lt_of_mem_primesBelow hp
              omega)
          linarith
  have hM : ∑ p ∈ Nat.primesBelow (Y+1), (1:ℝ)/p
      ≤ 4 * Real.log (Real.log ((Y+1:ℕ):ℝ)) + 20 :=
    sum_prime_recip_le_loglog (Y+1) (by omega)
  have hYp1 : Real.log ((Y+1:ℕ):ℝ) ≤ 2 * Real.log (Y:ℝ) := by
    have hle : ((Y+1:ℕ):ℝ) ≤ (Y:ℝ)^2 := by
      push_cast
      have hY2 : (2:ℝ) ≤ Y := by exact_mod_cast (by omega : 2 ≤ Y)
      nlinarith [hY2, mul_nonneg (Nat.cast_nonneg Y)
        (show (0:ℝ) ≤ (Y:ℝ) - 2 by linarith)]
    calc Real.log ((Y+1:ℕ):ℝ)
        ≤ Real.log ((Y:ℝ)^2) :=
          Real.log_le_log (by exact_mod_cast Nat.succ_pos Y) hle
      _ = 2 * Real.log (Y:ℝ) := by rw [Real.log_pow]; norm_num
  have hpos1 : 0 < Real.log ((Y+1:ℕ):ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : (1:ℕ) < Y+1)
  have hll : Real.log (Real.log ((Y+1:ℕ):ℝ))
      ≤ Real.log 2 + Real.log (Real.log (Y:ℝ)) := by
    calc Real.log (Real.log ((Y+1:ℕ):ℝ))
        ≤ Real.log (2 * Real.log (Y:ℝ)) := Real.log_le_log hpos1 hYp1
      _ = Real.log 2 + Real.log (Real.log (Y:ℝ)) :=
          Real.log_mul (by norm_num) (ne_of_gt hlogY)
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have htot : Real.log (∏ p ∈ Nat.primesBelow (Y+1), (1 - (1:ℝ)/p)⁻¹)
      ≤ 4 * Real.log (Real.log (Y:ℝ)) + 25 := by
    rw [hlog]
    linarith [hbound, hM, hll, hlog2]
  calc ∏ p ∈ Nat.primesBelow (Y+1), (1 - (1:ℝ)/p)⁻¹
      = Real.exp (Real.log (∏ p ∈ Nat.primesBelow (Y+1), (1 - (1:ℝ)/p)⁻¹)) :=
        (Real.exp_log hprod_pos).symm
    _ ≤ Real.exp (4 * Real.log (Real.log (Y:ℝ)) + 25) :=
        Real.exp_le_exp.mpr htot
    _ = Real.exp 25 * (Real.log (Y:ℝ))^4 := by
        rw [Real.exp_add]
        have e : Real.exp (4 * Real.log (Real.log (Y:ℝ)))
            = (Real.log (Y:ℝ))^4 := by
          rw [show (4:ℝ) * Real.log (Real.log (Y:ℝ))
              = Real.log ((Real.log (Y:ℝ))^4) by
            rw [Real.log_pow]; norm_num]
          exact Real.exp_log (pow_pos hlogY 4)
        rw [e, mul_comm]

end JSP361
