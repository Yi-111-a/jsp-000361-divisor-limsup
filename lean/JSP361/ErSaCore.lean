import JSP361.Defs
import JSP361.Basic
import JSP361.Counting
import JSP361.CountA
import JSP361.Mertens
import JSP361.MertensLow
import JSP361.MassSplit
import JSP361.OmegaTail
import JSP361.TupleSum
import JSP361.ErSaAsympt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.IntervalCases

/-!
# JSP-000361 — the Erdős–Sárközy Part-II core lemma

This is the analytic heart of the theorem: at a scale `x` where the
reciprocal sum `f(x) = recipSum A x` exceeds `exp(√(log log x))`, there
is an integer `n ≤ exp(8 (log x)²)` with
`dA A n > exp((e/32)·(log f(x))²)`.

The paper's argument (ErSa80 Part II, §3, proving
`D_A(u) > exp((e/16 − ε)(log f(x))²)` for `u = x^{⌊log x⌋}`):

* Let `F = f(x)`, `L = ll x`, `y = exp((log F)³)`, `r = ⌊log x⌋`, and let
  `t ∈ (1, L)` solve `(eL/t)^t = (log F)⁴` (exists by IVT since
  `g(1) = eL < (log F)⁴` and `g(L) = e^L = log x > (log F)⁴`).
* `A* = {a ∈ A ∩ [1,x) : ω(a, y) > t}` where `ω(a,y)` counts prime factors
  `> y` with multiplicity.  Lemma 2 (reciprocal bound for `ω(·,y) < t`)
  gives `f_{A∖A*}(x) ≤ c·log y·(eL/t)^{t/2} = c·(log F)⁵ ≪ F/2`, hence
  `f_{A*}(x) ≥ F/2`.
* `S = {n ≤ x^r : n = a₁⋯a_r·m, a_i ∈ A*}`; the representation count
  `T = #{(tuple, m)} ≥ (x^r/2)·(F/2)^r` (from `⌊u⌋ ≥ u/2`), while
  `ρ(n) ≤ d_A(n)^r ≤ D^r` for `n ≤ x^r`.
* `|S| ≤ x^r·exp(−c·r·t·L)`: the `S₁` part (large repeated-prime part,
  `ω+(n,y) − ν+(n,y) > rt/12`) via the convergent squarefull reciprocal
  series at threshold `y^{rt/12}`; the `S₂` part via the Norton–Rankin
  tail `#{n ≤ u : ν(n, y, u) ≥ s} ≤ c·u·exp((α−1−α log α)·E)` with
  `E = ∑_{y<p≤u} 1/p ≈ 2L`.
* Combining: `D^r ≥ T/|S| ≥ (F/2)^r·exp(c·r·t·L)/4`, hence
  `D ≥ (F/4)·exp(c·t·L)`, and `t·L ≈ 4·log log F·L/log L` beats
  `(e/32)(log F)²` in the regime `log F ≲ L/(3k)`.

CAUTION (reconstruction status): the constant bookkeeping in the last
step is delicate; the regime `log F ≈ L` (ultra-dense `A`) may need a
separate argument.  Keep the statement fixed: any constant `0 < c` in
place of `e/32` and any fixed exponent `J` in place of `8` is acceptable
— report changes.

Formalization notes: we take `Y = ⌈e^{L+3}⌉`, `r = ⌊log x⌋`, `u = x^r`,
`E' = ∑_{Y < p < x} 1/p`, `S = E' + 1`, and `t` from `ersa_params`
(satisfying `t·log(2eS/t) ≤ lf/2` and `t·(L − log L − 8) ≥
(e/64)·lf² + log 16 + 1`).  The large-Ω subset `B ⊆ A` below `x`
contributes `fst ≥ F/2` (the complement mass is `≤ e⁶(L+4)·e^{lf/2}
≤ F/4` by `recipSum_le_of_largeOmegaFac_le`), and the tail bound
`card_bigOmega_ge_le` at `z = r(t+1)/(2E'')` gives
`dA(n)^r ≥ fst^r·u/(2·u·z^{-s}·P_Y·e^{2zE''}) = fst^r·(z/e)^{t+1}/(2P_Y)`,
whose `t`-dependent factor beats `exp((e/64)·lf²)` via `ersa_params`.
-/

namespace JSP361

open Finset
open scoped Classical

set_option maxHeartbeats 3200000 in
/-- **ErSa80 Part II core.**  At a scale `x` with
`f(x) = recipSum A x > exp(√(log log x))`, some `n ≤ exp(8 (log x)²)` has
`dA A n > exp((e/64)·(log f(x))²)`.  (Constant `e/64` chosen for formalization
margin; any `c > 0` suffices for the application in `CaseB`.) -/
theorem ersa_core (A : Set ℕ) (hA : A.Infinite) {x : ℕ}
    (hx : (100000 : ℝ) ≤ Real.log (Real.log (x : ℝ)))
    (hf : Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ)))) < recipSum A x) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (8 * (Real.log (x : ℝ)) ^ 2) ∧
      Real.exp ((Real.exp 1 / 64) * (Real.log (recipSum A x)) ^ 2)
        < (dA A n : ℝ) := by
  classical
  -- ===== abbreviations =====
  set L : ℝ := Real.log (Real.log (x : ℝ)) with hLd
  set lx : ℝ := Real.log (x : ℝ) with hlxd
  set F : ℝ := recipSum A x with hFd
  set lf : ℝ := Real.log F with hlfd
  -- ===== coarse bounds =====
  have hL : (100000 : ℝ) ≤ L := by rw [hLd]; exact hx
  have hLpos : (0 : ℝ) < L := by linarith
  have hf' : Real.exp (Real.sqrt L) < F := by rw [hLd, hFd]; exact hf
  have hFpos : (0 : ℝ) < F := (Real.exp_pos _).trans hf'
  have hFgt1 : (1 : ℝ) < F := by
    have h1 : (0:ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hLpos
    have h2 : Real.exp 0 < Real.exp (Real.sqrt L) := Real.exp_lt_exp.mpr h1
    rw [Real.exp_zero] at h2
    linarith
  have hlf_low : Real.sqrt L < lf := by
    have h := Real.log_lt_log (Real.exp_pos _) hf'
    rw [Real.log_exp] at h
    rw [hlfd]; exact h
  -- ===== x ≥ 16, lx = log x ≥ 10 =====
  have hx2 : 2 ≤ x := by
    by_contra h
    push_neg at h
    interval_cases x
    · rw [hLd, hlxd] at hL
      simp only [Nat.cast_zero, Real.log_zero] at hL
      norm_num at hL
    · rw [hLd, hlxd] at hL
      simp only [Nat.cast_one, Real.log_one, Real.log_zero] at hL
      norm_num at hL
  have hxr : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlx_pos : (0:ℝ) < lx := by
    rw [hlxd]
    exact Real.log_pos (by exact_mod_cast (by omega : (1:ℕ) < x))
  have hloglx : Real.log lx = L := by rw [hlxd, ← hLd]
  have hlx_exp : lx = Real.exp L := by
    have h := Real.exp_log hlx_pos
    rw [hloglx] at h
    exact h.symm
  have hlx_ge : (10 : ℝ) ≤ lx := by
    have h := Real.add_one_le_exp (100000 : ℝ)
    rw [hlx_exp]
    linarith [Real.exp_le_exp.mpr hL]
  have hx_exp : (x:ℝ) = Real.exp lx := by
    have h := Real.exp_log hxr
    rw [← hlxd] at h
    exact h.symm
  have hx16 : 16 ≤ x := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
    have h3 : (Real.exp 1)^10 ≤ Real.exp 10 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h4 : (16:ℝ) ≤ Real.exp 10 :=
      le_trans (by norm_num : (16:ℝ) ≤ 2^10) (pow_le_pow_left₀ (by norm_num) h2 10 |>.trans h3)
    have h5 : Real.exp 10 ≤ Real.exp lx := Real.exp_le_exp.mpr hlx_ge
    have h6 : (16:ℝ) ≤ (x:ℝ) := by rw [hx_exp]; linarith [h4, h5]
    exact_mod_cast h6
  -- ===== sqrt/log estimates for L =====
  have he3 : (19 : ℝ) ≤ Real.exp 3 := by
    have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      simpa using (Real.exp_nat_mul (1 : ℝ) 3)
    rw [h3]
    calc (19:ℝ) ≤ (2.7:ℝ)^3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  have hsqrtL : (256 : ℝ) ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 256) hLpos.le).mpr
    have hsq : (256:ℝ)^2 = 65536 := by norm_num
    linarith [hsq, hL]
  have hLexp : L ≤ Real.exp (Real.sqrt L / 4) := by
    have h1 : Real.sqrt L / 16 + 1 ≤ Real.exp (Real.sqrt L / 16) :=
      Real.add_one_le_exp _
    have h2 : Real.exp (Real.sqrt L / 4) = (Real.exp (Real.sqrt L / 16)) ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [h2]
    have h3 : (Real.sqrt L) ^ 4 = L ^ 2 := by
      have h := Real.sq_sqrt hLpos.le
      have h4 : (Real.sqrt L) ^ 4 = ((Real.sqrt L) ^ 2) ^ 2 := by ring
      rw [h4, h]
    calc L ≤ L ^ 2 / 65536 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 65536)]
          nlinarith [hL, hLpos]
        _ = (Real.sqrt L / 16) ^ 4 := by rw [div_pow, h3]; norm_num
        _ ≤ (Real.exp (Real.sqrt L / 16)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hlogL : Real.log L ≤ Real.sqrt L / 4 := by
    have h := Real.log_le_log hLpos hLexp
    rwa [Real.log_exp] at h
  have h4logL : 4 * Real.log L + 30 ≤ L / 2 := by
    have h1 : 4 * Real.log L ≤ Real.sqrt L := by linarith
    have h2 : 4 * Real.sqrt L ≤ L := by
      have h4 : (4:ℝ) ≤ Real.sqrt L := by linarith [hsqrtL]
      calc 4 * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
            mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg L)
        _ = L := Real.mul_self_sqrt hLpos.le
    linarith
  -- ===== Y = ⌈e^{L+3}⌉ =====
  set Y : ℕ := ⌈Real.exp (L + 3)⌉₊ with hYd
  have hY_lower : Real.exp (L + 3) ≤ (Y : ℝ) := by
    rw [hYd]; exact Nat.le_ceil _
  have hY_upper : (Y : ℝ) ≤ Real.exp (L + 3) + 1 := by
    rw [hYd]
    exact (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
  have hY19 : (19 : ℝ) ≤ (Y : ℝ) :=
    le_trans (le_trans he3 (Real.exp_le_exp.mpr (by linarith : (3:ℝ) ≤ L + 3))) hY_lower
  have hYpos : 0 < Y := by
    have h : (0:ℝ) < (Y:ℝ) := by linarith [hY19]
    exact_mod_cast h
  have hY16 : 16 ≤ Y := by
    exact_mod_cast (by linarith [hY19] : (16:ℝ) ≤ (Y:ℝ))
  have hY1le : (Y:ℝ) + 1 ≤ Real.exp (L + 4) := by
    have h1 : (Y:ℝ) + 1 ≤ Real.exp (L + 3) + 2 := by linarith [hY_upper]
    have h2 : (2:ℝ) ≤ Real.exp (L + 3) :=
      le_trans (by linarith : (2:ℝ) ≤ Real.exp 3)
        (Real.exp_le_exp.mpr (by linarith : (3:ℝ) ≤ L + 3))
    have h3 : Real.exp (L + 3) + 2 ≤ Real.exp 1 * Real.exp (L + 3) := by
      have he : (2:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
      nlinarith [h2, he, Real.exp_pos (L + 3)]
    calc (Y:ℝ) + 1 ≤ Real.exp (L + 3) + 2 := h1
      _ ≤ Real.exp 1 * Real.exp (L + 3) := h3
      _ = Real.exp (L + 4) := by rw [← Real.exp_add]; congr 1; ring
  have hlogY : Real.log (Y : ℝ) ≤ L + 4 := by
    have hle : (Y:ℝ) ≤ Real.exp (L + 4) := by linarith [hY1le]
    calc Real.log (Y:ℝ) ≤ Real.log (Real.exp (L + 4)) :=
          Real.log_le_log (by exact_mod_cast hYpos) hle
      _ = L + 4 := Real.log_exp _
  have hlogY1 : Real.log (Real.log ((Y:ℝ) + 1)) ≤ Real.log (L + 4) := by
    apply Real.log_le_log
    · exact Real.log_pos (by linarith [hY19] : (1:ℝ) < (Y:ℝ) + 1)
    · calc Real.log ((Y:ℝ) + 1) ≤ Real.log (Real.exp (L + 4)) :=
            Real.log_le_log (by linarith [hY19] : (0:ℝ) < (Y:ℝ) + 1) hY1le
        _ = L + 4 := Real.log_exp _
  have hL4 : Real.log (L + 4) ≤ Real.log L + 1 := by
    have h1 : L + 4 ≤ 2 * L := by linarith [hLpos]
    calc Real.log (L + 4) ≤ Real.log (2 * L) :=
          Real.log_le_log (by linarith) h1
      _ = Real.log 2 + Real.log L := Real.log_mul two_ne_zero hLpos.ne'
      _ ≤ Real.log L + 1 := by linarith [Real.log_two_lt_d9]
  -- ===== E' = ∑_{Y<p<x} 1/p and S = E'+1 =====
  set E' : ℝ := ∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ Y < p), (1:ℝ)/p with hE'd
  have hE'_le : E' ≤ 4 * L + 20 := by
    have h1 : E' ≤ ∑ p ∈ Nat.primesBelow x, (1:ℝ)/p := by
      rw [hE'd]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun p _ _ ↦ by positivity
    have h2 := sum_prime_recip_le_loglog x hx16
    rw [← hLd] at h2
    linarith
  have hge : L - 6 ≤ ∑ p ∈ Nat.primesBelow x, (1:ℝ)/p := by
    have h := sum_prime_recip_ge x hx16
    rwa [← hLd] at h
  have hle_small : ∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ p ≤ Y), (1:ℝ)/p ≤
      4 * Real.log L + 24 := by
    calc ∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ p ≤ Y), (1:ℝ)/p
        ≤ ∑ p ∈ Nat.primesBelow (Y+1), (1:ℝ)/p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_filter] at hp
            exact Nat.mem_primesBelow.mpr
              ⟨Nat.lt_succ_iff.mpr hp.2, (Nat.mem_primesBelow.mp hp.1).2⟩
          · intro p _ _
            positivity
      _ ≤ 4 * Real.log (Real.log ((Y+1:ℕ):ℝ)) + 20 :=
          sum_prime_recip_le_loglog (Y+1) (by omega)
      _ ≤ 4 * Real.log L + 24 := by
          have h : Real.log (Real.log ((Y+1:ℕ):ℝ)) ≤ Real.log (L+4) := by
            simp only [Nat.cast_add, Nat.cast_one]
            exact hlogY1
          linarith [h, hL4]
  have hE'ge : L - 4 * Real.log L - 30 ≤ E' := by
    have hsplit : ∑ p ∈ Nat.primesBelow x, (1:ℝ)/p =
        ∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ p ≤ Y), (1:ℝ)/p + E' := by
      rw [hE'd]
      have hc : ((Nat.primesBelow x).filter (fun p ↦ Y < p)) =
          (Nat.primesBelow x).filter (fun p ↦ ¬ p ≤ Y) :=
        Finset.filter_congr fun p _ ↦ not_le.symm
      rw [hc, ← Finset.sum_filter_add_sum_filter_not (Nat.primesBelow x)
        (fun p ↦ p ≤ Y)]
    linarith
  set S : ℝ := E' + 1 with hSd
  have hSpos : (0:ℝ) < S := by rw [hSd]; linarith [hE'ge, h4logL]
  have hS_ge : L / 2 ≤ S := by rw [hSd]; linarith [hE'ge, h4logL]
  have hS_le : S ≤ 6 * L := by rw [hSd]; linarith [hE'_le, hL]
  -- ===== bounds on lf = log F =====
  have hF_le : F ≤ 1 + lx := by
    have h := recipSum_le_log A x
    rw [← hlxd] at h
    rw [hFd]; exact h
  have hlf_up : lf ≤ L + 1 := by
    have h1 : lf ≤ Real.log (1 + lx) := by
      rw [hlfd]
      exact Real.log_le_log hFpos hF_le
    have h2 : (1:ℝ) + lx ≤ 2 * lx := by linarith [hlx_ge]
    have h3 : Real.log (1 + lx) ≤ Real.log (2 * lx) :=
      Real.log_le_log (by linarith) h2
    have h4 : Real.log (2 * lx) = Real.log 2 + L := by
      rw [Real.log_mul two_ne_zero hlx_pos.ne', hloglx]
    linarith [h1, h3, h4, Real.log_two_lt_d9]
  -- ===== parameter t =====
  obtain ⟨t, ht1, htS, hcost, hgain⟩ := ersa_params hL hlf_low hlf_up hS_ge hS_le
  have htr : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
  have ht2 : (2:ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [htr]
  -- ===== r = ⌊log x⌋, u = x^r =====
  set r : ℕ := ⌊lx⌋₊ with hrd
  have hr_le : (r:ℝ) ≤ lx := by rw [hrd]; exact Nat.floor_le hlx_pos.le
  have hr_gt : lx - 1 ≤ (r:ℝ) := by
    have h := Nat.lt_floor_add_one lx
    rw [← hrd] at h
    linarith
  have hr1 : 1 ≤ r := by
    have h : (1:ℝ) ≤ (r:ℝ) := by linarith [hr_gt, hlx_ge]
    exact_mod_cast h
  have hrr : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  set u : ℕ := x ^ r with hud
  have hupos : 0 < u := by rw [hud]; exact pow_pos (by omega) r
  have hu1 : 1 ≤ u := hupos
  have hxu : x ≤ u := by
    rw [hud]
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ r := Nat.pow_le_pow_right (by omega) hr1
  -- ===== E'' = ∑_{Y<p≤u} 1/p =====
  set E'' : ℝ := ∑ p ∈ (Nat.primesBelow (u + 1)).filter (fun p ↦ Y < p), (1:ℝ)/p
    with hE''d
  have hlogu1 : Real.log ((u:ℝ) + 1) ≤ 1 + lx ^ 2 := by
    have hu1' : (1:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu1
    have h1 : (u:ℝ) + 1 ≤ 2 * (u:ℝ) := by linarith
    have h2 : Real.log ((u:ℝ) + 1) ≤ Real.log (2 * (u:ℝ)) :=
      Real.log_le_log (by linarith) h1
    have h3 : Real.log (2 * (u:ℝ)) = Real.log 2 + (r:ℝ) * lx := by
      rw [Real.log_mul two_ne_zero (Nat.cast_pos.mpr hupos).ne']
      congr 1
      rw [hud, Nat.cast_pow, Real.log_pow, hlxd]
    have h5 : (r:ℝ) * lx ≤ lx * lx :=
      mul_le_mul_of_nonneg_right hr_le hlx_pos.le
    nlinarith [h2, h3, h5, Real.log_two_lt_d9]
  have hllu : Real.log (Real.log ((u:ℝ) + 1)) ≤ 1 + 2 * L := by
    have hpos : (0:ℝ) < Real.log ((u:ℝ) + 1) := by
      apply Real.log_pos
      have h : (1:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu1
      linarith
    have hsq : (1:ℝ) ≤ lx^2 := by nlinarith [hlx_ge]
    have h1 : Real.log ((u:ℝ)+1) ≤ 2 * lx^2 := by linarith [hlogu1]
    have h2 : Real.log (Real.log ((u:ℝ)+1)) ≤ Real.log (2 * lx^2) :=
      Real.log_le_log hpos h1
    have h3 : Real.log (2 * lx^2) = Real.log 2 + 2 * L := by
      have hne : lx^2 ≠ 0 := pow_ne_zero 2 hlx_pos.ne'
      rw [Real.log_mul two_ne_zero hne, Real.log_pow, hloglx]
      push_cast
      ring
    rw [h3] at h2
    linarith [Real.log_two_lt_d9]
  have hE''le : E'' ≤ 8 * L + 24 := by
    have h1 : E'' ≤ ∑ p ∈ Nat.primesBelow (u+1), (1:ℝ)/p := by
      rw [hE''d]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun p _ _ ↦ by positivity
    have h2 : ∑ p ∈ Nat.primesBelow (u+1), (1:ℝ)/p ≤
        4 * Real.log (Real.log ((u+1:ℕ):ℝ)) + 20 :=
      sum_prime_recip_le_loglog (u+1) (by omega)
    have h3 : Real.log (Real.log ((u+1:ℕ):ℝ)) = Real.log (Real.log ((u:ℝ)+1)) := by
      simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hE'le_E'' : E' ≤ E'' := by
    rw [hE'd, hE''d]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      have hpx : p < x := (Nat.mem_primesBelow.mp hp.1).1
      have hpu : p < u + 1 := lt_of_lt_of_le hpx (Nat.le_trans hxu (Nat.le_succ u))
      exact ⟨Nat.mem_primesBelow.mpr ⟨hpu, (Nat.mem_primesBelow.mp hp.1).2⟩, hp.2⟩
    · intro p _ _
      positivity
  have hE''ge : L / 2 ≤ E'' := by linarith [hE'le_E'', h4logL]
  have hE''pos : (0:ℝ) < E'' := by linarith [hLpos]
  have hE''0 : E'' ≠ 0 := hE''pos.ne'
  -- ===== P_Y = ∏_{p ≤ Y} (1 - 1/p)⁻¹ =====
  set PY : ℝ := ∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1:ℝ)/p)⁻¹ with hPYd
  have hPYpos : (0:ℝ) < PY := by
    rw [hPYd]
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hp2' : (1:ℝ)/p ≤ 1/2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hp2
    rw [inv_pos]
    linarith
  have hPY1 : (1:ℝ) ≤ PY := by
    rw [hPYd]
    apply Finset.one_le_prod₀
    intro p hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hp2' : (1:ℝ)/p ≤ 1/2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hp2
    have hpos : (0:ℝ) < 1 - (1:ℝ)/p := by linarith
    rw [inv_eq_one_div, one_le_div hpos]
    have hnn : (0:ℝ) ≤ (1:ℝ)/p := by positivity
    linarith
  have hPYle : PY ≤ Real.exp 25 * (L + 4) ^ 4 := by
    have h := prod_primesBelow_le Y hY16
    have h2 : (Real.log (Y:ℝ)) ^ 4 ≤ (L + 4) ^ 4 :=
      pow_le_pow_left₀
        (Real.log_nonneg (by linarith [hY19] : (1:ℝ) ≤ (Y:ℝ))) hlogY 4
    calc PY = ∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1:ℝ)/p)⁻¹ := hPYd
      _ ≤ Real.exp 25 * (Real.log (Y:ℝ)) ^ 4 := h
      _ ≤ Real.exp 25 * (L + 4) ^ 4 :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hlogPY : Real.log PY ≤ 30 + 4 * Real.log L := by
    have h1 : Real.log PY ≤ Real.log (Real.exp 25 * (Real.log (Y:ℝ)) ^ 4) := by
      apply Real.log_le_log hPYpos
      rw [hPYd]
      exact prod_primesBelow_le Y hY16
    have hlogYpos : (0:ℝ) < Real.log (Y:ℝ) :=
      Real.log_pos (by linarith [hY19] : (1:ℝ) < (Y:ℝ))
    have h2 : Real.log (Real.exp 25 * (Real.log (Y:ℝ)) ^ 4)
        = 25 + 4 * Real.log (Real.log (Y:ℝ)) := by
      rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hlogYpos 4).ne',
          Real.log_exp, Real.log_pow]
      push_cast
      ring
    have h3 : Real.log (Real.log (Y:ℝ)) ≤ Real.log (L + 4) :=
      Real.log_le_log hlogYpos hlogY
    linarith [h1, h2, h3, hL4]
  -- `8·log L + 61 ≤ √L` for `L ≥ 2^16`, via `s = L^{1/16} ≥ 2`.
  have hbig : 8 * Real.log L + 61 ≤ Real.sqrt L := by
    set s : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt L))) with hsd
    -- `s^16 = L` and `s ≥ 2`
    have hs2 : s * s = Real.sqrt (Real.sqrt (Real.sqrt L)) := by
      rw [hsd]; exact Real.mul_self_sqrt (Real.sqrt_nonneg _)
    have hs4 : s ^ 4 = Real.sqrt (Real.sqrt L) := by
      calc s ^ 4 = (s * s) * (s * s) := by ring
        _ = Real.sqrt (Real.sqrt (Real.sqrt L)) *
              Real.sqrt (Real.sqrt (Real.sqrt L)) := by rw [hs2]
        _ = Real.sqrt (Real.sqrt L) :=
            Real.mul_self_sqrt (Real.sqrt_nonneg _)
    have hs8 : s ^ 8 = Real.sqrt L := by
      calc s ^ 8 = (s ^ 4) * (s ^ 4) := by ring
        _ = Real.sqrt (Real.sqrt L) * Real.sqrt (Real.sqrt L) := by rw [hs4]
        _ = Real.sqrt L := Real.mul_self_sqrt (Real.sqrt_nonneg L)
    have hs16 : s ^ 16 = L := by
      calc s ^ 16 = (s ^ 8) * (s ^ 8) := by ring
        _ = Real.sqrt L * Real.sqrt L := by rw [hs8]
        _ = L := Real.mul_self_sqrt hLpos.le
    have hsge2 : (2:ℝ) ≤ s := by
      by_contra hlt
      push_neg at hlt
      have hs0 : (0:ℝ) ≤ s := by rw [hsd]; exact Real.sqrt_nonneg _
      have h16 : s ^ 16 < (2:ℝ) ^ 16 :=
        pow_lt_pow_left₀ hlt hs0 (by norm_num : (16:ℕ) ≠ 0)
      rw [hs16] at h16
      norm_num at h16
      linarith [hL]
    have hlogs : Real.log s ≤ s - 1 :=
      Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < s)
    have hlogs16 : Real.log s = Real.log L / 16 := by
      have e1 : Real.log (Real.sqrt L) = Real.log L / 2 :=
        Real.log_sqrt hLpos.le
      have e2 : Real.log (Real.sqrt (Real.sqrt L)) = Real.log L / 4 := by
        rw [Real.log_sqrt (Real.sqrt_nonneg _), e1]; ring
      have e3 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt L))) = Real.log L / 8 := by
        rw [Real.log_sqrt (Real.sqrt_nonneg _), e2]; ring
      rw [hsd, Real.log_sqrt (Real.sqrt_nonneg _), e3]; ring
    have hlogL' : Real.log L ≤ 16 * (s - 1) := by linarith [hlogs, hlogs16]
    have hs7 : (128:ℝ) ≤ s ^ 7 := by
      calc (128:ℝ) = 2 ^ 7 := by norm_num
        _ ≤ s ^ 7 := pow_le_pow_left₀ (by norm_num) hsge2 7
    have hstep : (128:ℝ) * s ≤ s ^ 8 := by
      calc (128:ℝ) * s ≤ s ^ 7 * s :=
            mul_le_mul_of_nonneg_right hs7 (by linarith : (0:ℝ) ≤ s)
        _ = s ^ 8 := by ring
    calc 8 * Real.log L + 61 ≤ 8 * (16 * (s - 1)) + 61 := by linarith [hlogL']
      _ = 128 * s - 67 := by ring
      _ ≤ s ^ 8 := by linarith [hstep]
      _ = Real.sqrt L := hs8
  -- ===== the complement-mass bound =====
  have hwt : (2 * Real.exp 1 * S / (t:ℝ)) ^ t ≤ Real.exp (lf / 2) := by
    have hpos : (0:ℝ) < 2 * Real.exp 1 * S / (t:ℝ) :=
      div_pos (mul_pos (mul_pos two_pos (Real.exp_pos 1)) hSpos)
        (by linarith : (0:ℝ) < (t:ℝ))
    have h1 : Real.log ((2 * Real.exp 1 * S / (t:ℝ)) ^ t) =
        (t:ℝ) * Real.log (2 * Real.exp 1 * S / (t:ℝ)) := Real.log_pow _ _
    have h2 : (2 * Real.exp 1 * S / (t:ℝ)) ^ t =
        Real.exp ((t:ℝ) * Real.log (2 * Real.exp 1 * S / (t:ℝ))) := by
      rw [← h1]
      exact (Real.exp_log (pow_pos hpos t)).symm
    rw [h2]
    exact Real.exp_le_exp.mpr hcost
  have hOm_eq : ∀ a : ℕ, a ≠ 0 → a < x →
      (∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p), a.factorization p) =
      (∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ Y < p), a.factorization p) := by
    intro a ha0 hax
    apply Finset.sum_subset
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp.1
      exact ⟨Nat.mem_primesBelow.mpr
        ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0)
          (Nat.dvd_of_mem_primeFactors hp.1)) hax, hpP⟩, hp.2⟩
    · intro p hpbig hpnmem
      rw [Finset.mem_filter] at hpbig
      have hpP : p.Prime := (Nat.mem_primesBelow.mp hpbig.1).2
      rw [Finset.mem_filter] at hpnmem
      by_contra hne
      have hdvd : p ∣ a := Nat.dvd_of_factorization_pos hne
      exact hpnmem ⟨Nat.mem_primeFactors.mpr ⟨hpP, hdvd, ha0⟩, hpbig.2⟩
  -- ===== B and fst =====
  set B : Finset ℕ := (Finset.range x).filter (fun a ↦ a ∈ A ∧
      t + 1 ≤ ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p), a.factorization p) with hBd
  set fst : ℝ := ∑ a ∈ B, (1:ℝ)/a with hfstd
  set comp : ℝ := ∑ a ∈ ((Finset.range x).filter (· ∈ A \ {0})).filter
      (fun a ↦ ¬(t + 1 ≤ ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p),
        a.factorization p)), (1:ℝ)/a with hcompd
  have hBA : ∀ a ∈ B, a ∈ A := by
    intro a ha
    rw [hBd] at ha
    exact (Finset.mem_filter.mp ha).2.1
  have hBlt : ∀ a ∈ B, a < x := by
    intro a ha
    rw [hBd] at ha
    exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hOm : ∀ a ∈ B, t + 1 ≤
      ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p), a.factorization p := by
    intro a ha
    rw [hBd] at ha
    exact (Finset.mem_filter.mp ha).2.2
  have hB1 : ∀ a ∈ B, 1 ≤ a := by
    intro a ha
    have hΩ := hOm a ha
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [Nat.primeFactors_zero, Finset.filter_empty, Finset.sum_empty] at hΩ
      omega
    · exact hpos
  have hTB : ((Finset.range x).filter (· ∈ A \ {0})).filter
      (fun a ↦ t + 1 ≤ ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p),
        a.factorization p) = B := by
    rw [hBd]
    apply Finset.ext
    intro a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hax, hmem⟩, hΩ⟩
      obtain ⟨haA, ha0⟩ := hmem
      exact ⟨hax, haA, hΩ⟩
    · rintro ⟨hax, haA, hΩ⟩
      refine ⟨⟨hax, ?_⟩, hΩ⟩
      constructor
      · exact haA
      · rw [Set.mem_singleton_iff]
        intro h0
        rw [h0] at hΩ
        rw [Nat.primeFactors_zero, Finset.filter_empty, Finset.sum_empty] at hΩ
        omega
  have hFeq : F = fst + comp := by
    rw [hFd, hfstd, hcompd, recipSum_eq_sum_filter, ← hTB,
      ← Finset.sum_filter_add_sum_filter_not ((Finset.range x).filter (· ∈ A \ {0}))
        (fun a ↦ t + 1 ≤ ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p), a.factorization p)]
  have hcompMS : comp ≤ PY * (2 * Real.exp 1 * S / (t:ℝ)) ^ t := by
    have hsub : comp ≤ ∑ a ∈ Finset.range x,
        if (∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ Y < p), a.factorization p) ≤ t
          then (1:ℝ)/a else 0 := by
      rw [hcompd]
      have hcongr : ∀ a ∈ ((Finset.range x).filter (· ∈ A \ {0})).filter
          (fun a ↦ ¬(t + 1 ≤ ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p),
            a.factorization p)),
          (1:ℝ)/a = if (∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ Y < p),
            a.factorization p) ≤ t then (1:ℝ)/a else 0 := by
        intro a ha
        obtain ⟨haT, hnot⟩ := Finset.mem_filter.mp ha
        obtain ⟨hax, hmem⟩ := Finset.mem_filter.mp haT
        obtain ⟨haA, ha0⟩ := hmem
        have ha0' : a ≠ 0 := fun h0 ↦ ha0 (Set.mem_singleton_iff.mpr h0)
        have hlt : ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p),
            a.factorization p ≤ t := by omega
        rw [hOm_eq a ha0' (Finset.mem_range.mp hax)] at hlt
        rw [if_pos hlt]
      rw [Finset.sum_congr rfl hcongr]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
      · intro a _ _
        split_ifs <;> positivity
    refine hsub.trans ?_
    have htE' : (t:ℝ) ≤ (∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ Y < p),
        (1:ℝ)/p) + 1 := htS
    have h := recipSum_le_of_largeOmegaFac_le x Y t ht1 htE'
    rw [← hPYd, ← hE'd, ← hSd] at h
    exact h
  -- comp ≤ e²⁵(L+4)⁴·e^{lf/2} ≤ F/4
  have hcompF4 : comp ≤ F / 4 := by
    have hkey4 : Real.exp 25 * (L + 4) ^ 4 * Real.exp (lf / 2) ≤ F / 4 := by
      have hk : 4 * (Real.exp 25 * (L + 4) ^ 4) ≤ Real.exp (lf / 2) := by
        apply Real.le_exp_of_log_le
        have hpos : (0:ℝ) < Real.exp 25 * (L + 4) ^ 4 := by positivity
        rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hpos.ne',
            Real.log_mul (Real.exp_pos _).ne' (pow_pos (by linarith) 4).ne',
            Real.log_exp, Real.log_pow]
        have hlog4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
          norm_num
        -- `log 4 + (25 + 4·log(L+4)) ≤ √L/2` via `8·log L + 61 ≤ √L`
        have hb : Real.log 4 + (25 + 4 * Real.log (L+4)) ≤ Real.sqrt L / 2 := by
          have h1 : Real.log (L + 4) ≤ Real.log L + 1 := hL4
          linarith [hlog4, Real.log_two_lt_d9, h1, hbig, hLpos]
        push_cast
        linarith [hb, hlf_low]
      have hnn : (0:ℝ) ≤ Real.exp (lf/2) := (Real.exp_pos _).le
      have hee : Real.exp (lf/2) * Real.exp (lf/2) = F := by
        rw [← Real.exp_add]
        have hh : lf/2 + lf/2 = lf := by ring
        rw [hh]
        exact Real.exp_log hFpos
      calc Real.exp 25 * (L+4) ^ 4 * Real.exp (lf/2)
          ≤ (Real.exp (lf/2)/4) * Real.exp (lf/2) := by
            have h : Real.exp 25 * (L+4) ^ 4 ≤ Real.exp (lf/2)/4 := by
              linarith [hk]
            exact mul_le_mul_of_nonneg_right h hnn
        _ = Real.exp (lf/2) * Real.exp (lf/2) / 4 := by ring
        _ = F / 4 := by rw [hee]
    calc comp ≤ PY * (2 * Real.exp 1 * S / (t:ℝ)) ^ t := hcompMS
      _ ≤ Real.exp 25 * (L + 4) ^ 4 * Real.exp (lf / 2) :=
          mul_le_mul hPYle hwt
            (pow_nonneg (div_nonneg
              (mul_nonneg (mul_nonneg two_pos.le (Real.exp_pos _).le) hSpos.le)
              (Nat.cast_nonneg t)) t)
            (mul_nonneg (Real.exp_pos _).le
              (pow_nonneg (by linarith [hLpos] : (0:ℝ) ≤ L + 4) 4))
      _ ≤ F / 4 := hkey4
  have hfst_ge : F / 2 ≤ fst := by linarith [hFeq, hFpos]
  have hfstpos : (0:ℝ) < fst := by linarith
  have hfst2 : (2:ℝ) ≤ fst := by
    have h2 : Real.exp 3 ≤ Real.exp (Real.sqrt L) :=
      Real.exp_le_exp.mpr (by linarith [hsqrtL])
    linarith [hf', h2, he3]
  have hfB : (2:ℝ) ≤ fst ^ r :=
    le_trans hfst2 (le_self_pow₀ (by linarith : (1:ℝ) ≤ fst) (by omega : r ≠ 0))
  -- ===== z and the tail bound =====
  have hsr_pos : (0:ℝ) < ((r * (t + 1) : ℕ) : ℝ) := by
    have h : (0:ℕ) < r * (t + 1) := mul_pos (by omega) (by omega)
    exact_mod_cast h
  set z : ℝ := ((r * (t + 1) : ℕ) : ℝ) / (2 * E'') with hzd
  have hzpos : (0:ℝ) < z := by
    rw [hzd]; exact div_pos hsr_pos (by linarith [hE''pos])
  have h2E0 : 2 * E'' ≠ 0 := mul_ne_zero two_ne_zero hE''0
  have hrr0 : (r:ℝ) ≠ 0 := hrpos.ne'
  have hzz : 2 * z * E'' = ((r * (t + 1) : ℕ) : ℝ) := by
    rw [hzd]
    field_simp
  have hz1 : (1:ℝ) ≤ z := by
    rw [hzd, one_le_div (by linarith [hE''pos] : (0:ℝ) < 2 * E'')]
    have h2 : (2:ℝ) * E'' ≤ 16 * L + 48 := by linarith [hE''le]
    have h3 : (16:ℝ) * L + 48 ≤ ((r * (t + 1) : ℕ) : ℝ) := by
      have h4 : (2:ℝ) * (r:ℝ) ≤ ((r * (t + 1) : ℕ) : ℝ) := by
        rw [Nat.cast_mul]
        have h6 := mul_le_mul_of_nonneg_left ht2 (Nat.cast_nonneg r)
        linarith [h6]
      have h7 : (16:ℝ)*L + 48 ≤ 2 * (lx - 1) := by
        have heL : L^2/4 ≤ Real.exp L := by
          have hh := Real.add_one_le_exp (L/2)
          have heq : Real.exp (L/2) * Real.exp (L/2) = Real.exp L := by
            rw [← Real.exp_add]; congr 1; ring
          have hmul := mul_le_mul hh hh (by linarith : (0:ℝ) ≤ L/2 + 1)
            (Real.exp_pos _).le
          rw [heq] at hmul
          nlinarith [hmul]
        rw [hlx_exp]
        nlinarith [heL, hL, hLpos]
      linarith [h4, h7, hr_gt]
    linarith [h2, h3]
  have hzy : 2 * z ≤ (Y:ℝ) := by
    have h2z : 2 * z = ((r * (t + 1) : ℕ) : ℝ) / E'' := by
      rw [hzd]
      field_simp
    have h1 : ((r * (t + 1) : ℕ) : ℝ) / E'' ≤ ((r * (t + 1) : ℕ) : ℝ) / (L/2) := by
      rw [div_le_div_iff₀ hE''pos (by linarith : (0:ℝ) < L/2)]
      exact mul_le_mul_of_nonneg_left hE''ge hsr_pos.le
    have h2 : ((r * (t + 1) : ℕ) : ℝ) / (L/2) ≤ 14 * lx := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < L/2)]
      have h3 : ((r * (t + 1) : ℕ) : ℝ) ≤ lx * (7 * L) := by
        rw [Nat.cast_mul]
        have ht7 : ((t + 1 : ℕ) : ℝ) ≤ 7 * L := by
          have h : ((t + 1 : ℕ) : ℝ) = (t:ℝ) + 1 := by push_cast; ring
          rw [h]
          linarith [htS, hS_le, hL]
        have hmul := mul_le_mul hr_le ht7 (Nat.cast_nonneg (t+1)) hlx_pos.le
        linarith [hmul]
      linarith [h3]
    calc 2 * z = ((r * (t + 1) : ℕ) : ℝ) / E'' := h2z
      _ ≤ ((r * (t + 1) : ℕ) : ℝ) / (L/2) := h1
      _ ≤ 14 * lx := h2
      _ ≤ Real.exp (L + 3) := by
        have h14 : (14:ℝ) ≤ Real.exp 3 := by linarith [he3]
        have h4 : Real.exp (L + 3) = Real.exp L * Real.exp 3 := Real.exp_add _ _
        rw [h4, ← hlx_exp]
        have h5 := mul_le_mul_of_nonneg_left h14 hlx_pos.le
        linarith [h5]
      _ ≤ (Y:ℝ) := hY_lower
  have hlogz : L - Real.log L - 4 ≤ Real.log z := by
    have hzz' : Real.log z = Real.log ((r * (t + 1) : ℕ) : ℝ) - Real.log (2 * E'') := by
      rw [hzd]
      exact Real.log_div hsr_pos.ne' (mul_ne_zero two_ne_zero hE''0)
    rw [hzz']
    have h1 : Real.log (2 * E'') ≤ Real.log (18 * L) := by
      apply Real.log_le_log (by linarith [hE''pos])
      linarith [hE''le]
    have h2 : Real.log (18 * L) = Real.log 18 + Real.log L :=
      Real.log_mul (by norm_num) hLpos.ne'
    have h3 : Real.log 18 ≤ 3 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 18)]
      calc (18:ℝ) ≤ 19 := by norm_num
        _ ≤ Real.exp 3 := he3
    have h4 : Real.log ((r:ℝ)) ≤ Real.log ((r * (t + 1) : ℕ) : ℝ) := by
      apply Real.log_le_log hrpos
      rw [Nat.cast_mul]
      have h6 := mul_le_mul_of_nonneg_left
        (by exact_mod_cast (by omega : (1:ℕ) ≤ t + 1) : (1:ℝ) ≤ ((t+1:ℕ):ℝ))
        (Nat.cast_nonneg r)
      linarith [h6]
    have h5 : L - Real.log 2 ≤ Real.log ((r:ℝ)) := by
      have h6 : lx / 2 ≤ (r:ℝ) := by linarith [hr_gt, hlx_ge]
      have h7 : Real.log (lx/2) ≤ Real.log ((r:ℝ)) :=
        Real.log_le_log (by linarith [hlx_pos]) h6
      have h8 : Real.log (lx/2) = L - Real.log 2 := by
        rw [Real.log_div hlx_pos.ne' two_ne_zero, hloglx]
      linarith [h7, h8]
    linarith [h4, h5, h1, h2, h3, Real.log_two_lt_d9]
  -- ===== combine: exists_dA_pow_ge + card_bigOmega_ge_le =====
  have hs1 : 1 ≤ r * (t + 1) := by
    calc (1:ℕ) = 1 * 1 := by norm_num
      _ ≤ r * (t+1) := Nat.mul_le_mul hr1 (by omega)
  have hcard := card_bigOmega_ge_le Y u (r * (t + 1)) hz1 hzy hs1
  rw [← hPYd, ← hE''d] at hcard
  have hSBpos : (0:ℝ) < (u:ℝ) * z ^ (-(((r * (t + 1)) : ℕ) : ℝ)) * PY *
      Real.exp (2 * z * E'') := by
    have h1 : (0:ℝ) < (u:ℝ) := Nat.cast_pos.mpr hupos
    have h2 : (0:ℝ) < z ^ (-(((r * (t + 1)) : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos hzpos _
    exact mul_pos (mul_pos (mul_pos h1 h2) hPYpos) (Real.exp_pos _)
  obtain ⟨n, hnle_u, hkey⟩ :=
    exists_dA_pow_ge A hr1 (by omega) hud hBA hBlt hB1 hOm hfB hSBpos hcard
  rw [← hfstd, hzz] at hkey
  -- cancel the `u` factor
  have hu0 : (u:ℝ) ≠ 0 := (Nat.cast_pos.mpr hupos).ne'
  have hPY0 : PY ≠ 0 := hPYpos.ne'
  have hzs0 : z ^ (((r * (t + 1)) : ℕ) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hzpos _).ne'
  have he0 : Real.exp (((r * (t + 1)) : ℕ) : ℝ) ≠ 0 := (Real.exp_pos _).ne'
  have hfrac : fst ^ r * (u:ℝ) /
      (2 * ((u:ℝ) * z ^ (-(((r * (t + 1)) : ℕ) : ℝ)) * PY *
        Real.exp (((r * (t + 1)) : ℕ) : ℝ)))
      = fst ^ r * z ^ (((r * (t + 1)) : ℕ) : ℝ) /
        (2 * PY * Real.exp (((r * (t + 1)) : ℕ) : ℝ)) := by
    rw [Real.rpow_neg hzpos.le]
    field_simp
  rw [hfrac] at hkey
  -- take logarithms
  have hnumpos : (0:ℝ) < fst ^ r * z ^ (((r * (t + 1)) : ℕ) : ℝ) :=
    mul_pos (pow_pos hfstpos _) (Real.rpow_pos_of_pos hzpos _)
  have hdenpos : (0:ℝ) < 2 * PY * Real.exp (((r * (t + 1)) : ℕ) : ℝ) :=
    mul_pos (mul_pos two_pos hPYpos) (Real.exp_pos _)
  have hlogK : Real.log (fst ^ r * z ^ (((r * (t + 1)) : ℕ) : ℝ) /
      (2 * PY * Real.exp (((r * (t + 1)) : ℕ) : ℝ))) =
      (r:ℝ) * Real.log fst + (((r * (t + 1)) : ℕ) : ℝ) * Real.log z
        - (Real.log 2 + Real.log PY + (((r * (t + 1)) : ℕ) : ℝ)) := by
    rw [Real.log_div hnumpos.ne' hdenpos.ne',
        Real.log_mul (pow_pos hfstpos _).ne' (Real.rpow_pos_of_pos hzpos _).ne',
        Real.log_mul (mul_ne_zero two_ne_zero hPY0) he0,
        Real.log_mul two_ne_zero hPY0,
        Real.log_pow, Real.log_rpow hzpos, Real.log_exp]
  have hdApos : (0:ℝ) < (dA A n : ℝ) := by
    by_contra h
    push_neg at h
    have h0 : (dA A n : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    have hz : (dA A n : ℝ) ^ r = 0 := by rw [h0]; exact zero_pow (by omega : r ≠ 0)
    have hpos : (0:ℝ) < fst^r * z^(((r * (t + 1)) : ℕ) : ℝ) /
        (2 * PY * Real.exp (((r * (t + 1)) : ℕ) : ℝ)) := div_pos hnumpos hdenpos
    linarith only [hkey, hz, hpos]
  have hlogdAr : (r:ℝ) * Real.log (dA A n : ℝ) ≥
      (r:ℝ) * Real.log fst + (((r * (t + 1)) : ℕ) : ℝ) * Real.log z
        - (Real.log 2 + Real.log PY + (((r * (t + 1)) : ℕ) : ℝ)) := by
    have h1 : Real.log ((dA A n : ℝ) ^ r) = (r:ℝ) * Real.log (dA A n : ℝ) :=
      Real.log_pow _ _
    have h2 := Real.log_le_log (div_pos hnumpos hdenpos) hkey
    linarith only [h1, h2, hlogK]
  have hsr : (((r * (t + 1)) : ℕ) : ℝ) / (r:ℝ) = (t:ℝ) + 1 := by
    rw [Nat.cast_mul]
    rw [mul_div_cancel_left₀ _ hrpos.ne']
    push_cast
    ring
  have h3eq : ((r:ℝ) * Real.log fst + (((r * (t + 1)) : ℕ) : ℝ) * Real.log z
        - (Real.log 2 + Real.log PY + (((r * (t + 1)) : ℕ) : ℝ))) / (r:ℝ)
      = Real.log fst + ((t:ℝ) + 1) * (Real.log z - 1)
        - (Real.log 2 + Real.log PY) / (r:ℝ) := by
    rw [← hsr]
    field_simp
    ring
  have hlogdA : Real.log (dA A n : ℝ) ≥
      Real.log fst + ((t:ℝ) + 1) * (Real.log z - 1)
        - (Real.log 2 + Real.log PY) / (r:ℝ) := by
    have h := (div_le_div_iff_of_pos_right hrpos).mpr hlogdAr
    rw [mul_div_cancel_left₀ _ hrpos.ne'] at h
    linarith only [h, h3eq]
  have hlogfst : lf - Real.log 2 ≤ Real.log fst := by
    have h : Real.log (F/2) ≤ Real.log fst :=
      Real.log_le_log (by linarith [hFpos]) hfst_ge
    have h2 : Real.log (F/2) = lf - Real.log 2 := by
      rw [Real.log_div hFpos.ne' two_ne_zero, ← hlfd]
    linarith only [h, h2]
  have htW : (t:ℝ) * (L - Real.log L - 8) + (L - Real.log L - 5)
      ≤ ((t:ℝ) + 1) * (Real.log z - 1) := by
    have h1 : L - Real.log L - 5 ≤ Real.log z - 1 := by linarith only [hlogz]
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ (t:ℝ) + 1)
    have h3 : (t:ℝ) * (L - Real.log L - 8) + (L - Real.log L - 5)
        ≤ ((t:ℝ) + 1) * (L - Real.log L - 5) := by
      nlinarith [(Nat.cast_nonneg t : (0:ℝ) ≤ (t:ℝ))]
    linarith only [h2, h3]
  have hdiv : (Real.log 2 + Real.log PY) / (r:ℝ) ≤ 31 + 4 * Real.log L := by
    have h5 : (0:ℝ) ≤ Real.log 2 + Real.log PY := by
      have h6 : (0:ℝ) ≤ Real.log PY := Real.log_nonneg hPY1
      linarith only [h6, Real.log_two_gt_d9]
    calc (Real.log 2 + Real.log PY)/(r:ℝ) ≤ Real.log 2 + Real.log PY :=
          div_le_self h5 hrr
      _ ≤ 31 + 4 * Real.log L := by linarith only [hlogPY, Real.log_two_lt_d9]
  have hfinal : Real.exp 1 / 64 * lf ^ 2 < Real.log (dA A n : ℝ) := by
    have hcomb : Real.log (dA A n : ℝ) ≥
        lf - Real.log 2 + ((t:ℝ) * (L - Real.log L - 8) + (L - Real.log L - 5))
          - (31 + 4 * Real.log L) := by linarith only [hlogdA, hlogfst, htW, hdiv]
    -- `L ≥ 5·log L + 40` via `L = √L·√L ≥ 256·√L ≥ 256·(4·log L + 61)/8`-style
    have hsqrtL' : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
    have h256 : 256 * Real.sqrt L ≤ L := by
      calc 256 * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
            mul_le_mul_of_nonneg_right hsqrtL (Real.sqrt_nonneg L)
        _ = L := hsqrtL'
    have hLdom : 5 * Real.log L + 40 ≤ L := by linarith only [h256, hlogL, hsqrtL]
    linarith only [hcomb, hgain, hlf_low, hsqrtL, hlogL, hL, hFpos, hLdom,
      Real.log_two_lt_d9, Real.log_nonneg (by norm_num : (1:ℝ) ≤ (16:ℝ))]
  -- ===== assemble =====
  refine ⟨n, ?_, ?_⟩
  · have hnle : (n:ℝ) ≤ (u:ℝ) := by exact_mod_cast hnle_u
    have hux : (u:ℝ) = Real.exp ((r:ℝ) * lx) := by
      rw [hud, Nat.cast_pow]
      have hpos : (0:ℝ) < (x:ℝ)^r := pow_pos hxr _
      calc ((x:ℝ)^r) = Real.exp (Real.log ((x:ℝ)^r)) := (Real.exp_log hpos).symm
        _ = Real.exp ((r:ℝ) * lx) := by rw [Real.log_pow, ← hlxd]
    calc (n:ℝ) ≤ (u:ℝ) := hnle
      _ = Real.exp ((r:ℝ) * lx) := hux
      _ ≤ Real.exp (8 * lx ^ 2) :=
          Real.exp_le_exp.mpr (by
            have h1 : (r:ℝ) * lx ≤ lx * lx :=
              mul_le_mul_of_nonneg_right hr_le hlx_pos.le
            linarith only [h1, sq_nonneg lx])
  · calc Real.exp (Real.exp 1 / 64 * lf ^ 2)
        < Real.exp (Real.log (dA A n : ℝ)) := Real.exp_lt_exp.mpr hfinal
      _ = (dA A n : ℝ) := Real.exp_log hdApos

end JSP361
