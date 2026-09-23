import JSP361.Record2
import JSP361.ErSaCore
import JSP361.Counting
import JSP361.Unbounded
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination

/-!
# JSP-000361 — Case B: `f` is somewhere larger than `exp(√(log log))`

Under the Case-B hypothesis

  `hB : ∀ U : ℕ, ∃ u : ℕ, U ≤ u ∧
        Real.exp (Real.sqrt (Real.log (Real.log u))) < recipSum A u`

(i.e. the negation of the Case-A hypothesis), prove the full limsup
statement for `k ≥ 1`, `C > 0`.

## Assembly recipe (constants: `c = e/32`, `J = 8` in `ersa_core`)

Set `K = 4 * √(k/c)` so that `K² = 16k/c` and `2k/K² = c/8`.

Choose `z ≥ 16` so large that for every `x ≥ z`:

* `ll x = log log x ≥ 16` (needed by `ersa_core`'s hypothesis);
* `K·√(ll x) ≥ B₁` where `B₁` satisfies
  `log C + k·log 9 < (7c/8)·B₁²` — e.g.
  `B₁ = √(8*(log C + k*log 9)/(7*c)) + 1` and `ll z ≥ (B₁/K)²`;
* `√(ll x) ≥ B₂` where `B₂` satisfies `log C + 4k·B₂ < c·B₂²` — e.g.
  `B₂ = (4k + √(16k² + 8c*max(log C,0)))/(2c) + 1`.

Then apply `caseB_dichotomy A hB (K := K) (z := z)`:

**Dense branch** (`f(x) > exp(K·√ll x)`):
`ersa_core` gives `n ≤ exp(8 (log x)²)` with
`dA n > exp(c (log f(x))²)`.  Then `n ≥ 1` (divisors nonempty since
`dA > 0`), and `f(n+1) ≤ 1 + log(n+1)` (`recipSum_le_log`) gives
`f(n+1) ≤ 9·(log x)² = 9·exp(2 ll x)` for `log x ≥ 1`.  With
`(log f(x))² > K²·ll x` and `K² = 16k/c`:
`C·f(n+1)^k ≤ C·9^k·exp(2k·ll x) ≤ C·9^k·exp((c/8)·(log f(x))²)`
`< exp(c·(log f(x))²) < dA A n` for `ll x` large enough (the `z` choice).

**Controlled branch** (`f(x) > exp(√ll x)` and
`f(w) ≤ f(x)^{2√(ll w/ll x)}` for all `w ≥ x`):
`ersa_core` at `x` gives `n ≤ exp(8(log x)²)`; then
`n + 1 ≤ exp(9(log x)²)` so `ll(n+1) ≤ log(9(log x)²) = log 9 + 2 ll x
≤ 3·ll x` (for `ll x ≥ 3`).  Hence for `w := n+1 ≥ x`:
`f(n+1) ≤ f(x)^{2√(ll(n+1)/ll x)} ≤ f(x)^{2√3} ≤ f(x)^4`
(the last since `f(x) > exp(√ll x) > 1`); if `n+1 ≤ x` then
`f(n+1) ≤ f(x) ≤ f(x)^4` anyway.  So `f(n+1) ≤ f(x)^4` and
`C·f(n+1)^k ≤ C·f(x)^{4k} < exp(c·(log f(x))²) < dA A n` since
`log f(x) > √ll x ≥ B₂` ensures `c·(log f)² > 4k·log f + log C`.

Conclude with `x := n + 1`, `n := n`.
-/

namespace JSP361

open Finset
open scoped Classical

set_option maxHeartbeats 3200000 in
/-- **Case B of the divergent branch.** If `recipSum A` is unbounded and
exceeds `exp(√(log log u))` at arbitrarily large `u`, the limsup bound
holds for every `k` and every `C > 0`. -/
theorem divisor_limsup_caseB (A : Set ℕ) (hA : A.Infinite)
    (hU : ∀ M : ℝ, ∃ x : ℕ, M < recipSum A x)
    (hB : ∀ U : ℕ, ∃ u : ℕ, U ≤ u ∧
      Real.exp (Real.sqrt (Real.log (Real.log (u : ℝ)))) < recipSum A u)
    (k : ℕ) (C : ℝ) (hC : 0 < C) :
    ∃ x : ℕ, ∃ n : ℕ, n < x ∧
      C * (recipSum A x) ^ k < (dA A n : ℝ) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- k = 0: dA is unbounded, so pick n with C < dA n and x = n + 1.
    subst hk0
    obtain ⟨n, hn⟩ := dA_unbounded A hA C
    exact ⟨n + 1, n, Nat.lt_succ_self n, by simpa using hn⟩
  · -- k ≥ 1.
    have hk0r : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
    have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkpos
    -- constants
    set c : ℝ := Real.exp 1 / 64 with hc_def
    have hc : 0 < c := by rw [hc_def]; positivity
    have hcn : c ≠ 0 := hc.ne'
    have hc1 : c ≤ 1 := by
      have h9 := Real.exp_one_lt_d9
      rw [hc_def, div_le_one (by norm_num : (0:ℝ) < 64)]
      linarith
    have hkc : (1:ℝ) ≤ (k:ℝ)/c := by
      rw [le_div_iff₀ hc]
      nlinarith [hc1, hk1, hc]
    set K : ℝ := 4 * Real.sqrt ((k:ℝ)/c) with hK_def
    have hK : (1:ℝ) ≤ K := by
      have hs : (1:ℝ) ≤ Real.sqrt ((k:ℝ)/c) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hkc
      rw [hK_def]; linarith
    have hK2 : K ^ 2 = 16 * (k:ℝ) / c := by
      have h0 : (0:ℝ) ≤ (k:ℝ)/c := div_nonneg (Nat.cast_nonneg k) hc.le
      rw [hK_def, mul_pow, Real.sq_sqrt h0]
      ring
    have hcK2 : c * K^2 = 16 * (k:ℝ) := by
      rw [hK2]
      exact mul_div_cancel₀ _ hcn
    -- constants controlling the choice of `z`
    set M : ℝ := max (Real.log C) 0 with hM_def
    have hMge : Real.log C ≤ M := le_max_left _ _
    have hM0 : (0:ℝ) ≤ M := le_max_right _ _
    set D : ℝ := 16 * (k:ℝ)^2 + 8 * c * M with hD_def
    have hD0 : 0 ≤ D := by
      rw [hD_def]
      exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg (mul_nonneg (by norm_num) hc.le) hM0)
    set B₂ : ℝ := (4*(k:ℝ) + Real.sqrt D)/(2*c) + 1 with hB2_def
    set Lmin : ℝ := max 100000
      (max ((Real.log C + (k:ℝ)*Real.log 10)/(14*(k:ℝ)) + 1) (B₂^2))
      with hLmin_def
    set z : ℕ := ⌈Real.exp (Real.exp Lmin)⌉₊ + 17 with hz_def
    have h2c : (0:ℝ) < 2*c := mul_pos (by norm_num) hc
    -- `B₂` dominates `4k/(2c)` and solves the quadratic inequality.
    have hB2ge : (4:ℝ)*(k:ℝ)/(2*c) ≤ B₂ := by
      have h1 : (4*(k:ℝ))/(2*c) ≤ (4*(k:ℝ) + Real.sqrt D)/(2*c) :=
        (div_le_div_iff_of_pos_right h2c).mpr (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      rw [hB2_def]; linarith
    have hB2pos : (0:ℝ) ≤ B₂ := by
      have h0 : (0:ℝ) ≤ 4*(k:ℝ)/(2*c) :=
        div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) h2c.le
      linarith [hB2ge]
    have hquad : Real.log C + 4*(k:ℝ)*B₂ ≤ c * B₂^2 := by
      set u : ℝ := (4*(k:ℝ) + Real.sqrt D)/(2*c) with hu_def
      have hB2eq : B₂ = u + 1 := by rw [hB2_def, hu_def]
      have he : 2*c*u = 4*(k:ℝ) + Real.sqrt D := by
        rw [hu_def, ← mul_div_assoc, mul_div_cancel_left₀ _ h2c.ne']
      have h2cu : 4*(k:ℝ) ≤ 2*c*u := by
        have h1 := Real.sqrt_nonneg D
        linarith [he]
      have hsq : (2*c*u - 4*(k:ℝ))^2 = 16*(k:ℝ)^2 + 8*c*M := by
        have e : 2*c*u - 4*(k:ℝ) = Real.sqrt D := by linarith [he]
        rw [e, Real.sq_sqrt hD0, hD_def]
      have hcu : c * u^2 = 4*(k:ℝ)*u + 2*M := by
        have h4c : (4*c) * (c * u^2) = (4*c) * (4*(k:ℝ)*u + 2*M) := by
          linear_combination hsq
        exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hcn) h4c
      rw [hB2eq]
      nlinarith [hcu, h2cu, hMge, hM0, hc]
    -- facts about `z`
    have hz16 : 16 ≤ z := by rw [hz_def]; omega
    have hzE : Real.exp (Real.exp Lmin) < (z:ℝ) := by
      have h1 := Nat.le_ceil (Real.exp (Real.exp Lmin))
      rw [hz_def]; push_cast; linarith
    have hLL_of_ge : ∀ x : ℕ, z ≤ x →
        Lmin < Real.log (Real.log (x:ℝ)) := by
      intro x hxz
      have hxzR : (z:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxz
      have hE : Real.exp (Real.exp Lmin) < (x:ℝ) := lt_of_lt_of_le hzE hxzR
      have h1 : Real.exp Lmin < Real.log (x:ℝ) := by
        have h2 := Real.log_lt_log (Real.exp_pos _) hE
        rwa [Real.log_exp] at h2
      have h3 := Real.log_lt_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h3
    have hll16 : ∀ x : ℕ, z ≤ x → (100000:ℝ) ≤ Real.log (Real.log (x:ℝ)) := by
      intro x hxz
      exact le_trans (le_max_left _ _) (hLL_of_ge x hxz).le
    have h14ineq : ∀ x : ℕ, z ≤ x →
        Real.log C + (k:ℝ) * Real.log 10 <
          14*(k:ℝ)*Real.log (Real.log (x:ℝ)) := by
      intro x hxz
      have hle : (Real.log C + (k:ℝ)*Real.log 10)/(14*(k:ℝ)) + 1 ≤ Lmin :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have hlt := lt_of_le_of_lt hle (hLL_of_ge x hxz)
      have hk14 : (0:ℝ) < 14*(k:ℝ) := mul_pos (by norm_num) hk0r
      have h4 : (Real.log C + (k:ℝ)*Real.log 10)/(14*(k:ℝ)) <
          Real.log (Real.log (x:ℝ)) := by linarith
      have h5 := (div_lt_iff₀ hk14).mp h4
      nlinarith [h5]
    have hB2ll : ∀ x : ℕ, z ≤ x →
        B₂ ≤ Real.sqrt (Real.log (Real.log (x:ℝ))) := by
      intro x hxz
      have hle : B₂^2 ≤ Real.log (Real.log (x:ℝ)) :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
          (hLL_of_ge x hxz).le
      calc B₂ = Real.sqrt (B₂^2) := (Real.sqrt_sq hB2pos).symm
        _ ≤ Real.sqrt (Real.log (Real.log (x:ℝ))) := Real.sqrt_le_sqrt hle
    -- apply the dichotomy
    rcases caseB_dichotomy A hB hK hz16 with ⟨x, hxz, hfx⟩ | ⟨x, hxz, hfx, hctrl⟩
    · -- DENSE BRANCH: `f x > exp (K·√ll x)`
      have hxzR : (z:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxz
      have hz17 : (17:ℝ) ≤ (z:ℝ) := by
        have h17 : (17:ℕ) ≤ z := by rw [hz_def]; omega
        exact_mod_cast h17
      have hx1 : (1:ℝ) < (x:ℝ) :=
        lt_of_lt_of_le (by norm_num) (hz17.trans hxzR)
      have hlogxpos : 0 < Real.log (x:ℝ) := Real.log_pos hx1
      have hll16x : (100000:ℝ) ≤ Real.log (Real.log (x:ℝ)) := hll16 x hxz
      have hlogx1 : (1:ℝ) ≤ Real.log (x:ℝ) := by
        have e : (1:ℝ) ≤ Real.exp (Real.log (Real.log (x:ℝ))) :=
          Real.one_le_exp_iff.mpr (le_trans (by norm_num) hll16x)
        rwa [Real.exp_log hlogxpos] at e
      -- `ersa_core` applies since `f x > exp(√ll)`.
      have hs0 : 0 ≤ Real.sqrt (Real.log (Real.log (x:ℝ))) := Real.sqrt_nonneg _
      have hf : Real.exp (Real.sqrt (Real.log (Real.log (x:ℝ)))) < recipSum A x :=
        lt_of_le_of_lt (Real.exp_le_exp.mpr (le_mul_of_one_le_left hs0 hK)) hfx
      obtain ⟨n, hnle, hdA⟩ := ersa_core A hA hll16x hf
      rw [← hc_def] at hdA
      have hdA0 : dA A 0 = 0 := by simp [dA]
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [hdA0, Nat.cast_zero] at hdA
        exact (lt_irrefl _ (lt_trans (Real.exp_pos _) hdA)).elim
      have hnle' : ((n+1:ℕ):ℝ) ≤ 2 * Real.exp (8 * (Real.log (x:ℝ))^2) := by
        push_cast
        have e1 : (1:ℝ) ≤ Real.exp (8 * (Real.log (x:ℝ))^2) :=
          Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) (sq_nonneg _))
        have hnleR : (n:ℝ) ≤ Real.exp (8 * (Real.log (x:ℝ))^2) := hnle
        calc (n:ℝ) + 1
            ≤ Real.exp (8 * (Real.log (x:ℝ))^2) +
                Real.exp (8 * (Real.log (x:ℝ))^2) := add_le_add hnleR e1
          _ = 2 * Real.exp (8 * (Real.log (x:ℝ))^2) := (two_mul _).symm
      have hlogn1 : Real.log ((n+1:ℕ):ℝ) ≤ Real.log 2 + 8 * (Real.log (x:ℝ))^2 := by
        have h2e : Real.log (2 * Real.exp (8 * (Real.log (x:ℝ))^2)) =
            Real.log 2 + 8 * (Real.log (x:ℝ))^2 := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
        calc Real.log ((n+1:ℕ):ℝ)
            ≤ Real.log (2 * Real.exp (8 * (Real.log (x:ℝ))^2)) :=
              Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos n)) hnle'
          _ = Real.log 2 + 8 * (Real.log (x:ℝ))^2 := h2e
      have hf1 : recipSum A (n+1) ≤ 10 * (Real.log (x:ℝ))^2 := by
        have h := recipSum_le_log A (n+1)
        have hL2 : (1:ℝ) ≤ (Real.log (x:ℝ))^2 := by
          have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hlogx1 2
          rwa [one_pow] at h2
        have hL9 : Real.log 2 ≤ (Real.log (x:ℝ))^2 :=
          Real.log_two_lt_d9.le.trans (le_trans (by norm_num) hL2)
        calc recipSum A (n+1)
            ≤ 1 + Real.log ((n+1:ℕ):ℝ) := h
          _ ≤ 1 + (Real.log 2 + 8 * (Real.log (x:ℝ))^2) :=
              add_le_add_right hlogn1 1
          _ ≤ 2 * (Real.log (x:ℝ))^2 + 8 * (Real.log (x:ℝ))^2 := by
              have hsum := add_le_add hL2 hL9
              linarith [hsum]
          _ = 10 * (Real.log (x:ℝ))^2 := by ring
      have hCk : C * (recipSum A (n+1))^k ≤ C * (10 * (Real.log (x:ℝ))^2)^k :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (recipSum_nonneg _ _) hf1 k) hC.le
      have hexp2k : (Real.log (x:ℝ))^(2*k) =
          Real.exp (2*(k:ℝ) * Real.log (Real.log (x:ℝ))) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hlogxpos]
        congr 1
        push_cast
        ring
      have h10k : (10 * (Real.log (x:ℝ))^2)^k =
          (10:ℝ)^k * Real.exp (2*(k:ℝ) * Real.log (Real.log (x:ℝ))) := by
        rw [mul_pow, ← pow_mul, hexp2k]
      -- `dA n > exp(16k·ll x)`
      have hlogf : K * Real.sqrt (Real.log (Real.log (x:ℝ))) <
          Real.log (recipSum A x) := by
        have h2 := Real.log_lt_log (Real.exp_pos _) hfx
        rwa [Real.log_exp] at h2
      have hKsq : (K * Real.sqrt (Real.log (Real.log (x:ℝ))))^2 =
          16 * (k:ℝ)/c * Real.log (Real.log (x:ℝ)) := by
        rw [mul_pow, Real.sq_sqrt (by linarith [hll16x]), hK2]
      have hlogfsq : 16*(k:ℝ)/c * Real.log (Real.log (x:ℝ)) <
          (Real.log (recipSum A x))^2 := by
        rw [← hKsq]
        have h0 : 0 ≤ K * Real.sqrt (Real.log (Real.log (x:ℝ))) :=
          mul_nonneg (by linarith [hK]) hs0
        exact pow_lt_pow_left₀ hlogf h0 (show (2:ℕ) ≠ 0 by norm_num)
      have hbig : 16*(k:ℝ)*Real.log (Real.log (x:ℝ)) <
          c * (Real.log (recipSum A x))^2 := by
        have hs' := mul_lt_mul_of_pos_left hlogfsq hc
        have e : c * (16*(k:ℝ)/c * Real.log (Real.log (x:ℝ))) =
            16*(k:ℝ)*Real.log (Real.log (x:ℝ)) := by
          rw [div_mul_eq_mul_div (16 * (k:ℝ)) c (Real.log (Real.log (x:ℝ)))]
          exact mul_div_cancel₀ _ hcn
        rwa [e] at hs'
      have hdense_exp : Real.exp (16*(k:ℝ)*Real.log (Real.log (x:ℝ))) <
          (dA A n : ℝ) :=
        lt_trans (Real.exp_lt_exp.mpr hbig) hdA
      -- `C·10^k·exp(2k·ll) < exp(16k·ll)` from the choice of `z`
      have hstep : C * (10:ℝ)^k * Real.exp (2*(k:ℝ)*Real.log (Real.log (x:ℝ))) <
          Real.exp (16*(k:ℝ)*Real.log (Real.log (x:ℝ))) := by
        have e : Real.exp (16*(k:ℝ)*Real.log (Real.log (x:ℝ))) =
            Real.exp (14*(k:ℝ)*Real.log (Real.log (x:ℝ))) *
            Real.exp (2*(k:ℝ)*Real.log (Real.log (x:ℝ))) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e]
        have h10 : (10:ℝ)^k = Real.exp ((k:ℝ) * Real.log 10) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 10)]
          congr 1; ring
        have hCe : C = Real.exp (Real.log C) := (Real.exp_log hC).symm
        have hsmall : C * (10:ℝ)^k <
            Real.exp (14*(k:ℝ)*Real.log (Real.log (x:ℝ))) := by
          rw [hCe, h10, ← Real.exp_add]
          exact Real.exp_lt_exp.mpr (h14ineq x hxz)
        exact mul_lt_mul_of_pos_right hsmall (Real.exp_pos _)
      have hC10 : C * (10 * (Real.log (x:ℝ))^2)^k < (dA A n : ℝ) := by
        rw [h10k, ← mul_assoc]
        exact lt_trans hstep hdense_exp
      exact ⟨n+1, n, Nat.lt_succ_self n, lt_of_le_of_lt hCk hC10⟩
    · -- CONTROLLED BRANCH: `f` grows at most like `f x ^{2√(llw/llx)}`.
      have hxzR : (z:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxz
      have hz17 : (17:ℝ) ≤ (z:ℝ) := by
        have h17 : (17:ℕ) ≤ z := by rw [hz_def]; omega
        exact_mod_cast h17
      have hx1 : (1:ℝ) < (x:ℝ) :=
        lt_of_lt_of_le (by norm_num) (hz17.trans hxzR)
      have hlogxpos : 0 < Real.log (x:ℝ) := Real.log_pos hx1
      have hll16x : (100000:ℝ) ≤ Real.log (Real.log (x:ℝ)) := hll16 x hxz
      have hlogx1 : (1:ℝ) ≤ Real.log (x:ℝ) := by
        have e : (1:ℝ) ≤ Real.exp (Real.log (Real.log (x:ℝ))) :=
          Real.one_le_exp_iff.mpr (le_trans (by norm_num) hll16x)
        rwa [Real.exp_log hlogxpos] at e
      obtain ⟨n, hnle, hdA⟩ := ersa_core A hA hll16x hfx
      rw [← hc_def] at hdA
      set t : ℝ := Real.log (recipSum A x) with ht_def
      have hdA0 : dA A 0 = 0 := by simp [dA]
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [hdA0, Nat.cast_zero] at hdA
        exact (lt_irrefl _ (lt_trans (Real.exp_pos _) hdA)).elim
      have hfx1 : (1:ℝ) ≤ recipSum A x := by
        have e : (1:ℝ) ≤ Real.exp (Real.sqrt (Real.log (Real.log (x:ℝ)))) :=
          Real.one_le_exp_iff.mpr (Real.sqrt_nonneg _)
        linarith [e, hfx.le]
      have hfxpos : (0:ℝ) < recipSum A x := lt_of_lt_of_le one_pos hfx1
      have hlogf' : Real.sqrt (Real.log (Real.log (x:ℝ))) <
          Real.log (recipSum A x) := by
        have h2 := Real.log_lt_log (Real.exp_pos _) hfx
        rwa [Real.log_exp] at h2
      have htB : B₂ < t := by
        rw [ht_def]
        exact lt_of_le_of_lt (hB2ll x hxz) hlogf'
      -- `ll (n+1) ≤ 3·ll x`
      have hnle' : ((n+1:ℕ):ℝ) ≤ 2 * Real.exp (8 * (Real.log (x:ℝ))^2) := by
        push_cast
        have e1 : (1:ℝ) ≤ Real.exp (8 * (Real.log (x:ℝ))^2) :=
          Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) (sq_nonneg _))
        have hnleR : (n:ℝ) ≤ Real.exp (8 * (Real.log (x:ℝ))^2) := hnle
        calc (n:ℝ) + 1
            ≤ Real.exp (8 * (Real.log (x:ℝ))^2) +
                Real.exp (8 * (Real.log (x:ℝ))^2) := add_le_add hnleR e1
          _ = 2 * Real.exp (8 * (Real.log (x:ℝ))^2) := (two_mul _).symm
      have hlogn1 : Real.log ((n+1:ℕ):ℝ) ≤ 9 * (Real.log (x:ℝ))^2 := by
        have h2e : Real.log (2 * Real.exp (8 * (Real.log (x:ℝ))^2)) =
            Real.log 2 + 8 * (Real.log (x:ℝ))^2 := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
        have h1 : Real.log ((n+1:ℕ):ℝ) ≤ Real.log 2 + 8 * (Real.log (x:ℝ))^2 :=
          Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos n)) hnle' |>.trans_eq h2e
        have hL2 : (1:ℝ) ≤ (Real.log (x:ℝ))^2 := by
          have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hlogx1 2
          rwa [one_pow] at h
        have hL9 : Real.log 2 ≤ (Real.log (x:ℝ))^2 :=
          Real.log_two_lt_d9.le.trans (le_trans (by norm_num) hL2)
        calc Real.log ((n+1:ℕ):ℝ)
            ≤ Real.log 2 + 8 * (Real.log (x:ℝ))^2 := h1
          _ ≤ (Real.log (x:ℝ))^2 + 8 * (Real.log (x:ℝ))^2 :=
              add_le_add_left hL9 _
          _ = 9 * (Real.log (x:ℝ))^2 := by ring
      have hn1gt1 : (1:ℝ) < ((n+1:ℕ):ℝ) := by
        exact_mod_cast Nat.succ_lt_succ (Nat.pos_of_ne_zero hn0)
      have hlln1 : Real.log (Real.log ((n+1:ℕ):ℝ)) ≤
          Real.log 9 + 2 * Real.log (Real.log (x:ℝ)) := by
        have h2 : Real.log (Real.log ((n+1:ℕ):ℝ)) ≤
            Real.log (9 * (Real.log (x:ℝ))^2) :=
          Real.log_le_log (Real.log_pos hn1gt1) hlogn1
        have h9L : Real.log (9 * (Real.log (x:ℝ))^2) =
            Real.log 9 + 2 * Real.log (Real.log (x:ℝ)) := by
          rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hlogxpos.ne'),
            Real.log_pow]
          push_cast
          ring
        rwa [h9L] at h2
      have hlog9 : Real.log 9 ≤ Real.log (Real.log (x:ℝ)) := by
        have h1 : (9:ℝ) ≤ Real.exp 16 := by
          have h17 := Real.add_one_le_exp (16:ℝ)
          linarith
        have h2 : Real.log 9 ≤ Real.log (Real.exp 16) :=
          Real.log_le_log (by norm_num) h1
        rw [Real.log_exp] at h2
        have h16 : (16:ℝ) ≤ Real.log (Real.log (x:ℝ)) := by linarith [hll16x]
        linarith [h2, h16]
      have hlln1le : Real.log (Real.log ((n+1:ℕ):ℝ)) ≤
          3 * Real.log (Real.log (x:ℝ)) := by linarith [hlln1, hlog9]
      have hllpos : (0:ℝ) < Real.log (Real.log (x:ℝ)) := by linarith [hll16x]
      have hdiv : Real.log (Real.log ((n+1:ℕ):ℝ)) / Real.log (Real.log (x:ℝ)) ≤ 3 := by
        rw [div_le_iff₀ hllpos]
        linarith [hlln1le]
      have hexp_le4 : 2 * Real.sqrt
          (Real.log (Real.log ((n+1:ℕ):ℝ)) / Real.log (Real.log (x:ℝ))) ≤ 4 := by
        have h1 := Real.sqrt_le_sqrt hdiv
        have h2 : Real.sqrt 3 ≤ 2 := by
          have hs := Real.sqrt_le_sqrt (show (3:ℝ) ≤ 4 by norm_num)
          rwa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)] at hs
        linarith [h1, h2]
      -- `f (n+1) ≤ f x ^ 4`
      have hf4 : recipSum A (n+1) ≤ (recipSum A x)^(4:ℝ) := by
        by_cases hxle : x ≤ n + 1
        · exact (hctrl (n+1) hxle).trans
            (Real.rpow_le_rpow_of_exponent_le hfx1 hexp_le4)
        · have hlt : n + 1 < x := not_le.mp hxle
          exact (recipSum_mono A (Nat.le_of_lt hlt)).trans (by
            have e := Real.rpow_le_rpow_of_exponent_le hfx1
              (by norm_num : (1:ℝ) ≤ 4)
            rwa [Real.rpow_one] at e)
      have hfk : (recipSum A (n+1))^k ≤ (recipSum A x)^((4:ℝ)*(k:ℝ)) := by
        have h1 : (recipSum A (n+1))^k ≤ ((recipSum A x)^(4:ℝ))^k :=
          pow_le_pow_left₀ (recipSum_nonneg _ _) hf4 k
        have h2 : ((recipSum A x)^(4:ℝ))^k = (recipSum A x)^((4:ℝ)*(k:ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (recipSum_nonneg _ _)]
        rwa [h2] at h1
      have hfkexp : (recipSum A x)^((4:ℝ)*(k:ℝ)) =
          Real.exp ((4:ℝ)*(k:ℝ) * t) := by
        rw [Real.rpow_def_of_pos hfxpos, ht_def]
        congr 1
        ring
      -- the quadratic bound from `B₂`
      have hbig : Real.log C + 4*(k:ℝ)*t < c * t^2 := by
        have h4k : 4*(k:ℝ) < c * (t + B₂) := by
          have h1 : 4*(k:ℝ) ≤ 2*c*B₂ := by
            have e : 2*c*((4*(k:ℝ))/(2*c)) = 4*(k:ℝ) := mul_div_cancel₀ _ h2c.ne'
            have hmul := mul_le_mul_of_nonneg_left hB2ge h2c.le
            linarith [e, hmul]
          have h2 : c*(2*B₂) < c*(t + B₂) :=
            mul_lt_mul_of_pos_left (by linarith [htB]) hc
          linarith [h1, h2]
        have key := mul_pos (sub_pos.mpr htB) (sub_pos.mpr h4k)
        nlinarith [key, hquad]
      have hfinal : C * Real.exp ((4:ℝ)*(k:ℝ)*t) < (dA A n : ℝ) := by
        have hCe : C = Real.exp (Real.log C) := (Real.exp_log hC).symm
        rw [hCe, ← Real.exp_add]
        exact lt_trans (Real.exp_lt_exp.mpr hbig) hdA
      refine ⟨n+1, n, Nat.lt_succ_self n, ?_⟩
      calc C * (recipSum A (n+1))^k ≤ C * (recipSum A x)^((4:ℝ)*(k:ℝ)) :=
            mul_le_mul_of_nonneg_left hfk hC.le
        _ = C * Real.exp ((4:ℝ)*(k:ℝ) * t) := by rw [hfkexp]
        _ < (dA A n : ℝ) := hfinal

end JSP361
