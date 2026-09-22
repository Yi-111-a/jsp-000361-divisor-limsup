import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# JSP-000361 — real-analytic parameter choice for the ErSa80 core

For `L ≥ 10^5`, `√L < lf ≤ L+1`, `L/2 ≤ S ≤ 6L` there is a natural `t`
(explicitly `t = ⌈((e/64)·lf² + log 16 + 1)/(L − log L − 8)⌉₊` clamped at `1`)
with `1 ≤ t ≤ S` and

* complement-mass side: `t·log(2e·S/t) ≤ lf/2`,
* gain side: `t·(L − log L − 8) ≥ (e/64)·lf² + log 16 + 1`.

Worst cases: `lf ≈ L` with `S ≈ 6L` gives `t ≈ 0.043L` and cost
`≈ 0.043L·log(12e/0.043) ≈ 0.29L ≤ lf/2`; `lf ≈ √L` gives `t = 1` and cost
`log(12eL) ≈ 12 ≤ √L/2 ≈ 158`.  Both sides have margin ≥ ~1.7× for
`L ≥ 10^5`.
-/

namespace JSP361

/-- Tangent bound `log w ≤ w / e` (the tangent line at `w = e`). -/
private lemma log_le_div_exp {w : ℝ} (hw : 0 < w) :
    Real.log w ≤ w / Real.exp 1 := by
  have h1 : Real.log (w / Real.exp 1) ≤ w / Real.exp 1 - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hw (Real.exp_pos 1))
  have h2 : Real.log (w / Real.exp 1) = Real.log w - 1 := by
    rw [Real.log_div hw.ne' (Real.exp_ne_zero 1), Real.log_exp]
  linarith

/-- `v·log(1/v) ≤ 1/e` for `v > 0`. -/
private lemma mul_log_inv_le {v : ℝ} (hv : 0 < v) :
    v * Real.log (1 / v) ≤ 1 / Real.exp 1 := by
  have h1 : Real.log (1 / v) ≤ (1 / v) / Real.exp 1 :=
    log_le_div_exp (one_div_pos.mpr hv)
  calc v * Real.log (1 / v)
      ≤ v * ((1 / v) / Real.exp 1) := mul_le_mul_of_nonneg_left h1 hv.le
    _ = 1 / Real.exp 1 := by
        have hv' : v ≠ 0 := hv.ne'
        have he' : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
        field_simp

/-- `u ↦ u·log(C/u)` is nondecreasing for `0 < u ≤ v` with `v·e ≤ C`. -/
private lemma mul_log_div_mono {C u v : ℝ} (hC : 0 < C) (hu : 0 < u) (huv : u ≤ v)
    (hvC : v * Real.exp 1 ≤ C) :
    u * Real.log (C / u) ≤ v * Real.log (C / v) := by
  have hv : 0 < v := hu.trans_le huv
  rw [Real.log_div hC.ne' hu.ne', Real.log_div hC.ne' hv.ne']
  have h1 : Real.log v - Real.log u ≤ v / u - 1 := by
    rw [← Real.log_div hv.ne' hu.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hv hu)
  have h4 : u * (v / u - 1) = v - u := by
    have hu' : u ≠ 0 := hu.ne'
    field_simp
  have h2 : u * (Real.log v - Real.log u) ≤ v - u := by
    have h3 := mul_le_mul_of_nonneg_left h1 hu.le
    linarith [h3, h4]
  have h5 : Real.log v + 1 ≤ Real.log C := by
    have hve : 0 < v * Real.exp 1 := mul_pos hv (Real.exp_pos 1)
    have h6 := Real.log_le_log hve hvC
    rwa [Real.log_mul hv.ne' (Real.exp_ne_zero 1), Real.log_exp] at h6
  have h7 : v * Real.log v - u * Real.log u ≤ (v - u) * (Real.log v + 1) := by
    linarith [h2]
  have h8 : (v - u) * (Real.log v + 1) ≤ (v - u) * Real.log C :=
    mul_le_mul_of_nonneg_left h5 (sub_nonneg.mpr huv)
  linarith [h7, h8]

set_option maxHeartbeats 1600000 in
/-- Parameter `t` for the ErSa80 core argument. -/
theorem ersa_params {L lf S : ℝ} (hL : (100000 : ℝ) ≤ L)
    (hlf : Real.sqrt L < lf) (hlfu : lf ≤ L + 1)
    (hS : L / 2 ≤ S) (hSS : S ≤ 6 * L) :
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ S ∧
      (t : ℝ) * Real.log (2 * Real.exp 1 * S / (t : ℝ)) ≤ lf / 2 ∧
      Real.exp 1 / 64 * lf ^ 2 + Real.log 16 + 1 ≤
        (t : ℝ) * (L - Real.log L - 8) := by
  set G := Real.exp 1 / 64 * lf ^ 2 + Real.log 16 + 1 with hGeq
  set W := L - Real.log L - 8 with hWeq
  set T := G / W + 1 with hTeq
  set A := Real.exp 1 / 60 * lf ^ 2 / L with hAeq
  set B := Real.log 768 + 2 * Real.log (L / lf) with hBeq
  -- basic positivity
  have hLpos : (0 : ℝ) < L := by linarith
  have hLne : L ≠ 0 := hLpos.ne'
  have hs_pos : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hlf_pos : (0 : ℝ) < lf := hs_pos.trans hlf
  have hlfne : lf ≠ 0 := hlf_pos.ne'
  have hSpos : (0 : ℝ) < S := by linarith
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he_ne : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hs2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLpos.le
  have hs316 : (316 : ℝ) ≤ Real.sqrt L := by
    have h1 : (316 : ℝ) ≤ Real.sqrt 100000 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    exact h1.trans ((Real.sqrt_le_sqrt_iff hLpos.le).mpr hL)
  -- numeric bounds on `e`
  have hb := Real.exp_bound (show |(1 : ℝ)| ≤ 1 by norm_num) (n := 10) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  have he_lo : (2.716 : ℝ) ≤ Real.exp 1 := by linarith [(abs_le.mp hb).1]
  have he_hi : Real.exp 1 ≤ (2.7197 : ℝ) := by linarith [(abs_le.mp hb).2]
  -- bounds on `log L`
  have hlogL_nn : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogL1 : Real.log L ≤ 2 * Real.sqrt L := by
    have h1 := Real.log_le_sub_one_of_pos hs_pos
    rw [Real.log_sqrt hLpos.le] at h1
    linarith
  have he6 : (400 : ℝ) ≤ Real.exp 6 := by
    have hexp6 : Real.exp 6 = Real.exp 1 ^ 6 := by
      have h := Real.exp_nat_mul (1 : ℝ) 6
      rw [mul_one] at h
      norm_num at h
      exact h
    rw [hexp6]
    have e2 : (7.37 : ℝ) ≤ Real.exp 1 ^ 2 := by
      nlinarith [he_lo, mul_nonneg (sub_nonneg.mpr he_lo) (sub_nonneg.mpr he_lo)]
    have e3 : (20 : ℝ) ≤ Real.exp 1 ^ 3 := by
      have h : Real.exp 1 ^ 3 = Real.exp 1 ^ 2 * Real.exp 1 := by ring
      rw [h]
      have h2 := mul_le_mul e2 he_lo (by norm_num) (sq_nonneg _)
      nlinarith [h2]
    have e6 : Real.exp 1 ^ 6 = (Real.exp 1 ^ 3) ^ 2 := by ring
    rw [e6]
    have h3 := mul_le_mul e3 e3 (by norm_num) (le_trans (by norm_num) e3)
    nlinarith [h3]
  have hlogtan : ∀ y : ℝ, 0 < y → Real.log y ≤ y / 400 + 5 := by
    intro y hy
    have h1 : Real.log (y / Real.exp 6) ≤ y / Real.exp 6 - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 6))
    have h2 : Real.log (y / Real.exp 6) = Real.log y - 6 := by
      rw [Real.log_div hy.ne' (Real.exp_ne_zero 6), Real.log_exp]
    have h3 : y / Real.exp 6 ≤ y / 400 :=
      div_le_div_of_nonneg_left hy.le (by norm_num) he6
    linarith
  have hlogL2 : Real.log L ≤ Real.sqrt L / 200 + 10 := by
    have h1 := hlogtan (Real.sqrt L) hs_pos
    rw [Real.log_sqrt hLpos.le] at h1
    linarith
  -- `W` bounds
  have hWge : 19 * L / 20 ≤ W := by
    rw [hWeq]
    nlinarith [hlogL1, hs2, hs316, Real.sqrt_nonneg L]
  have hWpos : (0 : ℝ) < W := by linarith
  have hWle : W ≤ L := by rw [hWeq]; linarith [hlogL_nn]
  -- `G` bounds
  have hlog16_nn : (0 : ℝ) ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hGpos : (0 : ℝ) < G := by
    rw [hGeq]
    have h1 : (0 : ℝ) < Real.exp 1 / 64 * lf ^ 2 := by positivity
    linarith
  have hGWpos : (0 : ℝ) < G / W := div_pos hGpos hWpos
  -- ceiling facts
  have ht1n : 1 ≤ ⌈G / W⌉₊ := Nat.one_le_ceil_iff.mpr hGWpos
  have ht0 : (0 : ℝ) < (⌈G / W⌉₊ : ℝ) := by exact_mod_cast ht1n
  have ht_ge : G / W ≤ (⌈G / W⌉₊ : ℝ) := Nat.le_ceil _
  have ht_lt : (⌈G / W⌉₊ : ℝ) < T := by
    rw [hTeq]
    exact Nat.ceil_lt_add_one hGWpos.le
  -- numeric log bounds
  have hlog2 : Real.log 2 ≤ (0.7 : ℝ) := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.7 : ℝ) by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
    linarith
  have hlog3 : Real.log 3 ≤ (1.15 : ℝ) := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)]
    have h1 : Real.exp (1.15 : ℝ) = Real.exp 1 * Real.exp 0.15 := by
      rw [show (1.15 : ℝ) = 1 + 0.15 by norm_num, Real.exp_add]
    rw [h1]
    have h2 : (1.15 : ℝ) ≤ Real.exp 0.15 := by
      have := Real.add_one_le_exp (0.15 : ℝ); linarith
    have h3 := mul_le_mul he_lo h2 (by norm_num) (le_trans (by norm_num) he_lo)
    nlinarith [h3]
  have hlog16 : Real.log 16 ≤ (2.8 : ℝ) := by
    have h : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    rw [h]; linarith [hlog2]
  have hlog768 : Real.log 768 ≤ (6.75 : ℝ) := by
    have h : Real.log 768 = 8 * Real.log 2 + Real.log 3 := by
      rw [show (768 : ℝ) = 2 ^ 8 * 3 by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    rw [h]; linarith [hlog2, hlog3]
  -- `T ≤ A + 2`
  have hWbig : Real.log 16 + 1 ≤ W := by linarith [hWge, hL, hlog16]
  have hkey : G / W ≤ A + 1 := by
    rw [hAeq, div_le_iff₀ hWpos]
    have h1 : Real.exp 1 / 64 * lf ^ 2 ≤ Real.exp 1 / 60 * lf ^ 2 / L * W := by
      have h3 : Real.exp 1 / 60 * lf ^ 2 / L * W
          = Real.exp 1 / 60 * lf ^ 2 * W / L := by ring
      rw [h3, le_div_iff₀ hLpos]
      have hnn : (0 : ℝ) ≤ Real.exp 1 * lf ^ 2 := by positivity
      have hw : (0 : ℝ) ≤ W - 15 * L / 16 := by linarith [hWge]
      nlinarith [mul_nonneg hnn hw]
    have h2 : (Real.exp 1 / 60 * lf ^ 2 / L + 1) * W
        = Real.exp 1 / 60 * lf ^ 2 / L * W + W := by ring
    rw [h2, hGeq]
    linarith [h1, hWbig]
  have hTA : T ≤ A + 2 := by rw [hTeq]; linarith [hkey]
  have hA20 : A ≤ L / 20 := by
    rw [hAeq, div_le_iff₀ hLpos]
    have hlf2 : lf ^ 2 ≤ (L + 1) ^ 2 := by
      have h := mul_le_mul hlfu hlfu hlf_pos.le (by linarith : (0 : ℝ) ≤ L + 1)
      rw [pow_two, pow_two]
      exact h
    have hLsq : (0 : ℝ) ≤ L * (L - 100000) :=
      mul_nonneg hLpos.le (by linarith)
    have he2 : Real.exp 1 * lf ^ 2 ≤ (2.7197 : ℝ) * (L + 1) ^ 2 :=
      mul_le_mul he_hi hlf2 (sq_nonneg lf) (by norm_num)
    nlinarith [he2, hLsq, hL, hLpos]
  have hTS : T ≤ S := by linarith [hTA, hA20, hS, hL]
  have hTpos : (0 : ℝ) < T := by rw [hTeq]; linarith [hGWpos]
  have h768ge : (1 : ℝ) ≤ 768 * (L / lf) ^ 2 := by
    have h1 : L / (L + 1) ≤ L / lf := div_le_div_of_nonneg_left hLpos.le hlf_pos hlfu
    have h2 : (100000 / 100001 : ℝ) ≤ L / (L + 1) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 100001)
        (by positivity : (0 : ℝ) < L + 1)]
      linarith [hL]
    have hxc : (100000 / 100001 : ℝ) ≤ L / lf := h2.trans h1
    have hx0 : (0 : ℝ) ≤ L / lf := div_nonneg hLpos.le hlf_pos.le
    nlinarith [hxc, hx0]
  have hBlog : Real.log (768 * (L / lf) ^ 2) = B := by
    rw [hBeq, Real.log_mul (by norm_num) (pow_ne_zero 2 (div_ne_zero hLne hlfne)),
      Real.log_pow]
    norm_num
  have hBnn : (0 : ℝ) ≤ B := by
    rw [← hBlog]
    exact Real.log_nonneg h768ge
  -- monotonicity step: `t·log(2eS/t) ≤ T·log(2eS/T)`
  have hCe : T * Real.exp 1 ≤ 2 * Real.exp 1 * S := by
    have h1 : T ≤ 2 * S := by linarith [hTS, hSpos]
    calc T * Real.exp 1 ≤ (2 * S) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right h1 he_pos.le
      _ = 2 * Real.exp 1 * S := by ring
  have hmono : (⌈G / W⌉₊ : ℝ) * Real.log (2 * Real.exp 1 * S / (⌈G / W⌉₊ : ℝ))
      ≤ T * Real.log (2 * Real.exp 1 * S / T) :=
    mul_log_div_mono (by positivity) ht0 ht_lt.le hCe
  -- `log(2eS/T) ≤ log(12eL/T)`
  have h2e : 2 * Real.exp 1 * S ≤ 12 * Real.exp 1 * L := by
    have h := mul_le_mul_of_nonneg_left hSS
      (show (0 : ℝ) ≤ 2 * Real.exp 1 by positivity)
    linarith [h]
  have hstep2 : T * Real.log (2 * Real.exp 1 * S / T)
      ≤ T * Real.log (12 * Real.exp 1 * L / T) := by
    apply mul_le_mul_of_nonneg_left _ hTpos.le
    apply Real.log_le_log
    · positivity
    · rw [div_le_div_iff₀ hTpos hTpos]
      exact mul_le_mul_of_nonneg_right h2e hTpos.le
  -- `log(12eL/T) ≤ log(768·(L/lf)²) = B`
  have htLo : Real.exp 1 * lf ^ 2 / (64 * L) ≤ T := by
    have h1 : G / L ≤ G / W := div_le_div_of_nonneg_left hGpos.le hWpos hWle
    have h2 : Real.exp 1 * lf ^ 2 / (64 * L) ≤ G / L := by
      have h3 : Real.exp 1 / 64 * lf ^ 2 ≤ G := by rw [hGeq]; linarith [hlog16_nn]
      have h4 : Real.exp 1 / 64 * lf ^ 2 / L ≤ G / L :=
        (div_le_div_iff₀ hLpos hLpos).mpr (mul_le_mul_of_nonneg_right h3 hLpos.le)
      have h5 : Real.exp 1 * lf ^ 2 / (64 * L)
          = Real.exp 1 / 64 * lf ^ 2 / L := by ring
      rwa [h5]
    have hT1 : G / L ≤ T := by rw [hTeq]; linarith [h1]
    exact h2.trans hT1
  have hstep3 : T * Real.log (12 * Real.exp 1 * L / T) ≤ T * B := by
    have h768nn : (0 : ℝ) ≤ 768 * (L / lf) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left htLo h768nn
    have heq : 768 * (L / lf) ^ 2 * (Real.exp 1 * lf ^ 2 / (64 * L))
        = 12 * Real.exp 1 * L := by
      field_simp
      ring
    apply mul_le_mul_of_nonneg_left _ hTpos.le
    rw [← hBlog]
    apply Real.log_le_log
    · positivity
    · rw [div_le_iff₀ hTpos]
      calc 12 * Real.exp 1 * L
          = 768 * (L / lf) ^ 2 * (Real.exp 1 * lf ^ 2 / (64 * L)) := heq.symm
        _ ≤ 768 * (L / lf) ^ 2 * T := hmul
  -- bounds on the pieces of `B`
  have hlogLl : Real.log (L / lf) ≤ Real.log L / 2 := by
    have hLlf : L / lf < Real.sqrt L := by
      rw [div_lt_iff₀ hlf_pos]
      conv_lhs => rw [← hs2, pow_two]
      exact mul_lt_mul_of_pos_left hlf hs_pos
    have h1 := Real.log_lt_log (div_pos hLpos hlf_pos) hLlf
    rw [Real.log_sqrt hLpos.le] at h1
    exact h1.le
  have hvv : (lf / L) * Real.log (L / lf) ≤ 1 / Real.exp 1 := by
    have h := mul_log_inv_le (div_pos hlf_pos hLpos)
    rwa [one_div_div] at h
  have hllf : (lf ^ 2 / L) * Real.log (L / lf) ≤ lf / Real.exp 1 := by
    have h1 : lf ^ 2 / L = lf * (lf / L) := by rw [pow_two, mul_div_assoc]
    rw [h1, mul_assoc]
    calc lf * ((lf / L) * Real.log (L / lf))
        ≤ lf * (1 / Real.exp 1) := mul_le_mul_of_nonneg_left hvv hlf_pos.le
      _ = lf / Real.exp 1 := by rw [mul_one_div]
  have hA2 : A * (2 * Real.log (L / lf)) ≤ lf / 30 := by
    have hdec : A * (2 * Real.log (L / lf))
        = Real.exp 1 / 30 * ((lf ^ 2 / L) * Real.log (L / lf)) := by
      rw [hAeq]; ring
    rw [hdec]
    calc Real.exp 1 / 30 * ((lf ^ 2 / L) * Real.log (L / lf))
        ≤ Real.exp 1 / 30 * (lf / Real.exp 1) :=
          mul_le_mul_of_nonneg_left hllf (by positivity)
      _ = lf / 30 := by field_simp; try ring
  have hA1 : A * Real.log 768 ≤ (306 / 1000) * lf := by
    rw [hAeq]
    have hAnn : (0 : ℝ) ≤ Real.exp 1 / 60 * lf ^ 2 / L := by positivity
    have h1 : Real.exp 1 / 60 * lf ^ 2 / L * Real.log 768
        ≤ Real.exp 1 / 60 * lf ^ 2 / L * 6.75 :=
      mul_le_mul_of_nonneg_left hlog768 hAnn
    have hlf2L : lf ^ 2 / L ≤ (100001 / 100000 : ℝ) * lf := by
      have h1' : lf ^ 2 ≤ lf * (L + 1) := by
        have h := mul_le_mul_of_nonneg_left hlfu hlf_pos.le
        nlinarith [h]
      have h2' : lf * (L + 1) / L ≤ (100001 / 100000 : ℝ) * lf := by
        have h3' : (L + 1) / L ≤ (100001 : ℝ) / 100000 := by
          rw [div_le_div_iff₀ hLpos (by norm_num : (0 : ℝ) < 100000)]
          linarith [hL]
        have h4' : lf * (L + 1) / L = lf * ((L + 1) / L) := by ring
        rw [h4']
        exact (mul_le_mul_of_nonneg_left h3' hlf_pos.le).trans_eq (mul_comm _ _)
      calc lf ^ 2 / L ≤ lf * (L + 1) / L :=
            (div_le_div_iff₀ hLpos hLpos).mpr
              (mul_le_mul_of_nonneg_right h1' hLpos.le)
        _ ≤ (100001 / 100000 : ℝ) * lf := h2'
    have h2 : Real.exp 1 / 60 * lf ^ 2 / L
        ≤ Real.exp 1 / 60 * ((100001 / 100000 : ℝ) * lf) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hlf2L (by positivity)
    have h3 : Real.exp 1 / 60 * ((100001 / 100000 : ℝ) * lf) * 6.75
        ≤ (306 / 1000) * lf := by
      nlinarith [he_hi, hlf_pos.le]
    linarith [h1, h2, h3]
  have h2B : 2 * B ≤ lf / 7 := by
    rw [hBeq]
    have h1 : 2 * (Real.log 768 + 2 * Real.log (L / lf))
        ≤ 13.5 + 2 * Real.log L := by
      linarith [hlog768, hlogLl]
    have h2 : 13.5 + 2 * Real.log L ≤ Real.sqrt L / 7 := by
      linarith [hlogL2, hs316]
    have h3 : Real.sqrt L / 7 ≤ lf / 7 := by linarith [hlf.le]
    linarith [h1, h2, h3]
  -- assemble: `T·B ≤ lf/2`
  have hfin : T * B ≤ lf / 2 := by
    have e1 : T * B ≤ A * B + 2 * B := by
      have h := mul_le_mul_of_nonneg_right hTA hBnn
      linarith [h]
    have e2 : A * B = A * Real.log 768 + A * (2 * Real.log (L / lf)) := by
      rw [hBeq]; ring
    linarith [e1, e2, hA1, hA2, h2B, hlf_pos.le]
  -- conclude
  refine ⟨⌈G / W⌉₊, ht1n, ht_lt.le.trans hTS, ?_, ?_⟩
  · calc (⌈G / W⌉₊ : ℝ) * Real.log (2 * Real.exp 1 * S / (⌈G / W⌉₊ : ℝ))
        ≤ T * Real.log (2 * Real.exp 1 * S / T) := hmono
      _ ≤ T * Real.log (12 * Real.exp 1 * L / T) := hstep2
      _ ≤ T * B := hstep3
      _ ≤ lf / 2 := hfin
  · exact (div_le_iff₀ hWpos).mp ht_ge

end JSP361
