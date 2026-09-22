import Mathlib

/-!
Elementary real-analysis "eventually" lemmas used in the Erdős–Sárközy Case-A
argument.  Everything here is a pure ℝ/ℕ asymptotic fact.

Notation throughout: for `y : ℕ` viewed in `ℝ` we write `L = Real.log y` and
`u = Real.log (Real.log y)` (so `u = log L`).
-/

/-- Real version of `ev_loglog_linear`: `log` is `o(id)` at `atTop`, so any
affine function of `log u` is eventually dominated by `u`. -/
theorem aux_loglog_linear (D E : ℝ) :
    ∀ᶠ u : ℝ in Filter.atTop, D * Real.log u + E ≤ u := by
  have hc : (0:ℝ) < 1 / (2 * (|D| + 1)) := by positivity
  filter_upwards [Real.isLittleO_log_id_atTop.bound hc,
    Filter.eventually_ge_atTop (2 * |E|), Filter.eventually_ge_atTop (1:ℝ)]
    with u hu huE hu1
  have hu0 : (0:ℝ) ≤ u := le_trans zero_le_one hu1
  have hlu : (0:ℝ) ≤ Real.log u := Real.log_nonneg hu1
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hlu, abs_of_nonneg hu0] at hu
  have hcoef : |D| * (1 / (2 * (|D| + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (|D| + 1))]
    nlinarith [abs_nonneg D]
  have h1 : D * Real.log u ≤ u / 2 := by
    calc D * Real.log u ≤ |D| * Real.log u :=
          mul_le_mul_of_nonneg_right (le_abs_self D) hlu
      _ ≤ |D| * ((1 / (2 * (|D| + 1))) * u) :=
          mul_le_mul_of_nonneg_left hu (abs_nonneg D)
      _ = (|D| * (1 / (2 * (|D| + 1)))) * u := by ring
      _ ≤ (1 / 2) * u := mul_le_mul_of_nonneg_right hcoef hu0
      _ = u / 2 := by ring
  have h2 : E ≤ u / 2 := by linarith [huE, le_abs_self E]
  linarith

/-- Real version of `ev_sqrt_loglog`: `√u` is eventually dominated by `u`, so
any affine function of `√u` is eventually dominated by `u`. -/
theorem aux_sqrt_loglog (D E : ℝ) :
    ∀ᶠ u : ℝ in Filter.atTop, D * Real.sqrt u + E ≤ u := by
  filter_upwards [Filter.eventually_ge_atTop (4 * D^2),
    Filter.eventually_ge_atTop (2 * |E|), Filter.eventually_ge_atTop (0:ℝ)]
    with u huD huE hu0
  have hD2 : (2 * |D|)^2 ≤ u := by
    have h : (2 * |D|)^2 = 4 * D^2 := by
      calc (2 * |D|)^2 = 4 * |D|^2 := by ring
        _ = 4 * D^2 := by rw [sq_abs]
    rw [h]; exact huD
  have hs : 2 * |D| ≤ Real.sqrt u := by
    have h1 := Real.sqrt_le_sqrt hD2
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * |D|)] at h1
  have hsqrt : (0:ℝ) ≤ Real.sqrt u := Real.sqrt_nonneg u
  have h1 : D * Real.sqrt u ≤ u / 2 := by
    have h2 : |D| * Real.sqrt u ≤ (Real.sqrt u / 2) * Real.sqrt u :=
      mul_le_mul_of_nonneg_right (by linarith [hs]) hsqrt
    calc D * Real.sqrt u ≤ |D| * Real.sqrt u :=
          mul_le_mul_of_nonneg_right (le_abs_self D) hsqrt
      _ ≤ (Real.sqrt u / 2) * Real.sqrt u := h2
      _ = u / 2 := by rw [div_mul_eq_mul_div, Real.mul_self_sqrt hu0]
  have h2 : E ≤ u / 2 := by linarith [huE, le_abs_self E]
  linarith

theorem ev_loglog_linear (D E : ℝ) :
    ∀ᶠ y : ℕ in Filter.atTop, D * Real.log (Real.log y) + E ≤ Real.log y := by
  apply Filter.Eventually.natCast_atTop
  apply Real.tendsto_log_atTop.eventually
  exact aux_loglog_linear D E

theorem ev_sqrt_loglog (D E : ℝ) :
    ∀ᶠ y : ℕ in Filter.atTop, D * Real.sqrt (Real.log (Real.log y)) + E ≤ Real.log (Real.log y) := by
  apply Filter.Eventually.natCast_atTop
  apply Real.tendsto_log_atTop.eventually
  apply Real.tendsto_log_atTop.eventually
  exact aux_sqrt_loglog D E

/-- `log y → atTop` along `y : ℕ → atTop`. -/
theorem ev_log_ge (B : ℝ) : ∀ᶠ y : ℕ in Filter.atTop, B ≤ Real.log (y:ℝ) := by
  apply Filter.Eventually.natCast_atTop
  exact Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop B)

/-- `log log y → atTop` along `y : ℕ → atTop`. -/
theorem ev_loglog_ge (B : ℝ) :
    ∀ᶠ y : ℕ in Filter.atTop, B ≤ Real.log (Real.log (y:ℝ)) := by
  apply Filter.Eventually.natCast_atTop
  apply Real.tendsto_log_atTop.eventually
  apply Real.tendsto_log_atTop.eventually
  exact Filter.eventually_ge_atTop B

/-- `√(log log y) → atTop` along `y : ℕ → atTop`. -/
theorem ev_sqrt_loglog_ge (B : ℝ) :
    ∀ᶠ y : ℕ in Filter.atTop, B ≤ Real.sqrt (Real.log (Real.log (y:ℝ))) := by
  apply Filter.Eventually.natCast_atTop
  apply Real.tendsto_log_atTop.eventually
  apply Real.tendsto_log_atTop.eventually
  apply Real.tendsto_sqrt_atTop.eventually
  exact Filter.eventually_ge_atTop B

theorem ev_smooth_bound (K : ℕ) (hK : 1 ≤ K) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ y : ℕ in Filter.atTop,
      C * (4 * (Real.log 4 + 4) * (y:ℝ) ^ ((1:ℝ)/(4*K))) ^ K
        ≤ (y : ℝ) / (2 * (Real.log y)^2) := by
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hK0' : (↑K:ℝ) ≠ 0 := ne_of_gt hK0
  have h4Kne : (4:ℝ) * ↑K ≠ 0 := mul_ne_zero (by norm_num) hK0'
  have hlog4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  set c := 4 * (Real.log 4 + 4) with hcdef
  have hc : (0:ℝ) < c := by rw [hcdef]; positivity
  filter_upwards [ev_loglog_linear (8/3)
      ((4/3) * (Real.log C + ↑K * Real.log c + Real.log 2)),
    ev_log_ge 1, Filter.eventually_ge_atTop 1] with y hmaster hL1 hy1
  set L := Real.log ↑y with hLdef
  set u := Real.log L with hudef
  have hypos : (0:ℝ) < (↑y:ℝ) := by
    have h : (1:ℝ) ≤ ↑y := by exact_mod_cast hy1
    linarith
  have hLpos : (0:ℝ) < L := by linarith [hL1]
  have hck : (0:ℝ) < c^K := pow_pos hc K
  have hyr : (0:ℝ) < (↑y:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos hypos _
  have hA : (0:ℝ) < C * c^K * (↑y)^(1/4:ℝ) := mul_pos (mul_pos hC hck) hyr
  have hB : (0:ℝ) < 2 * L^2 := mul_pos two_pos (pow_pos hLpos 2)
  -- `2u + B ≤ (3/4)L` where `B = log C + K log c + log 2`
  have hlog_ineq : Real.log C + ↑K * Real.log c + Real.log 2 + 2 * u + L / 4 ≤ L := by
    linarith [hmaster]
  have heq : (1:ℝ)/(4*↑K) * ↑K = 1/4 := by
    rw [mul_comm (1/(4*↑K)) ↑K, mul_one_div, mul_comm (4:ℝ) ↑K, ← div_div,
      div_self hK0']
  have h1 : ((↑y:ℝ)^(1/(4*↑K)))^K = (↑y)^(1/4:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hypos.le, heq]
  have hLHS : C * (c * (↑y:ℝ)^(1/(4*↑K)))^K = C * c^K * (↑y)^(1/4:ℝ) := by
    rw [mul_pow, h1]; ring
  have hlogeq : Real.log (C * c^K * (↑y)^(1/4:ℝ) * (2 * L^2))
      = Real.log C + ↑K * Real.log c + (1/4) * L + (Real.log 2 + 2 * u) := by
    rw [Real.log_mul hA.ne' hB.ne', Real.log_mul (mul_pos hC hck).ne' hyr.ne',
        Real.log_mul hC.ne' hck.ne', Real.log_mul two_pos.ne' (pow_pos hLpos 2).ne',
        Real.log_rpow hypos]
    simp only [Real.log_pow, Nat.cast_ofNat]
    rw [← hLdef, ← hudef]
    ring
  have hlogineq' : Real.log (C * c^K * (↑y)^(1/4:ℝ) * (2 * L^2)) ≤ Real.log ↑y := by
    rw [hlogeq, ← hLdef]
    linarith [hlog_ineq]
  have hgoal : C * c^K * (↑y)^(1/4:ℝ) * (2 * L^2) ≤ ↑y := by
    calc C * c^K * (↑y)^(1/4:ℝ) * (2 * L^2)
        = Real.exp (Real.log (C * c^K * (↑y)^(1/4:ℝ) * (2 * L^2))) :=
          (Real.exp_log (mul_pos hA hB)).symm
      _ ≤ Real.exp (Real.log ↑y) := Real.exp_le_exp.mpr hlogineq'
      _ = ↑y := Real.exp_log hypos
  rw [hLHS, le_div_iff₀ hB]
  exact hgoal

theorem ev_fiber_size (K : ℕ) (hK : 1 ≤ K) :
    ∀ᶠ y : ℕ in Filter.atTop,
      Real.exp (2 * K * Real.sqrt (2 * Real.log (Real.log y))) + 1
        ≤ (y:ℝ) ^ ((1:ℝ)/(4*K)) / (4 * (Real.log y)^2) := by
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hK0' : (↑K:ℝ) ≠ 0 := ne_of_gt hK0
  filter_upwards [ev_loglog_linear (4 * ↑K * (2 * ↑K * Real.sqrt 2 + 2))
      (4 * ↑K * (3 * Real.log 2)),
    ev_loglog_ge 1, ev_log_ge 1, Filter.eventually_ge_atTop 1]
    with y hmaster hu1 hL1 hy1
  set L := Real.log ↑y with hLdef
  set u := Real.log L with hudef
  set z := 2 * ↑K * Real.sqrt (2 * u) with hzdef
  have hypos : (0:ℝ) < (↑y:ℝ) := by
    have h : (1:ℝ) ≤ ↑y := by exact_mod_cast hy1
    linarith
  have hLpos : (0:ℝ) < L := by linarith [hL1]
  have hz0 : (0:ℝ) ≤ z := by rw [hzdef]; positivity
  have hexp1 : (1:ℝ) ≤ Real.exp z := Real.one_le_exp hz0
  have hsqrt_le : Real.sqrt u ≤ u := by
    have hu0 : (0:ℝ) ≤ u := le_trans zero_le_one hu1
    have hsq : u ≤ u^2 := by
      rw [pow_two]
      exact le_mul_of_one_le_right hu0 hu1
    calc Real.sqrt u ≤ Real.sqrt (u^2) := Real.sqrt_le_sqrt hsq
      _ = u := Real.sqrt_sq hu0
  have hz' : z = (2 * ↑K * Real.sqrt 2) * Real.sqrt u := by
    rw [hzdef, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) u]; ring
  have h4K : (0:ℝ) < 4 * ↑K := by positivity
  have hdiv : (2 * ↑K * Real.sqrt 2 + 2) * u + 3 * Real.log 2 ≤ L / (4 * ↑K) := by
    rw [le_div_iff₀ h4K]
    have hrw : ((2 * ↑K * Real.sqrt 2 + 2) * u + 3 * Real.log 2) * (4 * ↑K)
        = (4 * ↑K * (2 * ↑K * Real.sqrt 2 + 2)) * u + 4 * ↑K * (3 * Real.log 2) := by
      ring
    rw [hrw]; exact hmaster
  have hmain : z + 3 * Real.log 2 + 2 * u ≤ L * (1 / (4 * ↑K)) := by
    rw [mul_one_div, hz']
    have hcoef : (0:ℝ) ≤ 2 * ↑K * Real.sqrt 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsqrt_le hcoef
    linarith [hdiv, h1]
  have hfin : 2 * Real.exp z * (4 * L^2) ≤ Real.exp (L * (1 / (4 * ↑K))) := by
    have h8 : (0:ℝ) < 8 * L^2 := by positivity
    have hlog8 : Real.log (8 * L^2) = 3 * Real.log 2 + 2 * u := by
      rw [Real.log_mul (by norm_num) (pow_pos hLpos 2).ne',
          show (8:ℝ) = 2^3 by norm_num, Real.log_pow, Real.log_pow, ← hudef]
      norm_num
    have e1 : 2 * Real.exp z * (4 * L^2) = Real.exp z * (8 * L^2) := by ring
    rw [e1, ← Real.exp_log h8, ← Real.exp_add, hlog8]
    apply Real.exp_le_exp.mpr
    linarith [hmain]
  have hgoal : Real.exp z + 1 ≤ (↑y:ℝ)^(1/(4*↑K)) / (4 * L^2) := by
    have h1 : Real.exp z + 1 ≤ 2 * Real.exp z := by linarith [hexp1]
    refine h1.trans ?_
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * L^2),
        Real.rpow_def_of_pos hypos, ← hLdef]
    exact hfin
  exact hgoal

theorem ev_loglog_witness (K : ℕ) (hK : 1 ≤ K) :
    ∀ᶠ y : ℕ in Filter.atTop,
      Real.log (2 * Real.exp (2 * K * Real.sqrt (2 * Real.log (Real.log y)))
          * Real.log y + 1) + 1
        ≤ 2 * Real.log (Real.log y) := by
  filter_upwards [ev_sqrt_loglog (2 * ↑K * Real.sqrt 2) (Real.log 2 + 2),
    ev_log_ge 1] with y hu hL1
  set L := Real.log ↑y with hLdef
  set u := Real.log L with hudef
  set z := 2 * ↑K * Real.sqrt (2 * u) with hzdef
  have hLpos : (0:ℝ) < L := by linarith [hL1]
  have hz0 : (0:ℝ) ≤ z := by rw [hzdef]; positivity
  have hexp1 : (1:ℝ) ≤ Real.exp z := Real.one_le_exp hz0
  have ht1 : (1:ℝ) ≤ 2 * Real.exp z * L := by
    nlinarith [hexp1, hL1, mul_nonneg (sub_nonneg.mpr hexp1) (sub_nonneg.mpr hL1)]
  have ht0 : (0:ℝ) < 2 * Real.exp z * L := lt_of_lt_of_le zero_lt_one ht1
  have hp : (0:ℝ) < 1 + 1 / (2 * Real.exp z * L) := by positivity
  have hlog : Real.log (2 * Real.exp z * L + 1) ≤ Real.log (2 * Real.exp z * L) + 1 := by
    have e1 : Real.log (2 * Real.exp z * L + 1)
        = Real.log (2 * Real.exp z * L) + Real.log (1 + 1 / (2 * Real.exp z * L)) := by
      rw [← Real.log_mul ht0.ne' hp.ne']
      congr 1
      rw [mul_add, mul_one, mul_one_div, div_self ht0.ne']
    rw [e1]
    have e2 : Real.log (1 + 1 / (2 * Real.exp z * L)) ≤ 1 / (2 * Real.exp z * L) := by
      have h := Real.log_le_sub_one_of_pos hp
      rwa [add_sub_cancel_left] at h
    have e3 : (1:ℝ) / (2 * Real.exp z * L) ≤ 1 := by
      rw [div_le_one ht0]
      exact ht1
    linarith [e2, e3]
  have hlogt : Real.log (2 * Real.exp z * L) = Real.log 2 + z + u := by
    rw [Real.log_mul (by positivity : (0:ℝ) < 2 * Real.exp z).ne' hLpos.ne',
        Real.log_mul two_pos.ne' (Real.exp_pos z).ne', Real.log_exp, ← hudef]
  have hmain : z + (Real.log 2 + 2) ≤ u := by
    have hz' : z = (2 * ↑K * Real.sqrt 2) * Real.sqrt u := by
      rw [hzdef, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) u]; ring
    rw [hz']; exact hu
  calc Real.log (2 * Real.exp z * L + 1) + 1
      ≤ (Real.log (2 * Real.exp z * L) + 1) + 1 := by linarith [hlog]
    _ = Real.log 2 + z + u + 2 := by rw [hlogt]; ring
    _ ≤ 2 * u := by linarith [hmain]

theorem ev_final_bound (K : ℕ) (hK : 1 ≤ K) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ y : ℕ in Filter.atTop,
      C * Real.exp (K * Real.sqrt (2 * Real.log (Real.log y))) + 1
        ≤ Real.exp (2 * K * Real.sqrt (Real.log (Real.log y))) := by
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hs2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]; norm_num
  have hcoef : (0:ℝ) < ↑K * (2 - Real.sqrt 2) := by
    have hs : (0:ℝ) < 2 - Real.sqrt 2 := sub_pos.mpr hs2
    positivity
  filter_upwards [ev_sqrt_loglog_ge (Real.log (C + 1) / (↑K * (2 - Real.sqrt 2)))]
    with y hsu
  set u := Real.log (Real.log ↑y) with hudef
  have hlog : Real.log (C + 1) ≤ ↑K * (2 - Real.sqrt 2) * Real.sqrt u := by
    have h := (div_le_iff₀ hcoef).mp hsu
    rwa [mul_comm (Real.sqrt u) (↑K * (2 - Real.sqrt 2))] at h
  have hexp : C + 1 ≤ Real.exp (↑K * (2 - Real.sqrt 2) * Real.sqrt u) := by
    have h := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (by positivity : (0:ℝ) < C + 1)] at h
  have hw : (0:ℝ) ≤ ↑K * Real.sqrt (2 * u) := by positivity
  have hexpw : (1:ℝ) ≤ Real.exp (↑K * Real.sqrt (2 * u)) := Real.one_le_exp hw
  have step3 : Real.exp (↑K * (2 - Real.sqrt 2) * Real.sqrt u)
        * Real.exp (↑K * Real.sqrt (2 * u))
      = Real.exp (2 * ↑K * Real.sqrt u) := by
    rw [← Real.exp_add]
    congr 1
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) u]
    ring
  have step2 : (C + 1) * Real.exp (↑K * Real.sqrt (2 * u))
      ≤ Real.exp (2 * ↑K * Real.sqrt u) := by
    rw [← step3]
    exact mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
  have step1 : C * Real.exp (↑K * Real.sqrt (2 * u)) + 1
      ≤ (C + 1) * Real.exp (↑K * Real.sqrt (2 * u)) := by
    nlinarith [hexpw]
  exact step1.trans step2

theorem ev_n_large (K : ℕ) (hK : 1 ≤ K) (U : ℕ) :
    ∀ᶠ y : ℕ in Filter.atTop,
      (U : ℝ) + 1
        ≤ Real.exp ((Real.log y / (8*K))
            * Real.exp (2 * K * Real.sqrt (2 * Real.log (Real.log y)))) := by
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  filter_upwards [ev_log_ge (8 * ↑K * Real.log (↑U + 1)), ev_log_ge 1]
    with y hL hL1
  set L := Real.log ↑y with hLdef
  set u := Real.log L with hudef
  have hLpos : (0:ℝ) < L := by linarith [hL1]
  have hz : (0:ℝ) ≤ 2 * ↑K * Real.sqrt (2 * u) := by positivity
  have hexp1 : (1:ℝ) ≤ Real.exp (2 * ↑K * Real.sqrt (2 * u)) := Real.one_le_exp hz
  have h1 : Real.log (↑U + 1) ≤ L / (8 * ↑K) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * ↑K)]
    linarith [hL]
  have hnn : (0:ℝ) ≤ L / (8 * ↑K) := by positivity
  have h2 : L / (8 * ↑K)
      ≤ (L / (8 * ↑K)) * Real.exp (2 * ↑K * Real.sqrt (2 * u)) := by
    calc L / (8 * ↑K) = (L / (8 * ↑K)) * 1 := (mul_one _).symm
      _ ≤ (L / (8 * ↑K)) * Real.exp _ := mul_le_mul_of_nonneg_left hexp1 hnn
  have h3 : Real.log (↑U + 1)
      ≤ (L / (8 * ↑K)) * Real.exp (2 * ↑K * Real.sqrt (2 * u)) := le_trans h1 h2
  have h4 := Real.exp_le_exp.mpr h3
  rwa [Real.exp_log (by positivity : (0:ℝ) < ↑U + 1)] at h4
