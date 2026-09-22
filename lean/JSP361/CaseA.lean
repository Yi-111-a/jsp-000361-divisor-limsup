import JSP361.PolyBound
import JSP361.Density
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# JSP-000361 — "Case A" of the Erdős–Sárközy limsup theorem

If the reciprocal sum `recipSum A` is unbounded (`hU`) but grows at most
like `exp (sqrt (log log u))` eventually (`hcase`), then for every `k ≥ 1`
and `C > 0` there is a pair `n < x` with `C * recipSum A x ^ k < dA A n`.

The proof is by contradiction: the negation `hcon` forces, via
`powSmooth_poly_of_hcon`, polynomial control of `s`-smooth elements of `A`.
At a dense scale `y` (from `exists_countA_ge_div_log_sq`), most elements of
`A ∩ [1, y)` carry a prime-power divisor `> s` (`s ≈ y^{1/(4k)}`).  A
pigeonhole over cofactors (`exists_pp_fiber_local`) yields a fiber `F` of
size `r ≈ exp (2k √(2 loglog y))`; then `n = m₀ * ∏_{a ∈ F'} a / m₀`
satisfies `r ≤ dA A n` while `n ≤ y^{r+1}` and `n + 1 ≥ U`, so the Case-A
hypothesis bounds `recipSum A (n+1)` and contradicts `hcon`.

This file is self-contained: it reproduces locally (as private lemmas) the
fiber/cofactor estimates and the asymptotic "eventually" bounds.
-/

namespace JSP361

open Finset Filter Asymptotics
open scoped Classical

/-! ### Rough vs smooth partition -/

private theorem rough_iff_not_smooth {a s : ℕ} :
    (∃ p : ℕ, p.Prime ∧ ∃ e : ℕ, 1 ≤ e ∧ s < p ^ e ∧ p ^ e ∣ a) ↔
      ¬ (∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e → p ^ e ∣ a → p ^ e ≤ s) := by
  constructor
  · rintro ⟨p, hp, e, he, hlt, hdvd⟩ hall
    exact (Nat.not_le.mpr hlt) (hall p hp e he hdvd)
  · intro h
    push_neg at h
    obtain ⟨p, hp, e, he, hdvd, hle⟩ := h
    exact ⟨p, hp, e, he, hle, hdvd⟩

/-! ### Fiber / cofactor lemmas -/

/-- Pigeonhole over cofactors: if every `a ∈ S` has a divisor `> s`, then
some cofactor `m₀ ≤ y/s` supports a large fiber `F ⊆ S`. -/
private theorem exists_pp_fiber_local {S : Finset ℕ}
    (hS0 : ∀ a ∈ S, a ≠ 0) {s y : ℕ} (hs : 0 < s)
    (hSy : ∀ a ∈ S, a < y)
    (hp : ∀ a ∈ S, ∃ q : ℕ, s < q ∧ q ∣ a)
    (hSne : S.Nonempty) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ m₀ ≤ y / s ∧ ∃ F : Finset ℕ, F ⊆ S ∧
      S.card ≤ F.card * (y / s + 1) ∧
      ∀ a ∈ F, m₀ ∣ a ∧ s < a / m₀ := by
  classical
  set q : ℕ → ℕ := fun a ↦ if h : a ∈ S then (hp a h).choose else 1 with hqdef
  have hq_spec : ∀ a, ∀ ha : a ∈ S, s < q a ∧ q a ∣ a := by
    intro a ha
    have e : q a = (hp a ha).choose := dif_pos ha
    rw [e]
    exact (hp a ha).choose_spec
  have hqs : ∀ a ∈ S, s + 1 ≤ q a := fun a ha ↦ Nat.succ_le_of_lt (hq_spec a ha).1
  have hqpos : ∀ a ∈ S, 0 < q a :=
    fun a ha ↦ lt_of_le_of_lt (Nat.zero_le s) (hq_spec a ha).1
  set T := Finset.range (y / s + 1) with hTdef
  set fib : ℕ → Finset ℕ := fun b ↦ S.filter (fun a ↦ a / q a = b) with hfibdef
  have hfle : ∀ a ∈ S, a / q a ≤ y / s := by
    intro a ha
    calc a / q a ≤ a / (s + 1) := Nat.div_le_div_left (hqs a ha) (Nat.succ_pos s)
      _ ≤ y / (s + 1) := Nat.div_le_div_right (hSy a ha).le
      _ ≤ y / s := Nat.div_le_div_left (Nat.le_succ s) hs
  have hsub : S ⊆ T.biUnion fib := by
    intro a ha
    rw [Finset.mem_biUnion]
    exact ⟨a / q a, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hfle a ha)),
      Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  have hTne : T.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  obtain ⟨m₀, hm₀T, hmax⟩ := Finset.exists_max_image T (fun b ↦ (fib b).card) hTne
  set F := fib m₀ with hFdef
  have hcard : S.card ≤ F.card * (y / s + 1) := by
    have h1 : S.card ≤ ∑ b ∈ T, (fib b).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∑ b ∈ T, (fib b).card ≤ (y / s + 1) * F.card := by
      calc ∑ b ∈ T, (fib b).card ≤ ∑ _b ∈ T, F.card :=
            Finset.sum_le_sum fun b hb ↦ hmax b hb
        _ = T.card * F.card := by rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
        _ = (y / s + 1) * F.card := by rw [hTdef, Finset.card_range]
    exact h1.trans (h2.trans_eq (mul_comm _ _))
  have hFne : F.Nonempty := by
    have hScard : 0 < S.card := Finset.card_pos.mpr hSne
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos F.card with hF | hF
    · exfalso
      rw [hF, Nat.zero_mul] at hcard
      omega
    · exact hF
  obtain ⟨a₀, ha₀⟩ := hFne
  have ha₀mem : a₀ ∈ fib m₀ := hFdef ▸ ha₀
  have ha₀S : a₀ ∈ S := Finset.filter_subset _ _ ha₀mem
  have ha₀f : a₀ / q a₀ = m₀ := (Finset.mem_filter.mp ha₀mem).2
  have hm₀pos : 0 < m₀ := by
    rw [← ha₀f]
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (hS0 a₀ ha₀S))
      (hq_spec a₀ ha₀S).2) (hqpos a₀ ha₀S)
  refine ⟨m₀, hm₀pos, ?_, F, Finset.filter_subset _ _, hcard, ?_⟩
  · rw [← ha₀f]; exact hfle a₀ ha₀S
  · intro a ha
    have hamem : a ∈ fib m₀ := hFdef ▸ ha
    have haS : a ∈ S := Finset.filter_subset _ _ hamem
    have haf : a / q a = m₀ := (Finset.mem_filter.mp hamem).2
    have ha_eq : a = m₀ * q a := by
      have h := Nat.div_mul_cancel (hq_spec a haS).2
      rw [haf] at h
      exact h.symm
    refine ⟨⟨q a, ha_eq⟩, ?_⟩
    rw [ha_eq, Nat.mul_div_right _ hm₀pos]
    exact (hq_spec a haS).1

/-- The elements of `F` are distinct divisors of `m₀ * ∏ a/m₀`. -/
private theorem dA_fiber_prod_ge_local (A : Set ℕ) {m₀ : ℕ} {F : Finset ℕ} (hm : 0 < m₀)
    (hF : ∀ a ∈ F, a ∈ A ∧ m₀ ∣ a ∧ a ≠ 0) :
    F.card ≤ dA A (m₀ * ∏ a ∈ F, a / m₀) := by
  have hne : m₀ * ∏ a ∈ F, a / m₀ ≠ 0 := by
    apply mul_ne_zero hm.ne'
    rw [Finset.prod_ne_zero_iff]
    intro a ha
    obtain ⟨-, hdvd, ha0⟩ := hF a ha
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hdvd) hm).ne'
  apply card_le_dA A _ hne
  intro a ha
  obtain ⟨hAa, hdvd, -⟩ := hF a ha
  refine ⟨hAa, ?_⟩
  obtain ⟨c, hc⟩ := hdvd
  have hc' : a / m₀ = c := by rw [hc]; exact Nat.mul_div_right _ hm
  have hd : c ∣ ∏ a' ∈ F, a' / m₀ := by
    have h := Finset.dvd_prod_of_mem (fun a' ↦ a' / m₀) ha
    rwa [hc'] at h
  rw [hc]
  exact mul_dvd_mul_left m₀ hd

/-- Upper bound for the fiber product. -/
private theorem fiber_prod_le_local {m₀ : ℕ} {F : Finset ℕ} {y : ℕ} (hm : m₀ ≤ y)
    (hb : ∀ a ∈ F, a < y) :
    m₀ * ∏ a ∈ F, a / m₀ ≤ y ^ (F.card + 1) := by
  have hle : ∏ a ∈ F, a / m₀ ≤ y ^ F.card := by
    have h : ∏ a ∈ F, a / m₀ ≤ ∏ _a ∈ F, y :=
      Finset.prod_le_prod' (fun a ha ↦ (Nat.div_le_self a m₀).trans (hb a ha).le)
    rwa [Finset.prod_const] at h
  calc m₀ * ∏ a ∈ F, a / m₀ ≤ y * y ^ F.card := Nat.mul_le_mul hm hle
    _ = y ^ (F.card + 1) := (pow_succ' y F.card).symm

/-! ### Tendsto infrastructure -/

private theorem tendsto_logNat :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_loglogNat :
    Tendsto (fun y : ℕ ↦ Real.log (Real.log (y : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_logNat

private theorem tendsto_sqrt_loglogNat :
    Tendsto (fun y : ℕ ↦ Real.sqrt (Real.log (Real.log (y : ℝ)))) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_loglogNat

private theorem tendsto_E_caseA (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun y : ℕ ↦ Real.exp (2 * (k:ℝ) *
      Real.sqrt (2 * Real.log (Real.log (y : ℝ))))) atTop atTop := by
  have h1 : Tendsto (fun y : ℕ ↦ 2 * Real.log (Real.log (y : ℝ))) atTop atTop :=
    tendsto_loglogNat.const_mul_atTop (by norm_num)
  have h2 := Real.tendsto_sqrt_atTop.comp h1
  have h3 := h2.const_mul_atTop (mul_pos two_pos (Nat.cast_pos.mpr hk))
  exact Real.tendsto_exp_atTop.comp h3

/-- `(log y)^r ≤ ε · y^s` eventually, for `s, ε > 0`. -/
private theorem ev_log_pow_le (r s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, (Real.log (y:ℝ))^r ≤ ε * (y:ℝ)^s := by
  have h := (isLittleO_log_rpow_rpow_atTop r hs).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [(isLittleO_iff.mp h) hε, eventually_ge_atTop 1] with y hy hy1
  have hly : (0:ℝ) ≤ Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast hy1)
  have hyR : (0:ℝ) ≤ (y:ℝ)^s := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlogr : (0:ℝ) ≤ Real.log (y:ℝ)^r := Real.rpow_nonneg hly r
  have hy' := hy
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hlogr,
    abs_of_nonneg hyR] at hy'
  exact hy'

/-! ### The five asymptotic bounds -/

/-- `C·(4c·y^{1/(4k)})^k ≤ y/(2·log²y)` eventually (`c = log 4 + 4`). -/
private theorem ev_smooth_bound_caseA (k : ℕ) (hk : 1 ≤ k) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ y : ℕ in atTop,
      C * (4 * (Real.log 4 + 4) * (y : ℝ) ^ ((1:ℝ)/(4*(k:ℝ)))) ^ k
        ≤ (y : ℝ) / (2 * (Real.log (y:ℝ))^2) := by
  have hc4 : (0:ℝ) < Real.log 4 + 4 := by
    have h := Real.log_pos (show (1:ℝ) < 4 by norm_num)
    linarith
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hCk : (0:ℝ) < C*(4*(Real.log 4 + 4))^k := by positivity
  filter_upwards [ev_log_pow_le 2 (1/4) (1/2) (by norm_num) (by norm_num),
    ((tendsto_rpow_atTop (show (0:ℝ) < (1:ℝ)/2 by norm_num)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (C*(4*(Real.log 4+4))^k),
    eventually_ge_atTop 3] with y hlog2 hyC hy3
  have hypos : (0:ℝ) < (y:ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hlogpos : (0:ℝ) < Real.log (y:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hpowk : ((y:ℝ)^((1:ℝ)/(4*(k:ℝ))))^k = (y:ℝ)^((1:ℝ)/4) := by
    rw [← Real.rpow_natCast _ k, ← Real.rpow_mul (Nat.cast_nonneg y)]
    congr 1
    rw [← div_div, div_mul_cancel₀ _ hk0]
  have h14 : (0:ℝ) ≤ (y:ℝ)^((1:ℝ)/4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2l : 2*(Real.log (y:ℝ))^2 ≤ (y:ℝ)^((1:ℝ)/4) := by
    rw [Real.rpow_two] at hlog2
    linarith [hlog2]
  have e14 : (y:ℝ)^((1:ℝ)/4)*(y:ℝ)^((1:ℝ)/4) = (y:ℝ)^((1:ℝ)/2) := by
    rw [← Real.rpow_add hypos]
    congr 1
    norm_num
  have e1 : (y:ℝ)^((1:ℝ)/2)*(y:ℝ)^((1:ℝ)/2) = (y:ℝ) := by
    rw [← Real.rpow_add hypos, show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one]
  have key : C*(4*(Real.log 4+4))^k * ((y:ℝ)^((1:ℝ)/4) * (2*(Real.log (y:ℝ))^2))
      ≤ (y:ℝ) := by
    calc C*(4*(Real.log 4+4))^k * ((y:ℝ)^((1:ℝ)/4) * (2*(Real.log (y:ℝ))^2))
        ≤ C*(4*(Real.log 4+4))^k * ((y:ℝ)^((1:ℝ)/4) * (y:ℝ)^((1:ℝ)/4)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h2l h14) hCk.le
      _ = C*(4*(Real.log 4+4))^k * (y:ℝ)^((1:ℝ)/2) := by rw [e14]
      _ ≤ (y:ℝ)^((1:ℝ)/2) * (y:ℝ)^((1:ℝ)/2) :=
          mul_le_mul_of_nonneg_right hyC
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (y:ℝ) := e1
  rw [mul_pow, hpowk, le_div_iff₀ (mul_pos two_pos (pow_pos hlogpos 2))]
  have e : C*((4*(Real.log 4+4))^k * (y:ℝ)^((1:ℝ)/4)) * (2*(Real.log (y:ℝ))^2)
      = C*(4*(Real.log 4+4))^k * ((y:ℝ)^((1:ℝ)/4) * (2*(Real.log (y:ℝ))^2)) := by
    ring
  rw [e]
  exact key

/-- `E + 1 ≤ y^{1/(4k)}/(4·log²y)` eventually, where
`E = exp(2k√(2·loglog y))`. -/
private theorem ev_fiber_size_caseA (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ y : ℕ in atTop,
      Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) + 1
        ≤ (y:ℝ)^((1:ℝ)/(4*(k:ℝ))) / (4 * (Real.log (y:ℝ))^2) := by
  have hk4 : (0:ℝ) < 4*(k:ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr hk)
  have h8k : (0:ℝ) < 8*(k:ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr hk)
  have h16k : (0:ℝ) < 16*(k:ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr hk)
  have hll := (isLittleO_log_rpow_atTop (show (0:ℝ) < (1:ℝ)/2 by norm_num)).comp_tendsto
    tendsto_logNat
  have ev_ll : ∀ᶠ y:ℕ in atTop,
      Real.log (Real.log (y:ℝ)) ≤ (Real.log (y:ℝ))^((1:ℝ)/2) := by
    filter_upwards [(isLittleO_iff.mp hll) one_pos,
      tendsto_logNat.eventually_ge_atTop 1, eventually_ge_atTop 1] with y hy hyl1 hy1
    have hly : (0:ℝ) ≤ Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast hy1)
    have hll0 : (0:ℝ) ≤ Real.log (Real.log (y:ℝ)) := Real.log_nonneg hyl1
    have hyr : (0:ℝ) ≤ (Real.log (y:ℝ))^((1:ℝ)/2) := Real.rpow_nonneg hly _
    have hy' := hy
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hll0,
      abs_of_nonneg hyr, one_mul] at hy'
    exact hy'
  have h16log2 := tendsto_logNat.eventually_ge_atTop (16*(k:ℝ)*Real.log 2)
  have hlog2ge := tendsto_logNat.eventually_ge_atTop 2
  have hsqrt32 := tendsto_logNat.eventually_ge_atTop ((32*(k:ℝ)^2)^2)
  have hlog2sq := ev_log_pow_le 2 (1/(8*(k:ℝ))) (1/4) (by positivity) (by norm_num)
  filter_upwards [ev_ll, h16log2, hlog2ge, hsqrt32, hlog2sq, eventually_ge_atTop 3]
    with y hll' h16l2 hl2 h32 hlogsq hy3
  have hypos : (0:ℝ) < (y:ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hlogpos : (0:ℝ) < Real.log (y:ℝ) := by linarith
  have hll_nonneg : 0 ≤ Real.log (Real.log (y:ℝ)) := Real.log_nonneg (by linarith)
  have hEge1 : (1:ℝ) ≤
      Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) := by
    have hnn : (0:ℝ) ≤ 2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ))) := by positivity
    calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ _ := Real.exp_le_exp.mpr hnn
  -- `2·llfun ≤ log y` via `loglog y ≤ √(log y)` and `√(log y) ≥ 2`.
  have h2ll : 2*Real.log (Real.log (y:ℝ)) ≤ Real.log (y:ℝ) := by
    have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have h1024 : (1024:ℝ) ≤ (32*(k:ℝ)^2)^2 := by
      calc (1024:ℝ) = (32*1^2)^2 := by norm_num
        _ ≤ (32*(k:ℝ)^2)^2 :=
            pow_le_pow_left₀ (by norm_num)
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ zero_le_one hk1 2) (by norm_num)) 2
    have hL4 : (4:ℝ) ≤ Real.log (y:ℝ) := by linarith [h32, h1024]
    have hsqrt2le : (2:ℝ) ≤ Real.sqrt (Real.log (y:ℝ)) := by
      have h := Real.sqrt_le_sqrt hL4
      rwa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)] at h
    have hloghalf : Real.log (Real.log (y:ℝ)) ≤ Real.sqrt (Real.log (y:ℝ)) := by
      rw [Real.sqrt_eq_rpow]; exact hll'
    have hfin : 2*Real.sqrt (Real.log (y:ℝ)) ≤ Real.log (y:ℝ) :=
      calc 2*Real.sqrt (Real.log (y:ℝ))
          ≤ Real.sqrt (Real.log (y:ℝ))*Real.sqrt (Real.log (y:ℝ)) :=
            mul_le_mul_of_nonneg_right hsqrt2le (Real.sqrt_nonneg _)
        _ = Real.log (y:ℝ) := Real.mul_self_sqrt hlogpos.le
    linarith [hloghalf, hfin]
  have hsqrt1 : Real.sqrt (2*Real.log (Real.log (y:ℝ))) ≤ Real.sqrt (Real.log (y:ℝ)) :=
    Real.sqrt_le_sqrt h2ll
  have hsqrt2 : 32*(k:ℝ)^2 ≤ Real.sqrt (Real.log (y:ℝ)) := by
    have h := Real.sqrt_le_sqrt h32
    rwa [Real.sqrt_sq (by positivity)] at h
  -- `2k·√(2·llfun) ≤ log y/(16k)`
  have hb : 2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))
      ≤ (1/(16*(k:ℝ)))*Real.log (y:ℝ) := by
    have h1 : 2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))
        ≤ 2*(k:ℝ)*Real.sqrt (Real.log (y:ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrt1 (by positivity)
    have h2 : 2*(k:ℝ)*Real.sqrt (Real.log (y:ℝ))
        ≤ (1/(16*(k:ℝ)))*Real.log (y:ℝ) := by
      rw [show (1/(16*(k:ℝ)))*Real.log (y:ℝ) = Real.log (y:ℝ)/(16*(k:ℝ)) from by ring,
        le_div_iff₀ h16k]
      calc (2*(k:ℝ)*Real.sqrt (Real.log (y:ℝ)))*(16*(k:ℝ))
          = (32*(k:ℝ)^2)*Real.sqrt (Real.log (y:ℝ)) := by ring
        _ ≤ Real.sqrt (Real.log (y:ℝ))*Real.sqrt (Real.log (y:ℝ)) :=
            mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _)
        _ = Real.log (y:ℝ) := Real.mul_self_sqrt hlogpos.le
    exact h1.trans h2
  have ha : Real.log 2 ≤ (1/(16*(k:ℝ)))*Real.log (y:ℝ) := by
    rw [show (1/(16*(k:ℝ)))*Real.log (y:ℝ) = Real.log (y:ℝ)/(16*(k:ℝ)) from by ring,
      le_div_iff₀ h16k]
    linarith [h16l2]
  -- `2·E ≤ y^{1/(8k)}` by comparing logarithms.
  have h2E : 2*Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ))))
      ≤ (y:ℝ)^(1/(8*(k:ℝ))) := by
    have harg2 : (0:ℝ) < (y:ℝ)^(1/(8*(k:ℝ))) := Real.rpow_pos_of_pos hypos _
    rw [← Real.log_le_log_iff (by positivity) harg2]
    rw [Real.log_rpow hypos, Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp]
    have hcoef : (1/(8*(k:ℝ)))*Real.log (y:ℝ)
        = (1/(16*(k:ℝ)))*Real.log (y:ℝ) + (1/(16*(k:ℝ)))*Real.log (y:ℝ) := by
      have hk0 : (k:ℝ) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
      field_simp
      ring
    linarith [ha, hb, hcoef]
  -- `4·log²y ≤ y^{1/(8k)}`.
  have h4l : 4*(Real.log (y:ℝ))^2 ≤ (y:ℝ)^(1/(8*(k:ℝ))) := by
    rw [Real.rpow_two] at hlogsq
    linarith [hlogsq]
  have hmul : (Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) + 1) *
      (4*(Real.log (y:ℝ))^2) ≤ (y:ℝ)^(1/(4*(k:ℝ))) := by
    have hE1 : Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) + 1
        ≤ (y:ℝ)^(1/(8*(k:ℝ))) := by
      linarith [h2E, hEge1]
    have hmul' := mul_le_mul h4l hE1 (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc (Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) + 1) *
          (4*(Real.log (y:ℝ))^2)
        = (4*(Real.log (y:ℝ))^2) *
          (Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) + 1) := by ring
      _ ≤ (y:ℝ)^(1/(8*(k:ℝ)))*(y:ℝ)^(1/(8*(k:ℝ))) := hmul'
      _ = (y:ℝ)^((1/(8*(k:ℝ)))+(1/(8*(k:ℝ)))) := (Real.rpow_add hypos _ _).symm
      _ = (y:ℝ)^(1/(4*(k:ℝ))) := by
          congr 1
          have hk0 : (k:ℝ) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
          field_simp
          ring
  rw [le_div_iff₀ (mul_pos (by norm_num) (pow_pos hlogpos 2))]
  exact hmul

/-- `log(2·E·log y + 1) + 1 ≤ 2·loglog y` eventually. -/
private theorem ev_loglog_witness_caseA (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ y : ℕ in atTop,
      Real.log (2 * Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ))))
          * Real.log (y:ℝ) + 1) + 1
        ≤ 2 * Real.log (Real.log (y:ℝ)) := by
  filter_upwards [tendsto_loglogNat.eventually_ge_atTop (2*(Real.log 3 + 1)),
    tendsto_loglogNat.eventually_ge_atTop (32*(k:ℝ)^2),
    tendsto_logNat.eventually_ge_atTop 1]
    with y hll3 hll32 hyl1
  have hlogpos : (0:ℝ) < Real.log (y:ℝ) := by linarith
  have hll_nonneg : 0 ≤ Real.log (Real.log (y:ℝ)) := Real.log_nonneg hyl1
  have hllpos : (0:ℝ) < Real.log (Real.log (y:ℝ)) := by
    have : (0:ℝ) < 32*(k:ℝ)^2 := by positivity
    linarith [hll32]
  have hEge1 : (1:ℝ) ≤
      Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) := by
    have hnn : (0:ℝ) ≤ 2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ))) := by positivity
    calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ _ := Real.exp_le_exp.mpr hnn
  have hEl : (1:ℝ) ≤ Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) *
      Real.log (y:ℝ) := by
    calc (1:ℝ) = 1*1 := by ring
      _ ≤ Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) * Real.log (y:ℝ) :=
          mul_le_mul hEge1 hyl1 zero_le_one (le_trans zero_le_one hEge1)
  have harg : 2*Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) *
      Real.log (y:ℝ) + 1
      ≤ 3*Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ))))*Real.log (y:ℝ) := by
    linarith [hEl]
  have hlog3 : Real.log (2*Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) *
      Real.log (y:ℝ) + 1)
      ≤ Real.log (3*Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) *
          Real.log (y:ℝ)) :=
    Real.log_le_log (by positivity) harg
  have he2 : Real.log (3*Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) *
      Real.log (y:ℝ))
      = Real.log 3 + 2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))
        + Real.log (Real.log (y:ℝ)) := by
    rw [Real.log_mul (mul_pos (by norm_num) (Real.exp_pos _)).ne' hlogpos.ne',
      Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  -- `4k√2 ≤ √llfun` from `32k² ≤ llfun`.
  have h4k : 4*(k:ℝ)*Real.sqrt 2 ≤ Real.sqrt (Real.log (Real.log (y:ℝ))) := by
    have hsq : (4*(k:ℝ)*Real.sqrt 2)^2 = 32*(k:ℝ)^2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    have h := Real.sqrt_le_sqrt hll32
    rwa [← hsq, Real.sqrt_sq (by positivity)] at h
  have hb : 2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))
      ≤ Real.log (Real.log (y:ℝ))/2 := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    have h4 : (4*(k:ℝ)*Real.sqrt 2)*Real.sqrt (Real.log (Real.log (y:ℝ)))
        ≤ Real.log (Real.log (y:ℝ)) := by
      calc (4*(k:ℝ)*Real.sqrt 2)*Real.sqrt (Real.log (Real.log (y:ℝ)))
          ≤ Real.sqrt (Real.log (Real.log (y:ℝ)))*Real.sqrt (Real.log (Real.log (y:ℝ))) :=
            mul_le_mul_of_nonneg_right h4k (Real.sqrt_nonneg _)
        _ = Real.log (Real.log (y:ℝ)) := Real.mul_self_sqrt hll_nonneg
    have e : 2*(k:ℝ)*(Real.sqrt 2 * Real.sqrt (Real.log (Real.log (y:ℝ))))
        = (1/2)*((4*(k:ℝ)*Real.sqrt 2)*Real.sqrt (Real.log (Real.log (y:ℝ)))) := by ring
    rw [e]
    linarith [h4]
  have ha : Real.log 3 + 1 ≤ Real.log (Real.log (y:ℝ))/2 := by linarith [hll3]
  have key : Real.log (3*Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) *
      Real.log (y:ℝ)) ≤ 2*Real.log (Real.log (y:ℝ)) - 1 := by
    rw [he2]
    linarith [hb, ha]
  linarith [hlog3, key]

/-- `C·exp(k·√(2·llfun)) + 1 ≤ exp(2k·√(llfun))` eventually. -/
private theorem ev_final_bound_caseA (k : ℕ) (hk : 1 ≤ k) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ y : ℕ in atTop,
      C * Real.exp ((k:ℝ) * Real.sqrt (2 * Real.log (Real.log (y:ℝ)))) + 1
        ≤ Real.exp (2 * (k:ℝ) * Real.sqrt (Real.log (Real.log (y:ℝ)))) := by
  have hsqrt2lt : Real.sqrt 2 < 2 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2) (show (2:ℝ) < 4 by norm_num)
    rwa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hv : Tendsto (fun y : ℕ ↦ (2 - Real.sqrt 2)*(k:ℝ) *
      Real.sqrt (Real.log (Real.log (y:ℝ)))) atTop atTop :=
    tendsto_sqrt_loglogNat.const_mul_atTop
      (mul_pos (sub_pos.mpr hsqrt2lt) (Nat.cast_pos.mpr hk))
  filter_upwards [tendsto_sqrt_loglogNat.eventually_ge_atTop 1,
    hv.eventually_ge_atTop (Real.log (2*C)),
    tendsto_logNat.eventually_ge_atTop 1] with y hv1 hvC hyl1
  have hll_nonneg : 0 ≤ Real.log (Real.log (y:ℝ)) := Real.log_nonneg hyl1
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have h2kv : (2:ℝ) ≤ 2*(k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ))) := by
    nlinarith [hv1, hk1, Real.sqrt_nonneg (Real.log (Real.log (y:ℝ)))]
  have h2exp : (2:ℝ) ≤ Real.exp (2*(k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ)))) := by
    have hlog2le : Real.log 2 ≤ 2*(k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ))) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith [h, h2kv]
    calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog2le
  have h2C : 2*C ≤ Real.exp ((2 - Real.sqrt 2)*((k:ℝ) *
      Real.sqrt (Real.log (Real.log (y:ℝ))))) := by
    have h : Real.log (2*C) ≤ (2 - Real.sqrt 2)*((k:ℝ) *
        Real.sqrt (Real.log (Real.log (y:ℝ)))) := by
      convert hvC using 1
      ring
    calc (2:ℝ)*C = Real.exp (Real.log (2*C)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr h
  have hshape : (k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))
      = Real.sqrt 2*((k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ)))) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring
  have hsplit : Real.exp (2*(k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ))))
      = Real.exp (Real.sqrt 2*((k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ))))) *
        Real.exp ((2 - Real.sqrt 2)*((k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ))))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hshape, hsplit]
  have hepos : (0:ℝ) < Real.exp (Real.sqrt 2*((k:ℝ) *
    Real.sqrt (Real.log (Real.log (y:ℝ))))) := Real.exp_pos _
  have hhalf : C*Real.exp (Real.sqrt 2*((k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ)))))
      ≤ (1/2)*(Real.exp (Real.sqrt 2*((k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ))))) *
        Real.exp ((2 - Real.sqrt 2)*((k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ)))))) := by
    have h := mul_le_mul_of_nonneg_left h2C hepos.le
    nlinarith [h]
  have h1le : (1:ℝ) ≤ (1/2)*(Real.exp (Real.sqrt 2*((k:ℝ)*
      Real.sqrt (Real.log (Real.log (y:ℝ))))) *
      Real.exp ((2 - Real.sqrt 2)*((k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ)))))) := by
    rw [hsplit] at h2exp
    linarith [h2exp]
  linarith [hhalf, h1le]

/-- `U + 1 ≤ exp((log y/(8k))·E)` eventually. -/
private theorem ev_n_large_caseA (k : ℕ) (hk : 1 ≤ k) (U : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      (U:ℝ) + 1 ≤ Real.exp ((Real.log (y:ℝ)/(8*(k:ℝ))) *
        Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ))))) := by
  have h8k : (0:ℝ) < 8*(k:ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr hk)
  have hUlog : (0:ℝ) ≤ Real.log ((U:ℝ)+1) :=
    Real.log_nonneg (by have : (0:ℝ) ≤ (U:ℝ) := Nat.cast_nonneg _; linarith)
  filter_upwards [tendsto_logNat.eventually_ge_atTop (8*(k:ℝ)*Real.log ((U:ℝ)+1))]
    with y hy
  have hlogy : (0:ℝ) ≤ Real.log (y:ℝ) := by
    have : (0:ℝ) ≤ 8*(k:ℝ)*Real.log ((U:ℝ)+1) :=
      mul_nonneg (by have hkn : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _; linarith) hUlog
    linarith [hy]
  have hEge1 : (1:ℝ) ≤ Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) := by
    have hnn : (0:ℝ) ≤ 2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ))) := by positivity
    calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ _ := Real.exp_le_exp.mpr hnn
  have harg : (0:ℝ) ≤ Real.log (y:ℝ)/(8*(k:ℝ)) := div_nonneg hlogy h8k.le
  have h1 : Real.log ((U:ℝ)+1) ≤ Real.log (y:ℝ)/(8*(k:ℝ)) := by
    rw [le_div_iff₀ h8k]
    linarith [hy]
  calc (U:ℝ)+1 = Real.exp (Real.log ((U:ℝ)+1)) :=
        (Real.exp_log (by positivity : (0:ℝ) < (U:ℝ)+1)).symm
    _ ≤ Real.exp (Real.log (y:ℝ)/(8*(k:ℝ))) := Real.exp_le_exp.mpr h1
    _ ≤ Real.exp ((Real.log (y:ℝ)/(8*(k:ℝ))) *
        Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ))))) := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hEge1 harg
        rwa [mul_one] at h

/-- `⌈y^{1/(4k)}⌉ ≤ y` eventually. -/
private theorem ev_s_le_y_caseA (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ y : ℕ in atTop, ⌈(y:ℝ)^((1:ℝ)/(4*(k:ℝ)))⌉₊ ≤ y := by
  have hk4 : (0:ℝ) < 4*(k:ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr hk)
  filter_upwards [eventually_ge_atTop 1] with y hy
  rw [Nat.ceil_le]
  have hyR : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy
  have h : (y:ℝ)^((1:ℝ)/(4*(k:ℝ))) ≤ (y:ℝ)^(1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hyR (by
      rw [div_le_iff₀ hk4]
      have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      linarith)
  rwa [Real.rpow_one] at h

/-! ### The main theorem -/

theorem divisor_limsup_caseA (A : Set ℕ) (hA : A.Infinite)
    (hU : ∀ M : ℝ, ∃ x : ℕ, M < recipSum A x)
    (hcase : ∃ U : ℕ, ∀ u : ℕ, U ≤ u →
      recipSum A u ≤ Real.exp (Real.sqrt (Real.log (Real.log u))))
    {k : ℕ} (hk : 1 ≤ k) {C : ℝ} (hC : 0 < C) :
    ∃ x : ℕ, ∃ n : ℕ, n < x ∧ C * recipSum A x ^ k < (dA A n : ℝ) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨U, hUbd⟩ := hcase
  obtain ⟨B₁, hB₁⟩ := Filter.eventually_atTop.mp (ev_smooth_bound_caseA k hk C hC)
  obtain ⟨B₂, hB₂⟩ := Filter.eventually_atTop.mp (ev_fiber_size_caseA k hk)
  obtain ⟨B₃, hB₃⟩ := Filter.eventually_atTop.mp (ev_loglog_witness_caseA k hk)
  obtain ⟨B₄, hB₄⟩ := Filter.eventually_atTop.mp (ev_final_bound_caseA k hk C hC)
  obtain ⟨B₅, hB₅⟩ := Filter.eventually_atTop.mp (ev_n_large_caseA k hk U)
  obtain ⟨B₆, hB₆⟩ := Filter.eventually_atTop.mp (ev_s_le_y_caseA k hk)
  obtain ⟨B₇, hB₇⟩ :=
    Filter.eventually_atTop.mp ((tendsto_E_caseA k hk).eventually_ge_atTop 2)
  obtain ⟨B₈, hB₈⟩ := Filter.eventually_atTop.mp (tendsto_logNat.eventually_ge_atTop 2)
  set B := B₁ + B₂ + B₃ + B₄ + B₅ + B₆ + B₇ + B₈ + 16 with hBdef
  obtain ⟨y, hyB, hdense⟩ := exists_countA_ge_div_log_sq A hU B
  have hB₁y : B₁ ≤ y := le_trans (by rw [hBdef]; omega) hyB
  have hB₂y : B₂ ≤ y := le_trans (by rw [hBdef]; omega) hyB
  have hB₃y : B₃ ≤ y := le_trans (by rw [hBdef]; omega) hyB
  have hB₄y : B₄ ≤ y := le_trans (by rw [hBdef]; omega) hyB
  have hB₅y : B₅ ≤ y := le_trans (by rw [hBdef]; omega) hyB
  have hB₆y : B₆ ≤ y := le_trans (by rw [hBdef]; omega) hyB
  have hB₇y : B₇ ≤ y := le_trans (by rw [hBdef]; omega) hyB
  have hB₈y : B₈ ≤ y := le_trans (by rw [hBdef]; omega) hyB
  have hy16N : 16 ≤ y := le_trans (by rw [hBdef]; omega) hyB
  -- the eventual bounds, instantiated at the dense scale `y`
  have hsmooth := hB₁ y hB₁y
  have hfiber := hB₂ y hB₂y
  have hloglogbd := hB₃ y hB₃y
  have hfinal := hB₄ y hB₄y
  have hUn := hB₅ y hB₅y
  have hsy := hB₆ y hB₆y
  have hE2 := hB₇ y hB₇y
  have hlog2 := hB₈ y hB₈y
  -- abbreviations
  set E : ℝ := Real.exp (2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) with hEdef
  set s : ℕ := ⌈(y:ℝ)^((1:ℝ)/(4*(k:ℝ)))⌉₊ with hsdef
  set r : ℕ := ⌈E⌉₊ with hrdef
  -- basic facts
  have hy16 : (16:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy16N
  have hypos : (0:ℝ) < (y:ℝ) := by linarith
  have hyR1 : (1:ℝ) ≤ (y:ℝ) := by linarith
  have hlogpos : (0:ℝ) < Real.log (y:ℝ) := by linarith
  have hlog1 : (1:ℝ) ≤ Real.log (y:ℝ) := by linarith
  have hll_nonneg : 0 ≤ Real.log (Real.log (y:ℝ)) := Real.log_nonneg hlog1
  have hEge1 : (1:ℝ) ≤ E := by
    have hnn : (0:ℝ) ≤ 2*(k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ))) := by positivity
    calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ E := Real.exp_le_exp.mpr hnn
  have hs_pos : 0 < s := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hypos _)
  have hs_ge : (y:ℝ)^((1:ℝ)/(4*(k:ℝ))) ≤ (s:ℝ) := Nat.le_ceil _
  have hr_ge_E : E ≤ (r:ℝ) := Nat.le_ceil _
  have hr_le : (r:ℝ) ≤ E + 1 := (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
  -- polynomial bound on `s`-smooth elements of `A` below `y`
  have hc4pos : (0:ℝ) < Real.log 4 + 4 := by
    have h := Real.log_pos (show (1:ℝ) < 4 by norm_num)
    linarith
  have hyqk : (1:ℝ) ≤ (y:ℝ)^((1:ℝ)/(4*(k:ℝ))) :=
    Real.one_le_rpow hyR1 (by positivity)
  have hs2 : (s:ℝ) ≤ 2*(y:ℝ)^((1:ℝ)/(4*(k:ℝ))) := by
    have h : (s:ℝ) < (y:ℝ)^((1:ℝ)/(4*(k:ℝ))) + 1 := by
      rw [hsdef]
      exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    linarith [h, hyqk]
  have h2cs : 2 + (Real.log 4 + 4)*(s:ℝ)
      ≤ 4*(Real.log 4 + 4)*(y:ℝ)^((1:ℝ)/(4*(k:ℝ))) := by
    have h1 : (1:ℝ) ≤ (Real.log 4 + 4)*(y:ℝ)^((1:ℝ)/(4*(k:ℝ))) := by
      have hc41 : (1:ℝ) ≤ Real.log 4 + 4 := by
        have hnn := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
        linarith
      calc (1:ℝ) = 1*1 := by ring
        _ ≤ _ := mul_le_mul hc41 hyqk zero_le_one (by linarith [hc41])
    have h2 : (Real.log 4+4)*(s:ℝ) ≤ (Real.log 4+4)*(2*(y:ℝ)^((1:ℝ)/(4*(k:ℝ)))) :=
      mul_le_mul_of_nonneg_left hs2 hc4pos.le
    nlinarith [h1, h2]
  have hPbound : (((Finset.range y).filter (fun a ↦ a ∈ A \ {0} ∧
        ∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e → p ^ e ∣ a → p ^ e ≤ s)).card : ℝ)
      ≤ (y:ℝ)/(2*(Real.log (y:ℝ))^2) :=
    (powSmooth_poly_of_hcon A hC hcon s y).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by
        have : (0:ℝ) ≤ (Real.log 4+4)*(s:ℝ) :=
          mul_nonneg hc4pos.le (Nat.cast_nonneg _)
        linarith) h2cs k) hC.le |>.trans hsmooth)
  -- the smooth/rough partition
  set P := (Finset.range y).filter (fun a ↦ a ∈ A \ {0} ∧
      ∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e → p ^ e ∣ a → p ^ e ≤ s) with hPdef
  set S := (Finset.range y).filter (fun a ↦ a ∈ A \ {0} ∧
      ∃ p : ℕ, p.Prime ∧ ∃ e : ℕ, 1 ≤ e ∧ s < p ^ e ∧ p ^ e ∣ a) with hSdef
  have hunion : (Finset.range y).filter (· ∈ A \ {0}) = P ∪ S := by
    rw [hPdef, hSdef, ← Finset.filter_or]
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hlt, hmem⟩
      rcases Classical.em (∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e → p ^ e ∣ a → p ^ e ≤ s)
        with hsm | hsm
      · exact ⟨hlt, Or.inl ⟨hmem, hsm⟩⟩
      · exact ⟨hlt, Or.inr ⟨hmem, rough_iff_not_smooth.mpr hsm⟩⟩
    · rintro ⟨hlt, ⟨hmem, -⟩ | ⟨hmem, -⟩⟩
      exacts [⟨hlt, hmem⟩, ⟨hlt, hmem⟩]
  have hdisj : Disjoint P S := by
    rw [Finset.disjoint_left]
    intro a haP haS
    rw [hPdef, Finset.mem_filter] at haP
    rw [hSdef, Finset.mem_filter] at haS
    exact (rough_iff_not_smooth.mp haS.2.2) haP.2.2
  have hpart : ((Finset.range y).filter (· ∈ A \ {0})).card = P.card + S.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  -- `S.card ≥ y/(2·log²y)`
  have hSlower : (y:ℝ)/(2*(Real.log (y:ℝ))^2) ≤ (S.card:ℝ) := by
    have hcount : (countA A y : ℝ) = (P.card:ℝ) + (S.card:ℝ) := by
      have h := hpart
      rw [← countA_eq_card A y] at h
      exact_mod_cast h
    have hhalf : (y:ℝ)/(Real.log (y:ℝ))^2 - (y:ℝ)/(2*(Real.log (y:ℝ))^2)
        = (y:ℝ)/(2*(Real.log (y:ℝ))^2) := by
      rw [show (y:ℝ)/(2*(Real.log (y:ℝ))^2) = (y:ℝ)/(Real.log (y:ℝ))^2/2 from by
        rw [div_div, mul_comm]]
      ring
    have hS_eq : (S.card:ℝ) = (countA A y : ℝ) - (P.card:ℝ) := by linarith [hcount]
    rw [hS_eq]
    linarith [hdense, hPbound, hhalf]
  -- the fiber construction
  have hS0 : ∀ a ∈ S, a ≠ 0 := by
    intro a ha
    rw [hSdef, Finset.mem_filter] at ha
    exact fun h0 ↦ ha.2.1.2 (Set.mem_singleton_iff.mpr h0)
  have hSy : ∀ a ∈ S, a < y := by
    intro a ha
    rw [hSdef, Finset.mem_filter] at ha
    exact Finset.mem_range.mp ha.1
  have hSne : S.Nonempty := by
    have hpos : (0:ℝ) < (S.card:ℝ) :=
      lt_of_lt_of_le (div_pos hypos (mul_pos two_pos (pow_pos hlogpos 2))) hSlower
    exact Finset.card_pos.mp (Nat.cast_pos.mp hpos)
  have hpp : ∀ a ∈ S, ∃ q : ℕ, s < q ∧ q ∣ a := by
    intro a ha
    rw [hSdef, Finset.mem_filter] at ha
    obtain ⟨-, -, p, hp, e, he, hlt, hdvd⟩ := ha
    exact ⟨p^e, hlt, hdvd⟩
  obtain ⟨m₀, hm₀pos, hm₀le, F, hFS, hcardF, hFprop⟩ :=
    exists_pp_fiber_local hS0 hs_pos hSy hpp hSne
  -- `F.card ≥ s/(4·log²y) ≥ r`
  have hFge : (s:ℝ)/(4*(Real.log (y:ℝ))^2) ≤ (F.card:ℝ) := by
    have hsR : (0:ℝ) < (s:ℝ) := Nat.cast_pos.mpr hs_pos
    have hstep1 : (S.card:ℝ) ≤ (F.card:ℝ)*(2*(y:ℝ)/(s:ℝ)) := by
      have h1 : (S.card:ℝ) ≤ (F.card:ℝ)*(((y/s : ℕ):ℝ) + 1) := by
        have h2 : (S.card:ℝ) ≤ (F.card:ℝ)*(((y/s + 1 : ℕ)):ℝ) := by
          exact_mod_cast hcardF
        rwa [Nat.cast_add, Nat.cast_one] at h2
      have h3 : ((y/s : ℕ):ℝ) + 1 ≤ 2*(y:ℝ)/(s:ℝ) := by
        have hcdl : ((y/s : ℕ):ℝ) ≤ (y:ℝ)/(s:ℝ) := Nat.cast_div_le
        have hyos : (1:ℝ) ≤ (y:ℝ)/(s:ℝ) := by
          rw [le_div_iff₀ hsR, one_mul]
          exact_mod_cast hsy
        have e : 2*(y:ℝ)/(s:ℝ) = (y:ℝ)/(s:ℝ) + (y:ℝ)/(s:ℝ) := by ring
        rw [e]
        exact add_le_add hcdl hyos
      exact h1.trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _))
    have hstep2 : (S.card:ℝ)*(s:ℝ) ≤ (F.card:ℝ)*(2*(y:ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hstep1 hsR.le
      have e : (F.card:ℝ)*(2*(y:ℝ)/(s:ℝ))*(s:ℝ) = (F.card:ℝ)*(2*(y:ℝ)) := by
        field_simp
      rwa [e] at h
    have hF1 : (S.card:ℝ)*(s:ℝ)/(2*(y:ℝ)) ≤ (F.card:ℝ) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(y:ℝ))]
      linarith [hstep2]
    calc (s:ℝ)/(4*(Real.log (y:ℝ))^2)
        = (((y:ℝ)/(2*(Real.log (y:ℝ))^2))*(s:ℝ))/(2*(y:ℝ)) := by
          have hy0 : (y:ℝ) ≠ 0 := hypos.ne'
          have hL0 : Real.log (y:ℝ) ≠ 0 := hlogpos.ne'
          field_simp
          ring
      _ ≤ (S.card:ℝ)*(s:ℝ)/(2*(y:ℝ)) := by
          apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ 2*(y:ℝ))
          exact mul_le_mul_of_nonneg_right hSlower hsR.le
      _ ≤ (F.card:ℝ) := hF1
  have hrleF : r ≤ F.card := by
    have h1 : (r:ℝ) ≤ E + 1 := (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
    have h3 : (y:ℝ)^((1:ℝ)/(4*(k:ℝ)))/(4*(Real.log (y:ℝ))^2)
        ≤ (s:ℝ)/(4*(Real.log (y:ℝ))^2) :=
      div_le_div_of_nonneg_right hs_ge (by positivity)
    have h4 : (r:ℝ) ≤ (F.card:ℝ) := h1.trans (hfiber.trans (h3.trans hFge))
    exact_mod_cast h4
  obtain ⟨F', hF'F, hF'card⟩ := Finset.exists_subset_card_eq hrleF
  -- the witness `n`
  set n := m₀ * ∏ a ∈ F', a / m₀ with hn
  have hF'prop : ∀ a ∈ F', a ∈ A ∧ m₀ ∣ a ∧ a ≠ 0 ∧ s < a / m₀ ∧ a < y := by
    intro a ha
    have hFa := hF'F ha
    have hSa := hFS hFa
    obtain ⟨hdvd, hgt⟩ := hFprop a hFa
    rw [hSdef, Finset.mem_filter] at hSa
    exact ⟨hSa.2.1.1, hdvd, fun h0 ↦ hSa.2.1.2 (Set.mem_singleton_iff.mpr h0), hgt,
      Finset.mem_range.mp hSa.1⟩
  have hdA_ge : r ≤ dA A n := by
    have h := dA_fiber_prod_ge_local A hm₀pos (F := F')
      (fun a ha ↦ ⟨(hF'prop a ha).1, (hF'prop a ha).2.1, (hF'prop a ha).2.2.1⟩)
    rwa [hF'card, ← hn] at h
  have hn_upper : n ≤ y ^ (r + 1) := by
    have h := fiber_prod_le_local (m₀ := m₀) (F := F') (y := y)
      (le_trans hm₀le (Nat.div_le_self _ _))
      (fun a ha ↦ (hF'prop a ha).2.2.2.2)
    rwa [hF'card, ← hn] at h
  have hn_lower : s ^ r ≤ n := by
    have hprod : (s+1)^r ≤ ∏ a ∈ F', a / m₀ := by
      have h := Finset.prod_le_prod' (s := F') (f := fun _ ↦ s+1) (g := fun a ↦ a / m₀)
        (fun a ha ↦ Nat.succ_le_of_lt (hF'prop a ha).2.2.2.1)
      rwa [Finset.prod_const, hF'card] at h
    calc s^r ≤ (s+1)^r := pow_le_pow_left₀ (Nat.zero_le s) (Nat.le_succ s) r
      _ ≤ ∏ a ∈ F', a / m₀ := hprod
      _ ≤ m₀ * ∏ a ∈ F', a / m₀ := Nat.le_mul_of_pos_left _ hm₀pos
      _ = n := hn.symm
  -- `n + 1 ≥ U`, so the Case-A hypothesis applies at `u = n+1`
  have hnU : U ≤ n + 1 := by
    have h1 : (s:ℝ)^r ≤ (n:ℝ) := by exact_mod_cast hn_lower
    have h2 : ((y:ℝ)^((1:ℝ)/(4*(k:ℝ))))^r ≤ (s:ℝ)^r :=
      pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hs_ge r
    have h3 : ((y:ℝ)^((1:ℝ)/(4*(k:ℝ))))^r = (y:ℝ)^((r:ℝ)/(4*(k:ℝ))) := by
      rw [← Real.rpow_natCast _ r, ← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      rw [div_mul_eq_mul_div, one_mul]
    have h4 : (y:ℝ)^((r:ℝ)/(4*(k:ℝ)))
        = Real.exp (Real.log (y:ℝ)*((r:ℝ)/(4*(k:ℝ)))) :=
      Real.rpow_def_of_pos hypos _
    have h5 : Real.exp ((Real.log (y:ℝ)/(8*(k:ℝ)))*E) ≤ (y:ℝ)^((r:ℝ)/(4*(k:ℝ))) := by
      rw [h4]
      apply Real.exp_le_exp.mpr
      have hk4 : (0:ℝ) < 4*(k:ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr hk)
      have hk8 : (0:ℝ) < 8*(k:ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr hk)
      have hinv : (1:ℝ)/(8*(k:ℝ)) ≤ 1/(4*(k:ℝ)) :=
        one_div_le_one_div_of_le hk4 (by linarith)
      have hEl : E*Real.log (y:ℝ) ≤ (r:ℝ)*Real.log (y:ℝ) :=
        mul_le_mul_of_nonneg_right hr_ge_E hlogpos.le
      have hnn : (0:ℝ) ≤ (r:ℝ)*Real.log (y:ℝ) :=
        mul_nonneg (Nat.cast_nonneg _) hlogpos.le
      calc (Real.log (y:ℝ)/(8*(k:ℝ)))*E = (E*Real.log (y:ℝ))/(8*(k:ℝ)) := by ring
        _ ≤ ((r:ℝ)*Real.log (y:ℝ))/(4*(k:ℝ)) := by
            rw [div_le_div_iff₀ hk8 hk4]
            exact (mul_le_mul_of_nonneg_right hEl hk4.le).trans
              (mul_le_mul_of_nonneg_left (by linarith [hk4]) hnn)
        _ = Real.log (y:ℝ)*((r:ℝ)/(4*(k:ℝ))) := by ring
    have h6 : (U:ℝ)+1 ≤ (n:ℝ) := hUn.trans (h5.trans (h3 ▸ h2.trans h1))
    have hU1 : U + 1 ≤ n := by exact_mod_cast h6
    omega
  -- `loglog (n+1) ≤ 2·loglog y`
  have hn1ge : 1 ≤ n := le_trans (Nat.one_le_pow r s hs_pos) hn_lower
  have hlogn1 : (0:ℝ) < Real.log ((n+1:ℕ):ℝ) := by
    apply Real.log_pos
    have h2 : (2:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast (by omega : 2 ≤ n+1)
    linarith
  have hlogle1 : Real.log ((n+1:ℕ):ℝ) ≤ 1 + ((r:ℝ)+1)*Real.log (y:ℝ) := by
    have hn1' : (n:ℝ)+1 ≤ 2*(y:ℝ)^((r:ℝ)+1) := by
      have h1 : (n:ℝ) ≤ (y:ℝ)^((r:ℝ)+1) := by
        have h : (n:ℝ) ≤ ((y^(r+1) : ℕ):ℝ) := by exact_mod_cast hn_upper
        rwa [Nat.cast_pow, ← Real.rpow_natCast _ (r+1), Nat.cast_add, Nat.cast_one] at h
      have h2 : (1:ℝ) ≤ (y:ℝ)^((r:ℝ)+1) := Real.one_le_rpow hyR1 (by positivity)
      linarith
    have e' : ((n+1:ℕ):ℝ) = (n:ℝ)+1 := by push_cast; ring
    calc Real.log ((n+1:ℕ):ℝ) = Real.log ((n:ℝ)+1) := by rw [e']
      _ ≤ Real.log (2*(y:ℝ)^((r:ℝ)+1)) := Real.log_le_log (by linarith) hn1'
      _ = Real.log 2 + ((r:ℝ)+1)*Real.log (y:ℝ) := by
          rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hypos _)),
            Real.log_rpow hypos]
      _ ≤ 1 + ((r:ℝ)+1)*Real.log (y:ℝ) := by
          have h2le : Real.log 2 ≤ 1 := by
            have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
            linarith
          linarith
  have hr1E : (r:ℝ)+1 ≤ 2*E := by linarith [hr_le, hE2]
  have hlogle2 : Real.log ((n+1:ℕ):ℝ) ≤ 2*E*Real.log (y:ℝ) + 1 := by
    have hmul : ((r:ℝ)+1)*Real.log (y:ℝ) ≤ 2*E*Real.log (y:ℝ) :=
      mul_le_mul_of_nonneg_right hr1E hlogpos.le
    linarith [hlogle1, hmul]
  have hll_n : Real.log (Real.log ((n+1:ℕ):ℝ)) ≤ 2*Real.log (Real.log (y:ℝ)) := by
    have hmono : Real.log (Real.log ((n+1:ℕ):ℝ))
        ≤ Real.log (2*E*Real.log (y:ℝ) + 1) :=
      Real.log_le_log hlogn1 hlogle2
    linarith [hmono, hloglogbd]
  -- `recipSum A (n+1) ≤ exp (√(2·loglog y))`
  have hrecip : recipSum A (n+1)
      ≤ Real.exp (Real.sqrt (2*Real.log (Real.log (y:ℝ)))) := by
    have h1 := hUbd (n+1) hnU
    have h2 : Real.sqrt (Real.log (Real.log ((n+1:ℕ):ℝ)))
        ≤ Real.sqrt (2*Real.log (Real.log (y:ℝ))) :=
      Real.sqrt_le_sqrt hll_n
    exact h1.trans (Real.exp_le_exp.mpr h2)
  -- the final contradiction
  have hcontr := hcon (n+1) n (Nat.lt_succ_self n)
  have hpow : recipSum A (n+1)^k
      ≤ (Real.exp (Real.sqrt (2*Real.log (Real.log (y:ℝ)))))^k :=
    pow_le_pow_left₀ (recipSum_nonneg _ _) hrecip k
  have hexp : (Real.exp (Real.sqrt (2*Real.log (Real.log (y:ℝ)))))^k
      = Real.exp ((k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) := by
    rw [← Real.exp_nat_mul]
  have hbig : C * recipSum A (n+1) ^ k + 1 ≤ (r:ℝ) := by
    calc C * recipSum A (n+1) ^ k + 1
        ≤ C * (Real.exp (Real.sqrt (2*Real.log (Real.log (y:ℝ)))))^k + 1 :=
          add_le_add_left (mul_le_mul_of_nonneg_left hpow hC.le) _
      _ = C * Real.exp ((k:ℝ)*Real.sqrt (2*Real.log (Real.log (y:ℝ)))) + 1 := by
          rw [hexp]
      _ ≤ Real.exp (2*(k:ℝ)*Real.sqrt (Real.log (Real.log (y:ℝ)))) := hfinal
      _ ≤ E := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.sqrt_le_sqrt (by linarith [hll_nonneg])
      _ ≤ (r:ℝ) := hr_ge_E
  have hrdA : (r:ℝ) ≤ (dA A n : ℝ) := by exact_mod_cast hdA_ge
  linarith [hbig, hrdA, hcontr]

end JSP361
