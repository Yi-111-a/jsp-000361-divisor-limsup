import JSP361.Defs
import JSP361.Counting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# JSP-000361 — the Case-B record dichotomy (replaces ErSa80 Part II Lemma 1)

Notation: `f(x) = recipSum A x`, `ll x = Real.log (Real.log x)`,
`g(x) = log f(x) / √(ll x)` (the "logarithmic slope" of `f` at `x`).

Under the Case-B hypothesis `hB` (`f(u) > exp (√ll u)` for arbitrarily
large `u`), for every `K ≥ 1` and every lower bound `z` one of the
following holds:

* **Dense branch:** some `x ≥ z` has `f(x) > exp (K·√ll x)` — `g(x) > K`.
* **Controlled-future branch:** some `x ≥ z` with `f(x) > exp(√ll x)`
  satisfies `f(w) ≤ f(x)^{2√(ll w / ll x)}` for every `w ≥ x`.

The second branch is proved by a *doubling chain* argument: if no such
`x` exists, every `x` in `S = {w ≥ z : exp(√ll w) < f(w)}` has a
successor `y > x` in `S` with `g(y) > 2·g(x)`; iterating
`⌈log₂ K⌉ + 1` times contradicts the bound `g ≤ K` on `S`.

For `w ∉ S` (i.e. `f(w) ≤ exp(√ll w)`) and `x ∈ S` the bound
`f(w) ≤ f(x)^{√(ll w/ll x)}` is automatic, since
`f(x)^{√(ll w/ll x)} ≥ exp(√ll x · √(ll w/ll x)) = exp(√ll w)`.
-/

namespace JSP361

open Finset
open scoped Classical

/-- The logarithmic slope `g(w) = log (recipSum A w) / √(log log w)`. -/
noncomputable def grec (A : Set ℕ) (w : ℕ) : ℝ :=
  Real.log (recipSum A w) / Real.sqrt (Real.log (Real.log w))

/-- **Case-B dichotomy.** Either `f` reaches `exp(K·√ll x)` at some `x ≥ z`
(dense regime), or there is a scale `x ≥ z` where `f` has already exceeded
`exp(√ll x)` and all future growth is controlled by
`f(w) ≤ f(x)^{2√(ll w/ll x)}`. -/
theorem caseB_dichotomy (A : Set ℕ)
    (hB : ∀ U : ℕ, ∃ u : ℕ, U ≤ u ∧
      Real.exp (Real.sqrt (Real.log (Real.log (u : ℝ)))) < recipSum A u)
    {K : ℝ} (hK : 1 ≤ K) {z : ℕ} (hz : 16 ≤ z) :
    (∃ x : ℕ, z ≤ x ∧
      Real.exp (K * Real.sqrt (Real.log (Real.log (x : ℝ)))) < recipSum A x) ∨
    (∃ x : ℕ, z ≤ x ∧
      Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ)))) < recipSum A x ∧
      ∀ w : ℕ, x ≤ w → recipSum A w ≤
        (recipSum A x) ^ (2 * Real.sqrt (Real.log (Real.log w) /
          Real.log (Real.log x)))) := by
  -- For `w ≥ 16` we have `log (log w) > 1` (since `log 16 > exp 1`).
  have hll : ∀ w : ℕ, 16 ≤ w → (1 : ℝ) < Real.log (Real.log (w : ℝ)) := by
    intro w hw
    have hw16 : (16 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have he : Real.exp 1 < Real.log 16 := by
      have h16 : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
        norm_num
      have he9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      rw [h16]
      have hnum : (2.7182818286 : ℝ) < 4 * (0.6931471803 : ℝ) := by norm_num
      linarith
    have hle : Real.log 16 ≤ Real.log (w : ℝ) :=
      Real.log_le_log (by norm_num) hw16
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log (Real.log (w : ℝ)) :=
          Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le he hle)
  -- Case split on the dense branch.
  by_cases hDense : ∃ x : ℕ, z ≤ x ∧
      Real.exp (K * Real.sqrt (Real.log (Real.log (x : ℝ)))) < recipSum A x
  · exact Or.inl hDense
  push_neg at hDense
  right
  -- Case split on the controlled-future branch.
  by_cases hCtrl : ∃ x : ℕ, z ≤ x ∧
      Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ)))) < recipSum A x ∧
      ∀ w : ℕ, x ≤ w → recipSum A w ≤
        (recipSum A x) ^ (2 * Real.sqrt (Real.log (Real.log w) /
          Real.log (Real.log x)))
  · exact hCtrl
  push_neg at hCtrl
  -- For `x` with `z ≤ x` and `exp(√(ll x)) < f x` we have `1 < g x`.
  have hg1 : ∀ x : ℕ, z ≤ x →
      Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ)))) < recipSum A x →
      1 < grec A x := by
    intro x hxz hx
    have hsx : (0 : ℝ) < Real.sqrt (Real.log (Real.log (x : ℝ))) :=
      Real.sqrt_pos_of_pos (lt_trans zero_lt_one (hll x (le_trans hz hxz)))
    have h1 : Real.sqrt (Real.log (Real.log (x : ℝ))) < Real.log (recipSum A x) := by
      calc Real.sqrt (Real.log (Real.log (x : ℝ)))
          = Real.log (Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ))))) :=
            (Real.log_exp _).symm
        _ < Real.log (recipSum A x) := Real.log_lt_log (Real.exp_pos _) hx
    show 1 < Real.log (recipSum A x) / Real.sqrt (Real.log (Real.log (x : ℝ)))
    rw [lt_div_iff₀ hsx, one_mul]
    exact h1
  -- Failure of the dense branch bounds `g x ≤ K` on the good set.
  have hgK : ∀ x : ℕ, z ≤ x →
      Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ)))) < recipSum A x →
      grec A x ≤ K := by
    intro x hxz hx
    have hsx : (0 : ℝ) < Real.sqrt (Real.log (Real.log (x : ℝ))) :=
      Real.sqrt_pos_of_pos (lt_trans zero_lt_one (hll x (le_trans hz hxz)))
    have hfx : (0 : ℝ) < recipSum A x := lt_trans (Real.exp_pos _) hx
    have hlogle : Real.log (recipSum A x) ≤
        K * Real.sqrt (Real.log (Real.log (x : ℝ))) := by
      calc Real.log (recipSum A x)
          ≤ Real.log (Real.exp (K * Real.sqrt (Real.log (Real.log (x : ℝ))))) :=
            Real.log_le_log hfx (hDense x hxz)
        _ = K * Real.sqrt (Real.log (Real.log (x : ℝ))) := Real.log_exp _
    show Real.log (recipSum A x) / Real.sqrt (Real.log (Real.log (x : ℝ))) ≤ K
    rw [div_le_iff₀ hsx]
    exact hlogle
  -- Failure of the controlled branch yields a successor doubling `g`.
  have hsucc : ∀ x : ℕ, z ≤ x →
      Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ)))) < recipSum A x →
      ∃ w : ℕ, z ≤ w ∧
        Real.exp (Real.sqrt (Real.log (Real.log (w : ℝ)))) < recipSum A w ∧
        2 * grec A x < grec A w := by
    intro x hxz hx
    obtain ⟨w, hwx, hw⟩ := hCtrl x hxz hx
    have h16x : 16 ≤ x := le_trans hz hxz
    have h16w : 16 ≤ w := le_trans h16x hwx
    have hllx : (0 : ℝ) < Real.log (Real.log (x : ℝ)) :=
      lt_trans zero_lt_one (hll x h16x)
    have hllw : (0 : ℝ) < Real.log (Real.log (w : ℝ)) :=
      lt_trans zero_lt_one (hll w h16w)
    have hsx : (0 : ℝ) < Real.sqrt (Real.log (Real.log (x : ℝ))) :=
      Real.sqrt_pos_of_pos hllx
    have hsw : (0 : ℝ) < Real.sqrt (Real.log (Real.log (w : ℝ))) :=
      Real.sqrt_pos_of_pos hllw
    have hfx : (0 : ℝ) < recipSum A x := lt_trans (Real.exp_pos _) hx
    have hfw : (0 : ℝ) < recipSum A w :=
      lt_trans (Real.rpow_pos_of_pos hfx _) hw
    have hlogfx : Real.sqrt (Real.log (Real.log (x : ℝ))) <
        Real.log (recipSum A x) := by
      calc Real.sqrt (Real.log (Real.log (x : ℝ)))
          = Real.log (Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ))))) :=
            (Real.log_exp _).symm
        _ < Real.log (recipSum A x) := Real.log_lt_log (Real.exp_pos _) hx
    have hpos' : (0 : ℝ) < Real.sqrt (Real.log (Real.log (w : ℝ)) /
        Real.log (Real.log (x : ℝ))) :=
      Real.sqrt_pos_of_pos (div_pos hllw hllx)
    have hsqrt : Real.sqrt (Real.log (Real.log (w : ℝ)) /
        Real.log (Real.log (x : ℝ)))
        = Real.sqrt (Real.log (Real.log (w : ℝ))) /
          Real.sqrt (Real.log (Real.log (x : ℝ))) :=
      Real.sqrt_div hllx.le _
    -- Taking logs of `f x ^ (2√(llw/llx)) < f w`.
    have hlogfw : 2 * Real.sqrt (Real.log (Real.log (w : ℝ)) /
          Real.log (Real.log (x : ℝ))) * Real.log (recipSum A x)
        < Real.log (recipSum A w) := by
      calc 2 * Real.sqrt (Real.log (Real.log (w : ℝ)) /
              Real.log (Real.log (x : ℝ))) * Real.log (recipSum A x)
          = Real.log (recipSum A x ^ (2 * Real.sqrt (Real.log (Real.log (w : ℝ)) /
              Real.log (Real.log (x : ℝ))))) := (Real.log_rpow hfx _).symm
        _ < Real.log (recipSum A w) :=
            Real.log_lt_log (Real.rpow_pos_of_pos hfx _) hw
    -- Hence `√(ll w) < log f w`, so `w` is again in the good set.
    have hsw_lt : Real.sqrt (Real.log (Real.log (w : ℝ))) <
        Real.log (recipSum A w) := by
      have key : Real.sqrt (Real.log (Real.log (w : ℝ))) <
          Real.sqrt (Real.log (Real.log (w : ℝ)) / Real.log (Real.log (x : ℝ)))
            * Real.log (recipSum A x) := by
        calc Real.sqrt (Real.log (Real.log (w : ℝ)))
            = Real.sqrt (Real.log (Real.log (w : ℝ)) / Real.log (Real.log (x : ℝ)))
                * Real.sqrt (Real.log (Real.log (x : ℝ))) := by
              rw [hsqrt, div_mul_cancel₀ _ (ne_of_gt hsx)]
          _ < Real.sqrt (Real.log (Real.log (w : ℝ)) / Real.log (Real.log (x : ℝ)))
                * Real.log (recipSum A x) :=
              mul_lt_mul_of_pos_left hlogfx hpos'
      have hpos'' : (0 : ℝ) < Real.sqrt (Real.log (Real.log (w : ℝ)) /
          Real.log (Real.log (x : ℝ))) * Real.log (recipSum A x) :=
        lt_trans hsw key
      linarith
    have hmem : Real.exp (Real.sqrt (Real.log (Real.log (w : ℝ)))) <
        recipSum A w := by
      calc Real.exp (Real.sqrt (Real.log (Real.log (w : ℝ))))
          < Real.exp (Real.log (recipSum A w)) := Real.exp_lt_exp.mpr hsw_lt
        _ = recipSum A w := Real.exp_log hfw
    -- And `g w > 2 g x`.
    have hdbl : 2 * grec A x < grec A w := by
      show 2 * (Real.log (recipSum A x) / Real.sqrt (Real.log (Real.log (x : ℝ))))
          < Real.log (recipSum A w) / Real.sqrt (Real.log (Real.log (w : ℝ)))
      rw [lt_div_iff₀ hsw]
      have heq : 2 * (Real.log (recipSum A x) /
              Real.sqrt (Real.log (Real.log (x : ℝ))))
            * Real.sqrt (Real.log (Real.log (w : ℝ)))
          = 2 * Real.sqrt (Real.log (Real.log (w : ℝ)) /
              Real.log (Real.log (x : ℝ))) * Real.log (recipSum A x) := by
        rw [hsqrt]
        ring
      rw [heq]
      exact hlogfw
    exact ⟨w, le_trans hxz hwx, hmem, hdbl⟩
  -- Iterating the successor `j` times produces `x` with `g x > 2 ^ j`.
  obtain ⟨x0, hx0z, hx0⟩ := hB z
  have hiter : ∀ j : ℕ, ∃ x : ℕ, z ≤ x ∧
      Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ)))) < recipSum A x ∧
      (2 : ℝ) ^ j < grec A x := by
    intro j
    induction j with
    | zero =>
      exact ⟨x0, hx0z, hx0, by simpa using hg1 x0 hx0z hx0⟩
    | succ j ih =>
      obtain ⟨x, hxz, hx, hgx⟩ := ih
      obtain ⟨w, hwz, hw, hgw⟩ := hsucc x hxz hx
      refine ⟨w, hwz, hw, ?_⟩
      calc (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 := pow_succ _ _
        _ < grec A x * 2 := mul_lt_mul_of_pos_right hgx (by norm_num)
        _ = 2 * grec A x := mul_comm _ _
        _ < grec A w := hgw
  -- Choosing `j` with `K < 2 ^ j` contradicts `g x ≤ K`.
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt K (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨x, hxz, hx, hgx⟩ := hiter j
  have hle : grec A x ≤ K := hgK x hxz hx
  linarith

end JSP361
