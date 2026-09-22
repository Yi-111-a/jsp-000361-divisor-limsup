import JSP361.Defs
import JSP361.Basic
import JSP361.Counting
import JSP361.CountA
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# JSP-000361 — record points of `recipSum` (Erdős–Sárközy "Case B" regime)

`recordX A hU F` is the first scale `x` with `F < recipSum A x`; it exists
because the reciprocal sum is unbounded (`hU`).  This file collects the
infrastructure around record points:

* `recordX_spec`, `recordX_min` — `Nat.find` spec/minimality.
* `recordX_pos`, `recordX_le_succ` — a record point is positive and its value
  overshoots `F` by at most `1` (each step of `recipSum` adds `≤ 1`,
  imitating `div_recipSum_succ_le` in `Divergent.lean`).
* `recordX_ge_exp` — `exp (F - 1) ≤ recordX A hU F`, from the universal
  bound `recipSum A x ≤ 1 + log x` (`recipSum_le_log`, `Counting.lean`).
* `divisor_limsup_of_record_win` — Case-B reduction: if arbitrarily far out
  there is a scale `F` and some `n < recordX F` with `C (F+1)^k < dA n`,
  then `C · recipSum x ^ k < dA n` at the record point `x = recordX F`
  (since `recipSum (recordX F) ≤ F + 1`).
* `exists_record_small_loglog` — the record-point translation of Case B:
  from `exp (√(log log u)) < recipSum A u` for arbitrarily large `u`,
  produce arbitrarily large thresholds `F` with
  `log log (recordX F) < (log F)^2`.  The threshold is chosen as the
  midpoint `F = (exp (√(log log u)) + recipSum A u) / 2`, strictly between
  `exp (√(log log u))` and `recipSum A u`, so that `recordX F ≤ u`
  (minimality) while `(log F)^2 > log log u`.
* `divisor_limsup_caseB_reduces` — combines the two: the Case-B hypothesis
  supplies the record scales, and `hwin` supplies the `dA` win at each
  such scale.  (The hypothesis `hA : A.Infinite` is part of the stated
  contract but is not needed for the reduction.)

## Statement notes

All statements match the requested contract verbatim.  The proofs below are
complete (no placeholders, no extra axioms).
-/

namespace JSP361

open Classical

/-- The first scale where `recipSum A` exceeds `F`. -/
noncomputable def recordX (A : Set ℕ) (hU : ∀ M : ℝ, ∃ x : ℕ, M < recipSum A x)
    (F : ℝ) : ℕ := Nat.find (hU F)

theorem recordX_spec (A : Set ℕ) (hU : ∀ M : ℝ, ∃ x, M < recipSum A x) (F : ℝ) :
    F < recipSum A (recordX A hU F) :=
  Nat.find_spec (hU F)

theorem recordX_min (A : Set ℕ) (hU : ∀ M : ℝ, ∃ x, M < recipSum A x) (F : ℝ)
    {u : ℕ} (hu : u < recordX A hU F) : recipSum A u ≤ F :=
  not_lt.mp (Nat.find_min (hU F) hu)

theorem recordX_pos (A : Set ℕ) (hU : ∀ M : ℝ, ∃ x, M < recipSum A x) {F : ℝ}
    (hF : 0 ≤ F) : 0 < recordX A hU F := by
  rcases Nat.eq_zero_or_pos (recordX A hU F) with h0 | h0
  · exfalso
    have hspec := recordX_spec A hU F
    rw [h0] at hspec
    have hz : recipSum A 0 = 0 := by simp [recipSum]
    rw [hz] at hspec
    linarith
  · exact h0

/-- Increments of `recipSum` are `≤ 1` (one element contributes `≤ 1/a`). -/
private theorem record_recipSum_succ_le (A : Set ℕ) (x : ℕ) :
    recipSum A (x + 1) ≤ recipSum A x + 1 := by
  have hsucc : recipSum A (x + 1)
      = recipSum A x + (if x ∈ A then (1 : ℝ) / x else 0) := by
    unfold recipSum
    rw [Finset.sum_range_succ]
  rw [hsucc]
  rcases Nat.eq_zero_or_pos x with rfl | hxpos
  · simp
  · have hbound : (if x ∈ A then (1 : ℝ) / x else 0) ≤ 1 := by
      split_ifs with hx
      · have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
        calc (1 : ℝ) / x ≤ 1 / 1 := one_div_le_one_div_of_le zero_lt_one hx1
          _ = 1 := by norm_num
      · exact zero_le_one
    linarith

theorem recordX_le_succ (A : Set ℕ) (hU : ∀ M : ℝ, ∃ x, M < recipSum A x)
    {F : ℝ} (hF : 0 ≤ F) :
    recipSum A (recordX A hU F) ≤ F + 1 := by
  have hxpos := recordX_pos A hU hF
  have hprev : recipSum A (recordX A hU F - 1) ≤ F :=
    recordX_min A hU F (Nat.sub_lt hxpos zero_lt_one)
  have hle := record_recipSum_succ_le A (recordX A hU F - 1)
  rw [Nat.sub_add_cancel hxpos] at hle
  linarith

theorem recordX_ge_exp (A : Set ℕ) (hU : ∀ M : ℝ, ∃ x, M < recipSum A x)
    {F : ℝ} (hF : 0 ≤ F) :
    Real.exp (F - 1) ≤ (recordX A hU F : ℝ) := by
  have hspec := recordX_spec A hU F
  have hlog := recipSum_le_log A (recordX A hU F)
  have hlt : F - 1 < Real.log (recordX A hU F : ℝ) := by linarith
  have hxpos := recordX_pos A hU hF
  have hx0 : (0 : ℝ) < (recordX A hU F : ℝ) := by exact_mod_cast hxpos
  apply le_of_lt
  calc Real.exp (F - 1) < Real.exp (Real.log (recordX A hU F : ℝ)) :=
        Real.exp_lt_exp.mpr hlt
    _ = (recordX A hU F : ℝ) := Real.exp_log hx0

/-- **Case-B reduction.** If for arbitrarily large thresholds `F` there is a
counter `n < recordX A hU F` with `C (F+1)^k < dA A n`, then the limsup
statement holds at the record points themselves. -/
theorem divisor_limsup_of_record_win (A : Set ℕ) (hU : ∀ M : ℝ, ∃ x, M < recipSum A x)
    (k : ℕ) {C : ℝ} (hC : 0 < C)
    (hwin : ∀ F₀ : ℝ, ∃ F : ℝ, F₀ ≤ F ∧ ∃ n : ℕ, n < recordX A hU F ∧
      C * (F + 1) ^ k < (dA A n : ℝ)) :
    ∃ x : ℕ, ∃ n : ℕ, n < x ∧ C * recipSum A x ^ k < (dA A n : ℝ) := by
  obtain ⟨F, hF0, n, hn, hdA⟩ := hwin 0
  exact ⟨recordX A hU F, n, hn,
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (recipSum_nonneg A _) (recordX_le_succ A hU hF0) k)
        hC.le)
      hdA⟩

/-- **Record-point translation of Case B.** If `recipSum A u` exceeds
`exp (√(log log u))` for arbitrarily large `u`, then for arbitrarily large
thresholds `F` the record point `recordX A hU F` satisfies
`log log (recordX F) < (log F)^2`. -/
theorem exists_record_small_loglog (A : Set ℕ) (hU : ∀ M : ℝ, ∃ x, M < recipSum A x)
    (hB : ∀ U : ℕ, ∃ u : ℕ, U ≤ u ∧
      Real.exp (Real.sqrt (Real.log (Real.log u))) < recipSum A u) :
    ∀ F₀ : ℝ, ∃ F : ℝ, F₀ ≤ F ∧
      Real.log (Real.log (recordX A hU F)) < (Real.log F) ^ 2 := by
  intro F₀
  -- Pick `u` so large that `exp (√(log log u)) ≥ max F₀ 1`.
  set L : ℝ := Real.log (max F₀ 1) with hLdef
  have hLnn : 0 ≤ L := Real.log_nonneg (le_max_right _ _)
  obtain ⟨u, huU, huB⟩ := hB ⌈Real.exp (Real.exp (L ^ 2))⌉₊
  have huR : Real.exp (Real.exp (L ^ 2)) ≤ (u : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast huU)
  have hlogu : Real.exp (L ^ 2) ≤ Real.log (u : ℝ) := by
    have h1 := Real.log_le_log (Real.exp_pos _) huR
    rwa [Real.log_exp] at h1
  have hloglog : L ^ 2 ≤ Real.log (Real.log (u : ℝ)) := by
    have h2 := Real.log_le_log (Real.exp_pos _) hlogu
    rwa [Real.log_exp] at h2
  have hloglogu : 0 ≤ Real.log (Real.log (u : ℝ)) := le_trans (sq_nonneg L) hloglog
  have hsqrt : L ≤ Real.sqrt (Real.log (Real.log (u : ℝ))) := by
    have hs := Real.sqrt_le_sqrt hloglog
    rwa [Real.sqrt_sq hLnn] at hs
  -- The threshold: midpoint of `exp (√(log log u))` and `recipSum A u`.
  set e : ℝ := Real.exp (Real.sqrt (Real.log (Real.log (u : ℝ)))) with he_def
  set F : ℝ := (e + recipSum A u) / 2 with hF_def
  have hepos : 0 < e := by rw [he_def]; exact Real.exp_pos _
  have hFe : e < F := by rw [hF_def]; linarith [huB]
  have hFr : F < recipSum A u := by rw [hF_def]; linarith [huB]
  have hFnn : 0 ≤ F := (lt_trans hepos hFe).le
  have hF0 : F₀ ≤ F := by
    have hstep : max F₀ 1 ≤ e := by
      rw [he_def]
      calc max F₀ 1 = Real.exp L := by
            rw [hLdef]
            exact (Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_right _ _))).symm
        _ ≤ Real.exp (Real.sqrt (Real.log (Real.log (u : ℝ)))) :=
            Real.exp_le_exp.mpr hsqrt
    exact (le_max_left _ _).trans (hstep.trans hFe.le)
  refine ⟨F, hF0, ?_⟩
  -- `F < recipSum A u` forces `recordX F ≤ u` by minimality.
  have hrle : recordX A hU F ≤ u := Nat.find_min' hFr
  have hrpos := recordX_pos A hU hFnn
  -- `log F > √(log log u)`, so `(log F)^2 > log log u`.
  have hlogF : Real.sqrt (Real.log (Real.log (u : ℝ))) < Real.log F := by
    have h1 := Real.log_lt_log hepos hFe
    rw [he_def, Real.log_exp] at h1
    exact h1
  have hsqF : Real.log (Real.log (u : ℝ)) < (Real.log F) ^ 2 := by
    have hs : (Real.sqrt (Real.log (Real.log (u : ℝ)))) ^ 2 < (Real.log F) ^ 2 :=
      pow_lt_pow_left₀ hlogF (Real.sqrt_nonneg _) two_ne_zero
    rwa [Real.sq_sqrt hloglogu] at hs
  -- `log log` is monotone where positive; `recordX F ≤ u` finishes it.
  have hll : Real.log (Real.log (recordX A hU F : ℝ)) ≤
      Real.log (Real.log (u : ℝ)) := by
    rcases lt_or_ge (recordX A hU F) 2 with h1 | h1
    · have hr1 : recordX A hU F = 1 := by omega
      rw [hr1]
      simp only [Nat.cast_one, Real.log_one, Real.log_zero]
      exact hloglogu
    · have hr2 : (2 : ℝ) ≤ (recordX A hU F : ℝ) := by exact_mod_cast h1
      have hlogr_pos : 0 < Real.log (recordX A hU F : ℝ) :=
        lt_of_lt_of_le (Real.log_pos one_lt_two)
          (Real.log_le_log (by norm_num) hr2)
      have hlogle : Real.log (recordX A hU F : ℝ) ≤ Real.log (u : ℝ) :=
        Real.log_le_log (by exact_mod_cast hrpos) (by exact_mod_cast hrle)
      exact Real.log_le_log hlogr_pos hlogle
  exact lt_of_le_of_lt hll hsqF

/-- **Case B reduces to a `dA` win at record scales.** Under the Case-B
hypothesis `hB`, if every nonneg threshold `F` with small
`log log (recordX F)` has a counter `n < recordX F` beating
`C (F+1)^k`, the limsup statement holds. -/
theorem divisor_limsup_caseB_reduces (A : Set ℕ) (hA : A.Infinite)
    (hU : ∀ M : ℝ, ∃ x, M < recipSum A x)
    (hB : ∀ U : ℕ, ∃ u : ℕ, U ≤ u ∧
      Real.exp (Real.sqrt (Real.log (Real.log u))) < recipSum A u)
    (k : ℕ) {C : ℝ} (hC : 0 < C)
    (hwin : ∀ F : ℝ, 0 ≤ F →
      Real.log (Real.log (recordX A hU F)) < (Real.log F)^2 →
      ∃ n : ℕ, n < recordX A hU F ∧ C * (F + 1) ^ k < (dA A n : ℝ)) :
    ∃ x n, n < x ∧ C * recipSum A x ^ k < dA A n := by
  apply divisor_limsup_of_record_win A hU k hC
  intro F₀
  obtain ⟨F, hF0, hloglog⟩ := exists_record_small_loglog A hU hB (max F₀ 0)
  have hFnn : 0 ≤ F := (le_max_right F₀ 0).trans hF0
  obtain ⟨n, hn, hdA⟩ := hwin F hFnn hloglog
  exact ⟨F, (le_max_left F₀ 0).trans hF0, n, hn, hdA⟩

end JSP361
