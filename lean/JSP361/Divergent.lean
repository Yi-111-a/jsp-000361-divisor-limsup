import JSP361.Defs
import JSP361.LcmWin
import JSP361.ChebBound
import JSP361.BandDensity
import JSP361.CaseA
import JSP361.CaseB
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Finite.Basic

/-!
# JSP-000361 — divergent case of the Erdős–Sárközy limsup theorem

Target (Erdős–Sárközy, *Some asymptotic formulas on generalized divisor
functions*; the divergent case of ErSa80, Studia Sci. Math. Hungar. 15 (1980)
467–479, quoting Parts I–II): for infinite `A ⊆ ℕ` with divergent reciprocal
sum (`hU`), the ratio `max_{n<x} d_A(n) / recipSum A x ^ k` is unbounded for
every `k`.

## What is proved here

* `div_recipSum_zero`, `div_recipSum_nonneg`, `div_recipSum_mono`,
  `div_recipSum_succ`, `div_recipSum_succ_le` — elementary properties of
  `recipSum` (nonnegativity, monotonicity, increments `≤ 1`).
* `div_card_le_dA`, `div_dA_prod_ge`, `div_dA_lcm_ge` — lower bounds for
  `dA`: a finite set `F ⊆ A` of nonzero elements contributes `F.card`
  divisors to `∏ F` and to `lcm F`.
* `div_first_crossing` — since `recipSum A` is unbounded, for every `M ≥ 0`
  there is a *first* scale `x` with
  `recipSum A (x-1) ≤ M < recipSum A x ≤ M + 1`.
* `div_counter_bound`, `div_counter_bound_lcm` — the *forcing* consequence
  of the negation of the theorem: if `dA A n ≤ C * recipSum A x ^ k` for all
  `n < x`, then every finite `F ⊆ A ∖ {0}` satisfies
  `F.card ≤ C * recipSum A (∏F + 1) ^ k` (and likewise for `lcm F`).
* The main theorem for `C ≤ 0` (any `k`) and for `k = 0` (any `C`): products
  of finite subsets of `A ∖ {0}` already give arbitrarily large `dA`.

## The `k ≥ 1`, `C > 0` case (closed via CaseA/CaseB below)

For `k ≥ 1` and `C > 0` the statement is the content of ErSa80 Part I
(`k = 1`: `lim sup D_A/f_A = ∞`, their Theorem 6) sharpened in Part II to
`lim sup D_A(x)/exp(c·(log f_A(x))²) = ∞`, which dominates every `C·f_A^k`.
The mathematics, assuming `dA(n) ≤ C·recipSum(n+1)^k` for all `n`:

1. *Partial summation*: `recipSum A x = N_A(x)/x + ∫_{1}^{x} N_A(t)/t² dt`
   (with `N_A` the counting function).  Hence divergence forces
   `N_A(y) ≥ y/(log y)^{1+ε}` for infinitely many `y` (else the integral
   converges).  No Abel-summation infrastructure for `recipSum`/`N_A`
   exists yet in this project.
2. *Smooth-restricted lcm* (ErSa Thm. 3): among the `a ∈ A ∩ [1,y]` keep
   only `t`-smooth elements (`t ≈ log y / log log y`), losing at most a
   constant fraction of the count — this needs upper bounds on counts of
   `t`-rough integers (Mertens-type or sieve bounds) — and take
   `X = lcm` of the survivors: `log X ≲ π(t)·log y` via Chebyshev
   (`primorial ≤ 4^t` in Mathlib).  Then `dA(X) ≳ N_A(y)` at a point where
   `recipSum(X)` is only `O(log X)`, forcing `dA(X) > C·recipSum(X)^k`.
3. *Multi-scale bookkeeping* (ErSa Thm. 6 / Part II): the estimates must be
   run at the forced scales `y_i → ∞` and iterated to beat every fixed
   power `k`.

Step 2 is the genuinely hard, research-level input; the naive
product/lcm-of-everything constructions only yield the consistent
inequality `N_A(y) ≤ C·(1 + c₀·y)^k` (see `div_counter_bound_lcm` at the
`lcm ≤ 4^y` scale), which does not contradict anything.

## Round-6 reduction (proved below)

The negation of the goal, evaluated at `x = Nat.lcmUpto t + 1`
(`lcmUpto t = lcm(1,…,t)`, divisible by every `a ≤ t`; `log lcmUpto t`
`= ψ(t) ≤ (log 4 + 4)·t` by Chebyshev — `JSP361/ChebBound.lean`), yields
for EVERY `t`:

    `countA A (t + 1) ≤ C · recipSum A (⌈e^{(log4+4)·t}⌉ + 1)^{k+1}`.

Combined with the partial-summation density scales (`countA A y ≥
y/(log y)²` i.o., `JSP361/Density.lean`), this forces `recipSum`'s mass
into the bands `(t, e^{(log4+4)·t}]` and forces most elements to carry a
prime-power factor `> √y` (see `JSP361/RoughElem.lean` for the
`a ∣ lcmUpto t ↔ ∀ p^e ‖ a, p^e ≤ t` characterization).  The remaining
branch is the multiplicatively-dense regime handled by ErSa80
Part II; it is closed by `divisor_limsup_caseA` / `divisor_limsup_caseB`
(`JSP361/CaseA.lean`, `JSP361/CaseB.lean`, via `JSP361/ErSaCore.lean`).
-/

namespace JSP361

open Finset
open Classical

/-! ### Elementary properties of `recipSum` -/

private theorem div_recipSum_zero (A : Set ℕ) : recipSum A 0 = 0 := by
  simp [recipSum]

private theorem div_term_nonneg (A : Set ℕ) (a : ℕ) :
    0 ≤ (if a ∈ A then (1 : ℝ) / a else 0) := by
  split_ifs with ha
  · positivity
  · exact le_refl 0

private theorem div_recipSum_nonneg (A : Set ℕ) (x : ℕ) :
    0 ≤ recipSum A x := by
  unfold recipSum
  exact Finset.sum_nonneg fun a _ => div_term_nonneg A a

private theorem div_recipSum_mono (A : Set ℕ) : Monotone (recipSum A) := by
  intro x y hxy
  unfold recipSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr hxy
  · intro a _ _
    exact div_term_nonneg A a

/-- The `x+1` step of `recipSum` adds at most `1/x`-mass. -/
private theorem div_recipSum_succ (A : Set ℕ) (x : ℕ) :
    recipSum A (x + 1)
      = recipSum A x + (if x ∈ A then (1 : ℝ) / x else 0) := by
  unfold recipSum
  rw [Finset.sum_range_succ]

/-- Increments of `recipSum` are `≤ 1`. -/
private theorem div_recipSum_succ_le (A : Set ℕ) (x : ℕ) :
    recipSum A (x + 1) ≤ recipSum A x + 1 := by
  rw [div_recipSum_succ]
  rcases Nat.eq_zero_or_pos x with rfl | hxpos
  · simp
  · have hbound : (if x ∈ A then (1 : ℝ) / x else 0) ≤ 1 := by
      split_ifs with hx
      · have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
        calc (1 : ℝ) / x ≤ 1 / 1 :=
              one_div_le_one_div_of_le zero_lt_one hx1
          _ = 1 := by norm_num
      · exact zero_le_one
    linarith

/-! ### Lower bounds for `dA` -/

/-- If every member of `F` lies in `A` and divides `n` (with `n ≠ 0`), then
`F.card ≤ dA A n`. -/
private theorem div_card_le_dA (A : Set ℕ) {n : ℕ} (hn : n ≠ 0) {F : Finset ℕ}
    (hF : ∀ a ∈ F, a ∈ A ∧ a ∣ n) : F.card ≤ dA A n := by
  apply Finset.card_le_card
  intro a ha
  obtain ⟨hAa, han⟩ := hF a ha
  rw [Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨han, hn⟩, hAa⟩

/-- The product of a finite `F ⊆ A ∖ {0}` is divisible by every member of `F`,
hence `F.card ≤ dA A (∏ F)`. -/
private theorem div_dA_prod_ge (A : Set ℕ) {F : Finset ℕ}
    (hFA : ∀ a ∈ F, a ∈ A) (h0 : 0 ∉ F) :
    F.card ≤ dA A (∏ a ∈ F, a) := by
  have hne : (∏ a ∈ F, a) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro a ha
    exact fun h => h0 (h ▸ ha)
  apply div_card_le_dA A hne
  intro a ha
  exact ⟨hFA a ha, Finset.dvd_prod_of_mem _ ha⟩

/-- The lcm of a finite `F ⊆ A ∖ {0}` is divisible by every member of `F`,
hence `F.card ≤ dA A (lcm F)`. -/
private theorem div_dA_lcm_ge (A : Set ℕ) {F : Finset ℕ}
    (hFA : ∀ a ∈ F, a ∈ A) (h0 : 0 ∉ F) :
    F.card ≤ dA A (F.lcm id) := by
  have hne : F.lcm id ≠ 0 := by
    intro h
    rw [Finset.lcm_eq_zero_iff] at h
    obtain ⟨a, ha, ha0⟩ := h
    have h00 : a = 0 := ha0
    exact h0 (h00 ▸ ha)
  apply div_card_le_dA A hne
  intro a ha
  exact ⟨hFA a ha, Finset.dvd_lcm ha⟩

/-! ### First crossing of a level by `recipSum` -/

/-- Since `recipSum A` is unbounded, for every `M ≥ 0` there is a first
`x > 0` with `recipSum A (x-1) ≤ M < recipSum A x`; the jump is `≤ 1`, so
also `recipSum A x ≤ M + 1`. -/
private theorem div_first_crossing (A : Set ℕ)
    (hU : ∀ M : ℝ, ∃ x : ℕ, M < recipSum A x) {M : ℝ} (hM : 0 ≤ M) :
    ∃ x : ℕ, 0 < x ∧ recipSum A (x - 1) ≤ M ∧ M < recipSum A x ∧
      recipSum A x ≤ M + 1 := by
  obtain ⟨x₀, hx₀⟩ := hU M
  have hex : ∃ x, M < recipSum A x := ⟨x₀, hx₀⟩
  set x := Nat.find hex with hxdef
  have hxspec : M < recipSum A x := Nat.find_spec hex
  have hxpos : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · exfalso
      rw [h0, div_recipSum_zero] at hxspec
      linarith
    · exact h0
  have hprev : recipSum A (x - 1) ≤ M := by
    have hlt : x - 1 < x := Nat.sub_lt hxpos zero_lt_one
    exact not_lt.mp (Nat.find_min hex hlt)
  refine ⟨x, hxpos, hprev, hxspec, ?_⟩
  have hle := div_recipSum_succ_le A (x - 1)
  rw [Nat.sub_add_cancel hxpos] at hle
  linarith

/-! ### The forcing inequality from the negation of the theorem -/

/-- If `dA A n ≤ C * recipSum A x ^ k` for all `n < x`, then every finite
`F ⊆ A ∖ {0}` forces `F.card ≤ C * recipSum A (∏F + 1) ^ k`. -/
private theorem div_counter_bound (A : Set ℕ) {k : ℕ} {C : ℝ}
    (h : ∀ x n : ℕ, n < x → (dA A n : ℝ) ≤ C * recipSum A x ^ k)
    {F : Finset ℕ} (hFA : ∀ a ∈ F, a ∈ A) (h0 : 0 ∉ F) :
    (F.card : ℝ) ≤ C * recipSum A (∏ a ∈ F, a + 1) ^ k := by
  have hle := h (∏ a ∈ F, a + 1) (∏ a ∈ F, a) (Nat.lt_succ_self _)
  exact (Nat.cast_le.mpr (div_dA_prod_ge A hFA h0)).trans hle

/-- Same with `lcm F` (a smaller witness than `∏ F`). -/
private theorem div_counter_bound_lcm (A : Set ℕ) {k : ℕ} {C : ℝ}
    (h : ∀ x n : ℕ, n < x → (dA A n : ℝ) ≤ C * recipSum A x ^ k)
    {F : Finset ℕ} (hFA : ∀ a ∈ F, a ∈ A) (h0 : 0 ∉ F) :
    (F.card : ℝ) ≤ C * recipSum A (F.lcm id + 1) ^ k := by
  have hle := h (F.lcm id + 1) (F.lcm id) (Nat.lt_succ_self _)
  exact (Nat.cast_le.mpr (div_dA_lcm_ge A hFA h0)).trans hle

/-! ### The main theorem -/

/-- **ErSa80, divergent case.** For infinite `A ⊆ ℕ` with unbounded
reciprocal sum, `max_{n<x} dA A n / recipSum A x ^ k` is unbounded for
every `k`.

Proved here for `C ≤ 0` (any `k`) and `k = 0` (any `C`) directly; the
remaining case `k ≥ 1`, `C > 0` is the Erdős–Sárközy core, dispatched to
`divisor_limsup_caseA` / `divisor_limsup_caseB` (see the file header). -/
theorem divisor_set_limsup_divergent (A : Set ℕ) (hA : A.Infinite)
    (hU : ∀ M : ℝ, ∃ x : ℕ, M < recipSum A x) (k : ℕ) (C : ℝ) :
    ∃ x : ℕ, ∃ n : ℕ, n < x ∧ C * recipSum A x ^ k < (dA A n : ℝ) := by
  rcases le_or_gt C 0 with hC | hC
  · -- `C ≤ 0`: the left side is nonpositive; `dA A a ≥ 1` for nonzero `a ∈ A`.
    obtain ⟨a, ha⟩ := (hA.sdiff (Set.finite_singleton 0)).nonempty
    refine ⟨a + 1, a, Nat.lt_succ_self a, ?_⟩
    have hpos : (0 : ℝ) < (dA A a : ℝ) := by
      have hmem : a ∈ a.divisors.filter (· ∈ A) :=
        Finset.mem_filter.mpr ⟨Nat.mem_divisors_self a ha.2, ha.1⟩
      exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨a, hmem⟩)
    exact lt_of_le_of_lt
      (mul_nonpos_of_nonpos_of_nonneg hC (pow_nonneg (div_recipSum_nonneg A _) k))
      hpos
  · rcases k with _ | k'
    · -- `k = 0`: need `C < dA A n`; products of `m > C` elements of `A ∖ {0}`.
      obtain ⟨m, hm⟩ := exists_nat_gt C
      have hminf : (A \ {0}).Infinite := hA.sdiff (Set.finite_singleton 0)
      obtain ⟨F, hFsub, hFcard⟩ := hminf.exists_subset_card_eq m
      refine ⟨∏ b ∈ F, b + 1, ∏ b ∈ F, b, Nat.lt_succ_self _, ?_⟩
      rw [pow_zero, mul_one]
      have hcard : m ≤ dA A (∏ b ∈ F, b) := by
        rw [← hFcard]
        apply div_dA_prod_ge A
        · exact fun b hb => (hFsub hb).1
        · exact fun hb => (hFsub hb).2 rfl
      exact lt_of_lt_of_le hm (Nat.cast_le.mpr hcard)
    · -- `k ≥ 1`, `C > 0`: split on whether `recipSum` stays below
      -- `exp(√(log log u))` eventually (Case A, `JSP361/CaseA.lean`) or
      -- exceeds it at arbitrarily large scales (Case B, `JSP361/CaseB.lean`).
      by_cases hB : ∀ U : ℕ, ∃ u : ℕ, U ≤ u ∧
          Real.exp (Real.sqrt (Real.log (Real.log (u : ℝ)))) < recipSum A u
      · exact divisor_limsup_caseB A hA hU hB (k' + 1) C hC
      · push_neg at hB
        obtain ⟨U, hUbd⟩ := hB
        exact divisor_limsup_caseA A hA hU
          ⟨U, fun u hu => hUbd u hu⟩ (Nat.succ_pos k') hC

end JSP361