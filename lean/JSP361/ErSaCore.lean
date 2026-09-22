import JSP361.Defs
import JSP361.Counting
import JSP361.CountA
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

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
-/

namespace JSP361

open Finset
open scoped Classical

/-- **ErSa80 Part II core.**  At a scale `x` with
`f(x) = recipSum A x > exp(√(log log x))`, some `n ≤ exp(8 (log x)²)` has
`dA A n > exp((e/32)·(log f(x))²)`.  (Constants flexible: any `c > 0` and
`J` in place of `e/32` and `8` may be substituted; report what is used.) -/
theorem ersa_core (A : Set ℕ) (hA : A.Infinite) {x : ℕ}
    (hx : (16 : ℝ) ≤ Real.log (Real.log (x : ℝ)))
    (hf : Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ)))) < recipSum A x) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (8 * (Real.log (x : ℝ)) ^ 2) ∧
      Real.exp ((Real.exp 1 / 32) * (Real.log (recipSum A x)) ^ 2)
        < (dA A n : ℝ) := by
  sorry

end JSP361
