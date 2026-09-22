import JSP361.Basic
import JSP361.CountA
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# JSP-000361 — the Erdős–Sárközy "rough LCM" prime-power product

`Lprod x y = ∏_{p prime, p ≤ y} p^{⌊log_p x⌋}` is the `X` of
Erdős–Sárközy (ErSa80), Part I, Theorem 3: every `a ∈ A` with largest
prime factor `P(a) ≤ x/t` divides `X`, giving
`d_A(X) ≥ N_A(x) − #{a ≤ x : ∃ prime factor > x/t}`,
while `log X ≤ π(x/t)·log x`.

Main results:

* `Lprod_pos` — `Lprod x y > 0`.
* `dvd_Lprod` — every `a ≤ x` all of whose prime factors are `≤ y`
  divides `Lprod x y`.
* `Lprod_le` — `Lprod x y ≤ x^{π(y)}` for `x ≠ 0`
  (note `Lprod 0 y = 1`, so the bound genuinely needs `x ≠ 0`).
* `dA_Lprod_ge` — `d_A(Lprod x y)` counts at least the `A`-elements
  `≤ x` with all prime factors `≤ y`.
* `log_Lprod_le` — `log (Lprod x y) ≤ π(y) · log x`.
-/

namespace JSP361

open Finset
open scoped Classical

/-- The Erdős–Sárközy prime-power product:
`Lprod x y = ∏_{p prime, p ≤ y} p^{⌊log_p x⌋}`. -/
def Lprod (x y : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesBelow (y + 1), p ^ (Nat.log p x)

theorem Lprod_pos (x y : ℕ) : 0 < Lprod x y := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primesBelow hp).pos _

/-- Key divisibility: `a ≤ x` with all prime factors `≤ y` divides `Lprod x y`.
Proof: `a = ∏_{p ∈ a.primeFactors} p^{a.factorization p}` and
`p^{a.factorization p} ∣ a`, so `p^{a.factorization p} ≤ a ≤ x`, which gives
`a.factorization p ≤ Nat.log p x`; hence `p^{a.factorization p} ∣ p^{Nat.log p x}`
and the latter is a factor of `Lprod x y` since `p ≤ y` is prime. -/
theorem dvd_Lprod {a x y : ℕ} (ha : a ≤ x) (ha0 : a ≠ 0)
    (hp : ∀ p ∈ a.primeFactors, p ≤ y) : a ∣ Lprod x y := by
  have hx0 : x ≠ 0 := fun h => ha0 (le_antisymm (h ▸ ha) (Nat.zero_le a))
  rw [Nat.prod_primeFactors_pow_factorization ha0]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hpm
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
  have hle : a.factorization p ≤ Nat.log p x := by
    rw [Nat.le_log_iff_pow_le hpp.one_lt hx0]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) (Nat.ordProj_dvd a p)).trans ha
  exact (pow_dvd_pow p hle).trans
    (Finset.dvd_prod_of_mem _
      (Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_iff.mpr (hp p hpm), hpp⟩))

/-- Each factor `p^{Nat.log p x} ≤ x` (for `x ≠ 0`), so the product is at
most `x` raised to the number of primes `≤ y`.  (For `x = 0` one has
`Lprod 0 y = 1` while `0 ^ card = 0` once a prime `≤ y` exists, so the
hypothesis `x ≠ 0` is necessary.) -/
theorem Lprod_le (x y : ℕ) (hx : x ≠ 0) :
    Lprod x y ≤ x ^ (Nat.primesBelow (y + 1)).card := by
  apply Finset.prod_le_pow_card
  intro p _
  exact Nat.pow_log_le_self p hx

/-- `d_A(Lprod x y)` counts at least the `A`-elements `≤ x` with all prime
factors `≤ y`. -/
theorem dA_Lprod_ge (A : Set ℕ) (x y : ℕ) :
    ((Finset.range (x + 1)).filter (fun a ↦ a ≠ 0 ∧ a ∈ A ∧
      ∀ p ∈ a.primeFactors, p ≤ y)).card ≤ dA A (Lprod x y) := by
  refine card_le_dA A ?_ (Lprod_pos x y).ne'
  intro a ha
  rw [Finset.mem_filter] at ha
  obtain ⟨hax, ha0, haA, hp⟩ := ha
  exact ⟨haA, dvd_Lprod (Nat.lt_succ_iff.mp (Finset.mem_range.mp hax)) ha0 hp⟩

/-- `log (Lprod x y) = ∑_{p prime ≤ y} (Nat.log p x) · log p`, and each
summand is `log (p^{Nat.log p x}) ≤ log x` (for `x = 0` every summand is
`0` since `Nat.log p 0 = 0`). -/
theorem log_Lprod_le (x y : ℕ) :
    Real.log (Lprod x y) ≤
      (Nat.primesBelow (y + 1)).card * Real.log x := by
  have hlog : Real.log (Lprod x y)
      = ∑ p ∈ Nat.primesBelow (y + 1), (Nat.log p x : ℝ) * Real.log p := by
    have h1 : ((Lprod x y : ℕ) : ℝ)
        = ∏ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ Nat.log p x := by
      unfold Lprod
      norm_cast
    rw [h1, Real.log_prod (fun p hp ↦ (pow_pos
      (Nat.cast_pos.mpr (Nat.prime_of_mem_primesBelow hp).pos) _).ne')]
    exact Finset.sum_congr rfl fun p _ ↦ Real.log_pow _ _
  rw [hlog]
  calc ∑ p ∈ Nat.primesBelow (y + 1), (Nat.log p x : ℝ) * Real.log p
      ≤ ∑ _p ∈ Nat.primesBelow (y + 1), Real.log x := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hx : x = 0
        · subst hx
          have hlg : Nat.log p 0 = 0 :=
            Nat.log_eq_zero_iff.mpr (Or.inl (Nat.prime_of_mem_primesBelow hp).pos)
          simp [hlg]
        · have hpow : (p : ℝ) ^ Nat.log p x ≤ x := by
            exact_mod_cast Nat.pow_log_le_self p hx
          calc (Nat.log p x : ℝ) * Real.log p
              = Real.log ((p : ℝ) ^ Nat.log p x) := (Real.log_pow _ _).symm
            _ ≤ Real.log x := Real.log_le_log
                  (pow_pos (Nat.cast_pos.mpr
                    (Nat.prime_of_mem_primesBelow hp).pos) _) hpow
    _ = (Nat.primesBelow (y + 1)).card * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

end JSP361
