import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Mertens-type bounds for sums over primes

Main result (`JSP361.sum_prime_recip_le_loglog`): for `16 ≤ x`,

  `∑ p ∈ Nat.primesBelow x, (1 : ℝ) / p ≤ 4 * Real.log (Real.log x) + 20`.

Proof route (fully elementary, no integration):
* Split the primes below `x` into dyadic blocks `2^j ≤ p < 2^(j+1)`, indexed by
  `j = Nat.log 2 p ∈ Icc 1 (Nat.log 2 x)` (Finset fiberwise sum).
* On block `j`, `1 / p ≤ (1/2)^j`, and the block cardinality `N_j` satisfies
  `N_j * (j * log 2) ≤ ∑_{p ∈ block} log p ≤ θ(2^{j+1}) ≤ log 4 * 2^{j+1}`
  (Chebyshev's bound `Chebyshev.theta_le_log4_mul_x`), hence
  `N_j * (1/2)^j ≤ 4 / j`.
* `∑_{j=1}^{J} 4 / j ≤ 4 * (1 + log J)` is `harmonic_le_one_add_log`.
* `J = Nat.log 2 x ≤ log x / log 2`, so `log J ≤ log log x - log log 2 ≤ log log x + 1`
  (using `0.6931 < log 2 < 0.6932`).

Total: `∑ 1/p ≤ 4 * log log x + 8 ≤ 4 * log log x + 20`.
-/

namespace JSP361

open Finset

/-- For a prime `p`, `1 / p ≤ (1/2) ^ Nat.log 2 p` since `2 ^ Nat.log 2 p ≤ p`. -/
private lemma one_div_prime_le (p : ℕ) (hp : p.Prime) :
    (1 : ℝ) / p ≤ (1 / 2) ^ Nat.log 2 p := by
  have h1 : (2 : ℝ) ^ Nat.log 2 p ≤ p := by
    exact_mod_cast Nat.pow_log_le_self 2 hp.ne_zero
  have h2 : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 p := by positivity
  rw [div_pow, one_pow]
  exact one_div_le_one_div_of_le h2 h1

/-- Cardinal bound for the dyadic block `Nat.log 2 p = j`, in the form
`N_j * (1/2)^j ≤ 4 / j`, which is what the block decomposition consumes. -/
private lemma card_fiber_mul_le (x j : ℕ) (hj : 1 ≤ j) :
    ((Nat.primesBelow x).filter fun p ↦ Nat.log 2 p = j).card * ((1 : ℝ) / 2) ^ j
      ≤ 4 / j := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  -- (1) `N_j * (j * log 2) ≤ ∑_{p ∈ fiber} log p`, since `2^j ≤ p` on the fiber.
  have h1 : ((Nat.primesBelow x).filter fun p ↦ Nat.log 2 p = j).card * (j * Real.log 2)
      ≤ ∑ p ∈ (Nat.primesBelow x).filter fun p ↦ Nat.log 2 p = j, Real.log p := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpmem, hpm⟩ := Finset.mem_filter.1 hp
    have h2p : (2 : ℝ) ^ j ≤ p := by
      have h := Nat.pow_log_le_self 2 (Nat.prime_of_mem_primesBelow hpmem).ne_zero
      rw [hpm] at h
      exact_mod_cast h
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ j) h2p
    rwa [Real.log_pow] at hlog
  -- (2) `∑_{p ∈ fiber} log p ≤ θ (2^{j+1}) ≤ log 4 * 2^{j+1}`.
  have h2 : ∑ p ∈ (Nat.primesBelow x).filter fun p ↦ Nat.log 2 p = j, Real.log p
      ≤ ∑ p ∈ Nat.primesLE (2 ^ (j + 1)), Real.log p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Nat.mem_primesLE]
      obtain ⟨hpmem, hpm⟩ := Finset.mem_filter.1 hp
      have hlt : p < 2 ^ (j + 1) := by
        have h := Nat.lt_pow_succ_log_self Nat.one_lt_two p
        simpa [hpm] using h
      exact ⟨hlt.le, Nat.prime_of_mem_primesBelow hpmem⟩
    · intro i _ _
      exact Real.log_natCast_nonneg i
  have h3 : ∑ p ∈ Nat.primesLE (2 ^ (j + 1)), Real.log p
      ≤ Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ) := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  -- (3) cancel `log 2`: `N_j * j ≤ 2^{j+2}`.
  have h4 : ((Nat.primesBelow x).filter fun p ↦ Nat.log 2 p = j).card * j
      ≤ (4 : ℝ) * 2 ^ j := by
    have h := h1.trans (h2.trans h3)
    push_cast at h
    rw [hlog4] at h
    have hR : (2 : ℝ) * Real.log 2 * 2 ^ (j + 1) = (4 * 2 ^ j) * Real.log 2 := by
      rw [pow_add]
      ring
    have hL : ((Nat.primesBelow x).filter fun p ↦ Nat.log 2 p = j).card
        * (j * Real.log 2)
        = (((Nat.primesBelow x).filter fun p ↦ Nat.log 2 p = j).card * j)
          * Real.log 2 := by ring
    rw [hL, hR] at h
    exact le_of_mul_le_mul_right h hlog2pos
  -- (4) divide: `N_j * (1/2)^j ≤ 4 / j`.
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  refine (le_div_iff₀ hjpos).mpr ?_
  rw [div_pow, one_pow, mul_one_div, div_mul_eq_mul_div, div_le_iff₀ h2jpos]
  linarith [h4]

/-- Sum of `1/p` over one dyadic block. -/
private lemma sum_fiber_le (x j : ℕ) (hj : 1 ≤ j) :
    ∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ Nat.log 2 p = j), (1 : ℝ) / p
      ≤ 4 / j := by
  calc ∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ Nat.log 2 p = j), (1 : ℝ) / p
      ≤ ∑ p ∈ (Nat.primesBelow x).filter (fun p ↦ Nat.log 2 p = j), ((1 : ℝ) / 2) ^ j := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpmem, hpm⟩ := Finset.mem_filter.1 hp
        have h := one_div_prime_le p (Nat.prime_of_mem_primesBelow hpmem)
        rwa [hpm] at h
    _ = ((Nat.primesBelow x).filter (fun p ↦ Nat.log 2 p = j)).card
          * ((1 : ℝ) / 2) ^ j := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 / j := card_fiber_mul_le x j hj

/-- `log (Nat.log 2 x) ≤ log (log x) + 1` for `16 ≤ x`. -/
private lemma log_natLog_le (x : ℕ) (hx : 16 ≤ x) :
    Real.log (Nat.log 2 x) ≤ Real.log (Real.log x) + 1 := by
  have hx0 : x ≠ 0 := by omega
  have hJ4 : 4 ≤ Nat.log 2 x :=
    (Nat.le_log_iff_pow_le Nat.one_lt_two hx0).mpr (by omega)
  have hJpos : (0 : ℝ) < (Nat.log 2 x : ℕ) := by exact_mod_cast (by omega : 0 < Nat.log 2 x)
  have h2J : (2 : ℝ) ^ Nat.log 2 x ≤ x := by
    exact_mod_cast Nat.pow_log_le_self 2 hx0
  have hJle : (Nat.log 2 x : ℝ) * Real.log 2 ≤ Real.log x := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 x) h2J
    rwa [Real.log_pow] at h
  have hlogxpos : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hJle2 : (Nat.log 2 x : ℝ) ≤ Real.log x / Real.log 2 :=
    (le_div_iff₀ (Real.log_pos one_lt_two)).mpr hJle
  have h2half : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hloglog2 : -1 ≤ Real.log (Real.log 2) := by
    have h1 : Real.log ((1 : ℝ) / 2) ≤ Real.log (Real.log 2) :=
      Real.log_le_log (by norm_num) h2half
    have h2 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  calc Real.log (Nat.log 2 x)
      ≤ Real.log (Real.log x / Real.log 2) := Real.log_le_log hJpos hJle2
    _ = Real.log (Real.log x) - Real.log (Real.log 2) :=
        Real.log_div (ne_of_gt hlogxpos) (ne_of_gt (Real.log_pos one_lt_two))
    _ ≤ Real.log (Real.log x) + 1 := by linarith

/-- **Mertens bound on the sum of prime reciprocals** (dyadic-block version):
for `16 ≤ x`, `∑_{p < x} 1/p ≤ 4 * log log x + 20`. -/
theorem sum_prime_recip_le_loglog (x : ℕ) (hx : 16 ≤ x) :
    ∑ p ∈ Nat.primesBelow x, (1 : ℝ) / p ≤ 4 * Real.log (Real.log x) + 20 := by
  have hmaps : ∀ p ∈ Nat.primesBelow x, Nat.log 2 p ∈ Finset.Icc 1 (Nat.log 2 x) := by
    intro p hp
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.log_mono_right (Nat.lt_of_mem_primesBelow hp).le⟩
    have hpp := Nat.prime_of_mem_primesBelow hp
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hpp.ne_zero]
    simpa using hpp.two_le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p ↦ (1 : ℝ) / p)]
  refine (Finset.sum_le_sum fun j hj ↦
    sum_fiber_le x j (Finset.mem_Icc.1 hj).1).trans ?_
  calc ∑ j ∈ Finset.Icc 1 (Nat.log 2 x), (4 : ℝ) / j
      = 4 * ∑ j ∈ Finset.Icc 1 (Nat.log 2 x), (j : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [div_eq_mul_inv]
    _ ≤ 4 * (1 + Real.log (Nat.log 2 x)) := by
        gcongr
        have h := harmonic_le_one_add_log (Nat.log 2 x)
        rw [harmonic_eq_sum_Icc] at h
        push_cast at h
        exact h
    _ ≤ 4 * Real.log (Real.log x) + 20 := by
        have hlog := log_natLog_le x hx
        linarith

end JSP361
