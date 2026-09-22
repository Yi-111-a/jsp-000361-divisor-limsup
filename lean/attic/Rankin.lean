import Mathlib

/-!
# The Rankin trick for restricted prime-factor counts

`ω_E(n)` counts the *distinct* prime factors of `n` that lie in a finite set `E`.
We prove the elementary Rankin upper bound

  `∑_{n < N} z^{ω_E(n)} ≤ N · ∏_{p ∈ E} (1 + (z - 1)/p)`   (`z ≥ 1`)

and the resulting tail bound
`#{n < N : r ≤ ω_E(n)} ≤ N · z^{-r} · ∏_{p ∈ E} (1 + (z-1)/p)`,

which is the elementary input behind Norton's lemma in Erdős–Sárközy II.

Proof outline: for each `n` expand `z^{ω_E n} = (1 + (z-1))^{ω_E n}` over the powerset of
`n.primeFactors ∩ E` (subsets correspond to squarefree divisors built from `E`-primes),
interchange the two finite sums, bound `#{n < N : t ⊆ E-prime-factors of n}` by
`#{k < N + 1 : k ≠ 0 ∧ ∏ t ∣ k} = N / ∏ t` (`Nat.card_multiples'`), and re-factor the
resulting powerset sum with `Finset.prod_one_add`.
-/

namespace JSP361

/-- `ω_E n` = number of DISTINCT prime factors of `n` lying in `E`. -/
def omegaE (E : Finset ℕ) (n : ℕ) : ℕ := (n.primeFactors.filter (· ∈ E)).card

/-- Expansion of `z ^ ω_E(n)` over the powerset of the `E`-prime-factors of `n`
(these subsets enumerate the squarefree divisors of `n` built from primes in `E`). -/
theorem rpow_omegaE_eq_sum (E : Finset ℕ) (n : ℕ) (z : ℝ) :
    z ^ (omegaE E n : ℝ) =
      ∑ t ∈ (n.primeFactors.filter (· ∈ E)).powerset, (z - 1) ^ t.card := by
  rw [Real.rpow_natCast]
  unfold omegaE
  calc z ^ (n.primeFactors.filter (· ∈ E)).card
      = ∏ _p ∈ n.primeFactors.filter (· ∈ E), z := (Finset.prod_const).symm
    _ = ∏ _p ∈ n.primeFactors.filter (· ∈ E), (1 + (z - 1)) :=
        Finset.prod_congr rfl fun _ _ ↦ by ring
    _ = ∑ t ∈ (n.primeFactors.filter (· ∈ E)).powerset, ∏ _p ∈ t, (z - 1) :=
        Finset.prod_one_add _
    _ = ∑ t ∈ (n.primeFactors.filter (· ∈ E)).powerset, (z - 1) ^ t.card :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.prod_const

/-- Interchanging the order of summation over `n ∈ F` and subsets `t ⊆ S n` (with `S n ⊆ E`):
the powerset sums collapse to a weighted sum over `E.powerset`. -/
theorem sum_sum_powerset_of_subset (E F : Finset ℕ) (S : ℕ → Finset ℕ)
    (hS : ∀ n, S n ⊆ E) (f : Finset ℕ → ℝ) :
    (∑ n ∈ F, ∑ t ∈ (S n).powerset, f t) =
      ∑ t ∈ E.powerset, ((F.filter (fun n ↦ t ⊆ S n)).card : ℝ) * f t := by
  have hp : ∀ n, (S n).powerset = E.powerset.filter (· ⊆ S n) := by
    intro n
    ext t
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h ↦ ⟨fun x hx ↦ hS n (h hx), h⟩, fun h ↦ h.2⟩
  calc (∑ n ∈ F, ∑ t ∈ (S n).powerset, f t)
      = ∑ n ∈ F, ∑ t ∈ E.powerset.filter (· ⊆ S n), f t :=
        Finset.sum_congr rfl fun n _ ↦ by rw [hp n]
    _ = ∑ n ∈ F, ∑ t ∈ E.powerset, (if t ⊆ S n then f t else 0) :=
        Finset.sum_congr rfl fun n _ ↦
          Finset.sum_filter (fun t ↦ t ⊆ S n) (fun _ ↦ f t)
    _ = ∑ t ∈ E.powerset, ∑ n ∈ F, (if t ⊆ S n then f t else 0) := Finset.sum_comm
    _ = ∑ t ∈ E.powerset, ((F.filter (fun n ↦ t ⊆ S n)).card : ℝ) * f t :=
        Finset.sum_congr rfl fun t _ ↦ by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- For `t ⊆ E`, the number of `n < N` whose `E`-prime-factors cover `t` is at most
`N / ∏ t` (natural division cast to `ℝ`). -/
theorem card_filter_subset_primeFactors_le (E : Finset ℕ) (N : ℕ) (t : Finset ℕ) :
    (((Finset.range N).filter (fun n ↦ t ⊆ n.primeFactors.filter (· ∈ E))).card : ℝ) ≤
      (N : ℝ) / ∏ p ∈ t, (p : ℝ) := by
  rcases Finset.eq_empty_or_nonempty t with rfl | htn
  · simp
  · have hsub :
        (Finset.range N).filter (fun n ↦ t ⊆ n.primeFactors.filter (· ∈ E)) ⊆
          (Finset.range N.succ).filter (fun k ↦ k ≠ 0 ∧ (∏ p ∈ t, p) ∣ k) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnN, htsub⟩ := hn
      rw [Finset.mem_range] at hnN
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
      · intro hn0
        subst hn0
        rw [Nat.primeFactors_zero, Finset.filter_empty] at htsub
        exact htn.ne_empty (Finset.subset_empty.mp htsub)
      · have h' : t ⊆ n.primeFactors := htsub.trans (Finset.filter_subset _)
        exact (Finset.prod_dvd_prod_of_subset _ _ _ h').trans (Nat.prod_primeFactors_dvd n)
    calc (((Finset.range N).filter (fun n ↦ t ⊆ n.primeFactors.filter (· ∈ E))).card : ℝ)
        ≤ (((Finset.range N.succ).filter (fun k ↦ k ≠ 0 ∧ (∏ p ∈ t, p) ∣ k)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = ((N / ∏ p ∈ t, p : ℕ) : ℝ) := by rw [Nat.card_multiples']
      _ ≤ (N : ℝ) / ∏ p ∈ t, (p : ℝ) := by
          have h : ((N / ∏ p ∈ t, p : ℕ) : ℝ) ≤ (N : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ) :=
            Nat.cast_div_le
          rw [Nat.cast_prod] at h
          exact h

/-- Rankin trick: for `z ≥ 1`,
`∑_{n < N} z^{ω_E(n)} ≤ N · ∏_{p ∈ E} (1 + (z-1)/p)` when `E` consists of primes. -/
theorem sum_zpow_omegaE_le (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    {z : ℝ} (hz : 1 ≤ z) (N : ℕ) :
    (∑ n ∈ Finset.range N, z ^ (omegaE E n : ℝ)) ≤
      N * ∏ p ∈ E, (1 + (z - 1) / p) := by
  have hz1 : 0 ≤ z - 1 := sub_nonneg.mpr hz
  calc (∑ n ∈ Finset.range N, z ^ (omegaE E n : ℝ))
      = ∑ n ∈ Finset.range N,
          ∑ t ∈ (n.primeFactors.filter (· ∈ E)).powerset, (z - 1) ^ t.card :=
        Finset.sum_congr rfl fun n _ ↦ rpow_omegaE_eq_sum E n z
    _ = ∑ t ∈ E.powerset,
          (((Finset.range N).filter (fun n ↦ t ⊆ n.primeFactors.filter (· ∈ E))).card : ℝ) *
            (z - 1) ^ t.card :=
        sum_sum_powerset_of_subset E (Finset.range N)
          (fun n ↦ n.primeFactors.filter (· ∈ E))
          (fun n _ hx ↦ (Finset.mem_filter.mp hx).2) _
    _ ≤ ∑ t ∈ E.powerset,
          ((N : ℝ) / ∏ p ∈ t, (p : ℝ)) * (z - 1) ^ t.card := by
        refine Finset.sum_le_sum fun t _ ↦
          mul_le_mul_of_nonneg_right ?_ (pow_nonneg hz1 _)
        exact card_filter_subset_primeFactors_le E N t
    _ = N * ∏ p ∈ E, (1 + (z - 1) / p) := by
        rw [Finset.prod_one_add, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [Finset.prod_div_distrib, Finset.prod_const]
        ring

/-- Tail bound: `#{n < N : r ≤ ω_E(n)} ≤ N · z^{-r} · ∏_{p∈E}(1+(z-1)/p)`. -/
theorem card_omegaE_ge_le (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    {z : ℝ} (hz : 1 ≤ z) (N r : ℕ) :
    (((Finset.range N).filter (fun n ↦ r ≤ omegaE E n)).card : ℝ) ≤
      N * z ^ (-(r : ℝ)) * ∏ p ∈ E, (1 + (z - 1) / p) := by
  have hzpos : 0 < z := one_pos.trans_le hz
  have hzr : 0 < z ^ (r : ℝ) := Real.rpow_pos_of_pos hzpos _
  have hlow : (((Finset.range N).filter (fun n ↦ r ≤ omegaE E n)).card : ℝ) * z ^ (r : ℝ) ≤
      N * ∏ p ∈ E, (1 + (z - 1) / p) := by
    calc (((Finset.range N).filter (fun n ↦ r ≤ omegaE E n)).card : ℝ) * z ^ (r : ℝ)
        = ∑ n ∈ (Finset.range N).filter (fun n ↦ r ≤ omegaE E n), z ^ (r : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ (Finset.range N).filter (fun n ↦ r ≤ omegaE E n),
            z ^ (omegaE E n : ℝ) := by
          refine Finset.sum_le_sum fun n hn ↦ Real.rpow_le_rpow_of_exponent_le hz ?_
          exact_mod_cast (Finset.mem_filter.mp hn).2
      _ ≤ ∑ n ∈ Finset.range N, z ^ (omegaE E n : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _)
            fun n _ _ ↦ Real.rpow_nonneg hzpos.le _
      _ ≤ N * ∏ p ∈ E, (1 + (z - 1) / p) := sum_zpow_omegaE_le E hE hz N
  have hfinal : N * z ^ (-(r : ℝ)) * ∏ p ∈ E, (1 + (z - 1) / p) =
      N * ∏ p ∈ E, (1 + (z - 1) / p) / z ^ (r : ℝ) := by
    rw [Real.rpow_neg hzpos.le, div_eq_mul_inv]
    ring
  rw [hfinal, le_div_iff₀ hzr]
  exact hlow

end JSP361
