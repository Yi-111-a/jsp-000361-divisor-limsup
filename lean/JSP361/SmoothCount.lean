import Mathlib

/-!
# Count of `t`-smooth numbers — the squarefree-kernel (Rankin `σ = 1/2`) bound

We prove the elementary bound

    `Ψ(N, t) := #{0 < n < N : every prime factor of `n` is `< t`}
      ≤ √N · exp (2.5 · √t)`

which is the `σ = 1/2` instance of Rankin's method
`Ψ(N, t) ≤ N^σ · exp(O(t^{1-σ}))`, an input for the Erdős–Sárközy problem
JSP-000361.

**Proof.** Every nonzero `n` decomposes (uniquely) as `n = s · m²` with `s`
squarefree (the "squarefree kernel"): take `s` to be the product of the primes
dividing `n` to an *odd* power and `m = ∏ p^{⌊e_p/2⌋}` where `e_p` is the
exponent of `p` in `n` (`sqfreeKernel_mul_sq`).  If `n` is `t`-smooth then the
kernel set `T = {p : p ∣ n to an odd power}` satisfies `T ⊆ primesBelow t`, so
`n ↦ (T, m)` injects the `t`-smooth numbers below `N` into the pairs `(T, m)`
with `T ⊆ primesBelow t` and `(∏ T)·m² < N`.  For each `T` there are at most
`√(N/∏T) = √N·(∏T)^{-1/2}` admissible `m` (`card_fiber_le`), giving

    `Ψ(N,t) ≤ √N · ∑_{T ⊆ primesBelow t} (∏ T)^{-1/2}
            = √N · ∏_{p < t} (1 + p^{-1/2})`   (`Finset.prod_one_add`)
            `≤ √N · exp(∑_{p<t} p^{-1/2})`     (`Real.prod_one_add_le_exp_sum`).

Finally `∑_{p<t} p^{-1/2} ≤ ∑_{m<t} m^{-1/2} ≤ 2√t` by telescoping:
`m^{-1/2} ≤ 2(√m - √(m-1))` since
`2(√m - √(m-1)) = 2/(√m + √(m-1)) ≥ 1/√m` (`sum_range_inv_sqrt_le`).  The
constant `2.5` in the exponent has slack: the proof actually gives `2`.
-/

namespace JSP361

open Finset

/-- **Squarefree-kernel decomposition.**  Every nonzero `n` factors as
`n = s · m²` where `s` is the product of the prime factors of `n` occurring to
an odd power and `m = ∏_{p ∣ n} p^{⌊e_p/2⌋}`.  The product defining `s` is a
product of distinct primes, hence squarefree, so `s` is the squarefree kernel
of `n`. -/
theorem sqfreeKernel_mul_sq {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors.filter (fun p ↦ Odd (n.factorization p)), p) *
      (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) ^ 2 = n := by
  have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    Nat.prod_factorization_pow_eq_self hn
  have hf : (∏ p ∈ n.primeFactors.filter (fun p ↦ Odd (n.factorization p)), p)
      = ∏ p ∈ n.primeFactors, p ^ (n.factorization p % 2) := by
    have hsplit := Finset.prod_filter_mul_prod_filter_not n.primeFactors
      (fun p ↦ Odd (n.factorization p)) (fun p ↦ p ^ (n.factorization p % 2))
    have hA : (∏ p ∈ n.primeFactors.filter (fun p ↦ Odd (n.factorization p)),
        p ^ (n.factorization p % 2))
        = ∏ p ∈ n.primeFactors.filter (fun p ↦ Odd (n.factorization p)), p := by
      refine Finset.prod_congr rfl fun p hp ↦ ?_
      rw [Nat.odd_iff.mp (Finset.mem_filter.mp hp).2, pow_one]
    have hB : (∏ p ∈ n.primeFactors.filter (fun p ↦ ¬ Odd (n.factorization p)),
        p ^ (n.factorization p % 2)) = 1 := by
      refine Finset.prod_eq_one fun p hp ↦ ?_
      have h2 := (Finset.mem_filter.mp hp).2
      rcases Nat.mod_two_eq_zero_or_one (n.factorization p) with h | h
      · rw [h, pow_zero]
      · exact absurd (Nat.odd_iff.mpr h) h2
    rw [← hsplit, hA, hB, mul_one]
  calc (∏ p ∈ n.primeFactors.filter (fun p ↦ Odd (n.factorization p)), p) *
        (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) ^ 2
      = (∏ p ∈ n.primeFactors, p ^ (n.factorization p % 2)) *
          ∏ p ∈ n.primeFactors, (p ^ (n.factorization p / 2)) ^ 2 := by
        rw [hf, ← Finset.prod_pow]
    _ = ∏ p ∈ n.primeFactors,
          (p ^ (n.factorization p % 2) * (p ^ (n.factorization p / 2)) ^ 2) :=
        Finset.prod_mul_distrib.symm
    _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
        refine Finset.prod_congr rfl fun p _ ↦ ?_
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
    _ = n := hself

/-- For `x ≥ 1`, `1/√x ≤ 2(√x - √(x-1))`: equivalently
`1 ≤ 2√x(√x - √(x-1)) = 2x - 2√(x(x-1))`, and `√(x(x-1)) ≤ x - 1/2` since
`x(x-1) ≤ (x - 1/2)²`. -/
theorem one_div_sqrt_le_two_sqrt_sub {x : ℝ} (hx : 1 ≤ x) :
    1 / Real.sqrt x ≤ 2 * (Real.sqrt x - Real.sqrt (x - 1)) := by
  have hb : (0:ℝ) ≤ x - 1 := by linarith
  have hsa : (0:ℝ) < Real.sqrt x := Real.sqrt_pos_of_pos (by linarith)
  have hsqrtba : Real.sqrt (x - 1) * Real.sqrt x ≤ x - 1 / 2 := by
    have h1 : Real.sqrt (x - 1) * Real.sqrt x = Real.sqrt ((x - 1) * x) :=
      (Real.sqrt_mul hb x).symm
    rw [h1]
    have h2 : (x - 1) * x ≤ (x - 1 / 2) ^ 2 := by nlinarith
    calc Real.sqrt ((x - 1) * x) ≤ Real.sqrt ((x - 1 / 2) ^ 2) :=
        Real.sqrt_le_sqrt h2
      _ = x - 1 / 2 := Real.sqrt_sq (by linarith)
  rw [div_le_iff₀ hsa]
  have hexp : 2 * (Real.sqrt x - Real.sqrt (x - 1)) * Real.sqrt x
      = 2 * x - 2 * (Real.sqrt (x - 1) * Real.sqrt x) := by
    have h := Real.mul_self_sqrt (show (0:ℝ) ≤ x by linarith)
    linear_combination 2 * h
  rw [hexp]
  linarith [hsqrtba]

/-- Telescoping bound: `∑_{m < t} m^{-1/2} ≤ 2√t`.  The `m = 0` term vanishes
(`1/√0 = 0`), and for `m = i + 1`,
`(i+1)^{-1/2} ≤ 2(√(i+1) - √i)`, whose sum telescopes to `2√(t-1) ≤ 2√t`. -/
theorem sum_range_inv_sqrt_le (t : ℕ) :
    ∑ m ∈ Finset.range t, (1:ℝ) / Real.sqrt m ≤ 2 * Real.sqrt t := by
  rcases t with _ | k
  · simp
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, Real.sqrt_zero, div_zero, add_zero]
    calc ∑ i ∈ Finset.range k, (1:ℝ) / Real.sqrt ((i + 1 : ℕ))
        ≤ ∑ i ∈ Finset.range k,
            2 * (Real.sqrt ((i + 1 : ℕ)) - Real.sqrt (i : ℕ)) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hx : (1:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
            have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
            push_cast
            linarith
          have h := one_div_sqrt_le_two_sqrt_sub hx
          have heq : ((i + 1 : ℕ) : ℝ) - 1 = (i : ℝ) := by push_cast; ring
          rwa [heq] at h
      _ = 2 * (Real.sqrt (k : ℕ) - Real.sqrt (0 : ℕ)) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub (fun i ↦ Real.sqrt (i : ℕ)) k]
      _ = 2 * Real.sqrt (k : ℕ) := by
          rw [Nat.cast_zero, Real.sqrt_zero, sub_zero]
      _ ≤ 2 * Real.sqrt ((k + 1 : ℕ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 2)
          exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)

/-- For `s ≥ 1`, the number of positive `m < N` with `s·m² < N` is at most
`√(N/s) = √N/√s`: each such `m` satisfies `1 ≤ m ≤ ⌊√(N/s)⌋`. -/
theorem card_fiber_le (N s : ℕ) (hs : 1 ≤ s) :
    (((Finset.range N).filter (fun m ↦ m ≠ 0 ∧ s * m ^ 2 < N)).card : ℝ)
      ≤ Real.sqrt N / Real.sqrt s := by
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hsub : (Finset.range N).filter (fun m ↦ m ≠ 0 ∧ s * m ^ 2 < N)
      ⊆ Finset.Icc 1 ⌊Real.sqrt ((N:ℝ) / (s:ℝ))⌋₊ := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨_, hm0, hlt⟩ := hm
    rw [Finset.mem_Icc]
    refine ⟨Nat.pos_of_ne_zero hm0, Nat.le_floor ?_⟩
    have hlt' : (s:ℝ) * (m:ℝ) ^ 2 < (N:ℝ) := by exact_mod_cast hlt
    have h1 : (m:ℝ) ^ 2 < (N:ℝ) / (s:ℝ) := by
      rw [lt_div_iff₀ hsR]
      nlinarith [hlt']
    exact ((Real.lt_sqrt (Nat.cast_nonneg m)).mpr h1).le
  calc (((Finset.range N).filter (fun m ↦ m ≠ 0 ∧ s * m ^ 2 < N)).card : ℝ)
      ≤ ((Finset.Icc 1 ⌊Real.sqrt ((N:ℝ) / (s:ℝ))⌋₊).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (⌊Real.sqrt ((N:ℝ) / (s:ℝ))⌋₊ : ℝ) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ Real.sqrt ((N:ℝ) / (s:ℝ)) := Nat.floor_le (Real.sqrt_nonneg _)
    _ = Real.sqrt N / Real.sqrt s := Real.sqrt_div (Nat.cast_nonneg N) _

/-- `(∏ T)^{-1/2} = ∏_{p ∈ T} p^{-1/2}` for a finset `T` of naturals. -/
theorem one_div_sqrt_nat_prod (T : Finset ℕ) :
    (1:ℝ) / Real.sqrt ((∏ p ∈ T, p : ℕ)) = ∏ p ∈ T, (1:ℝ) / Real.sqrt p := by
  have hsqrt : Real.sqrt ((∏ p ∈ T, p : ℕ)) = ∏ p ∈ T, Real.sqrt (p : ℝ) := by
    rw [Nat.cast_prod]
    induction T using Finset.induction with
    | empty => simp
    | insert a T ha ih =>
        rw [Finset.prod_insert ha, Real.sqrt_mul (Nat.cast_nonneg a) _, ih,
          Finset.prod_insert ha]
  rw [hsqrt, one_div, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [one_div]

/-- **Smooth-number count** (squarefree-kernel method): the number of
nonzero `n < N` all of whose prime factors are `< t` is at most
`√N · exp(2.5·√t)`. -/
theorem card_smooth_le (N t : ℕ) :
    (((Finset.range N).filter (fun n ↦ n ≠ 0 ∧
        n.primeFactors ⊆ Nat.primesBelow t)).card : ℝ)
      ≤ Real.sqrt N * Real.exp (2.5 * Real.sqrt t) := by
  classical
  set P : Finset ℕ := Nat.primesBelow t with hP
  -- The kernel map `n ↦ (T, m)` with `n = (∏ T)·m²` injects the filtered set
  -- into pairs over `P.powerset`.
  set S : Finset (Finset ℕ × ℕ) := P.powerset.biUnion fun T ↦
    ((Finset.range N).filter (fun m ↦ m ≠ 0 ∧ (∏ p ∈ T, p) * m ^ 2 < N)).image
      (Prod.mk T) with hS
  have hinj :
      ((Finset.range N).filter (fun n ↦ n ≠ 0 ∧
        n.primeFactors ⊆ Nat.primesBelow t)).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn
      (fun n ↦ (n.primeFactors.filter (fun p ↦ Odd (n.factorization p)),
        ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2))) ?_ ?_
    · intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnN, hn0, hsub⟩ := hn
      rw [Finset.mem_range] at hnN
      have hdec := sqfreeKernel_mul_sq hn0
      have hm1 : 1 ≤ ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2) :=
        Finset.one_le_prod fun p hp ↦
          Nat.one_le_pow _ _ (Nat.mem_primeFactors.mp hp).1.pos
      have hs1 : 1 ≤
          ∏ p ∈ n.primeFactors.filter (fun p ↦ Odd (n.factorization p)), p :=
        Finset.one_le_prod fun p hp ↦
          (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.one_le
      have hm_le : ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2) ≤ n := by
        have h1 : ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
            ≤ (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) ^ 2 := by
          calc ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
              = (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) * 1 :=
                (mul_one _).symm
            _ ≤ (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) *
                  (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) :=
                Nat.mul_le_mul_left _ hm1
            _ = (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) ^ 2 :=
                (sq _).symm
        calc ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
            ≤ (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) ^ 2 := h1
          _ = 1 * (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) ^ 2 :=
              (one_mul _).symm
          _ ≤ (∏ p ∈ n.primeFactors.filter (fun p ↦ Odd (n.factorization p)), p) *
                (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) ^ 2 :=
              Nat.mul_le_mul_right _ hs1
          _ = n := hdec
      rw [hS, Finset.mem_biUnion]
      refine ⟨n.primeFactors.filter (fun p ↦ Odd (n.factorization p)), ?_, ?_⟩
      · rw [Finset.mem_powerset]
        exact (Finset.filter_subset _).trans hsub
      · refine Finset.mem_image.mpr
          ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_, rfl⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (lt_of_le_of_lt hm_le hnN),
          Nat.pos_iff_ne_zero.mp hm1, by rw [hdec]; exact hnN⟩
    · intro a ha b hb hab
      have ha0 : a ≠ 0 := (Finset.mem_filter.mp ha).2.1
      have hb0 : b ≠ 0 := (Finset.mem_filter.mp hb).2.1
      obtain ⟨hT, hm⟩ := Prod.mk.injEq.mp hab
      have hda := sqfreeKernel_mul_sq ha0
      have hdb := sqfreeKernel_mul_sq hb0
      rw [← hda, ← hdb, hT, hm]
  -- Cardinality of the cover.
  have hScard : (S.card : ℝ) ≤ ∑ T ∈ P.powerset,
      (((Finset.range N).filter (fun m ↦ m ≠ 0 ∧ (∏ p ∈ T, p) * m ^ 2 < N)).card : ℝ) := by
    have h1 : S.card ≤ ∑ T ∈ P.powerset,
        (((Finset.range N).filter (fun m ↦ m ≠ 0 ∧ (∏ p ∈ T, p) * m ^ 2 < N)).image
          (Prod.mk T)).card := by
      rw [hS]
      exact Finset.card_biUnion_le
    have h2 : ∑ T ∈ P.powerset,
        (((Finset.range N).filter (fun m ↦ m ≠ 0 ∧ (∏ p ∈ T, p) * m ^ 2 < N)).image
          (Prod.mk T)).card
        ≤ ∑ T ∈ P.powerset,
          ((Finset.range N).filter (fun m ↦ m ≠ 0 ∧ (∏ p ∈ T, p) * m ^ 2 < N)).card :=
      Finset.sum_le_sum fun T _ ↦ Finset.card_image_le
    have h3 := h1.trans h2
    exact_mod_cast h3
  -- Per-fiber bound.
  have hfiber : ∀ T ∈ P.powerset,
      (((Finset.range N).filter (fun m ↦ m ≠ 0 ∧ (∏ p ∈ T, p) * m ^ 2 < N)).card : ℝ)
        ≤ Real.sqrt N / Real.sqrt ((∏ p ∈ T, p : ℕ)) := by
    intro T hT
    have hTsub : T ⊆ P := Finset.mem_powerset.mp hT
    have hs1 : 1 ≤ ∏ p ∈ T, p :=
      Finset.one_le_prod fun p hp ↦
        (Nat.prime_of_mem_primesBelow (hTsub hp)).one_le
    exact card_fiber_le N _ hs1
  -- The Euler-factor bound `∑_T (∏T)^{-1/2} = ∏_{p<t}(1 + p^{-1/2}) ≤ exp(∑ p^{-1/2})`.
  have hpow : ∏ p ∈ P, (1 + (1:ℝ) / Real.sqrt p)
      = ∑ T ∈ P.powerset, ∏ p ∈ T, (1:ℝ) / Real.sqrt p :=
    Finset.prod_one_add P
  have hexp : ∏ p ∈ P, (1 + (1:ℝ) / Real.sqrt p)
      ≤ Real.exp (∑ p ∈ P, (1:ℝ) / Real.sqrt p) :=
    Real.prod_one_add_le_exp_sum P fun _ ↦ by positivity
  have hPsub : P ⊆ Finset.range t := fun p hp ↦
    Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp)
  have hsum2 : ∑ p ∈ P, (1:ℝ) / Real.sqrt p ≤ 2 * Real.sqrt t :=
    (Finset.sum_le_sum_of_subset_of_nonneg hPsub fun _ _ _ ↦ by positivity).trans
      (sum_range_inv_sqrt_le t)
  calc (((Finset.range N).filter (fun n ↦ n ≠ 0 ∧
          n.primeFactors ⊆ Nat.primesBelow t)).card : ℝ)
      ≤ (S.card : ℝ) := by exact_mod_cast hinj
    _ ≤ ∑ T ∈ P.powerset,
          (((Finset.range N).filter (fun m ↦ m ≠ 0 ∧ (∏ p ∈ T, p) * m ^ 2 < N)).card : ℝ) :=
        hScard
    _ ≤ ∑ T ∈ P.powerset, Real.sqrt N / Real.sqrt ((∏ p ∈ T, p : ℕ)) :=
        Finset.sum_le_sum fun T hT ↦ hfiber T hT
    _ = Real.sqrt N * ∑ T ∈ P.powerset, (1 / Real.sqrt ((∏ p ∈ T, p : ℕ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ ↦ ?_
        rw [div_eq_mul_inv, ← one_div]
    _ = Real.sqrt N * ∑ T ∈ P.powerset, ∏ p ∈ T, (1:ℝ) / Real.sqrt p := by
        congr 1
        exact Finset.sum_congr rfl fun T hT ↦ one_div_sqrt_nat_prod T
    _ = Real.sqrt N * ∏ p ∈ P, (1 + (1:ℝ) / Real.sqrt p) := by rw [← hpow]
    _ ≤ Real.sqrt N * Real.exp (∑ p ∈ P, (1:ℝ) / Real.sqrt p) :=
        mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt N * Real.exp (2.5 * Real.sqrt t) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        refine Real.exp_le_exp.mpr ?_
        calc ∑ p ∈ P, (1:ℝ) / Real.sqrt p ≤ 2 * Real.sqrt t := hsum2
          _ ≤ 2.5 * Real.sqrt t := by
            have h := Real.sqrt_nonneg (t : ℝ)
            linarith

end JSP361
