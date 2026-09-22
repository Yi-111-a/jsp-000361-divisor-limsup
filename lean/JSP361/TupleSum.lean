import JSP361.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin

/-!
# JSP-000361 — tuple-product pigeonhole for `dA`

Let `B ⊆ A ∩ [1,x)` consist of elements `a` with `Ω_{>Y}(a) ≥ t+1`, and
`u = x^r`.  Every ordered `r`-tuple `f : Fin r → B` and every
`1 ≤ m ≤ u / ∏ f` gives `n = (∏ f)·m ≤ u` with
`Ω_{>Y}(n) ≥ r·(t+1)`.

* The number of pairs is `T = ∑_f ⌊u / P_f⌋ ≥ u·(∑_{a∈B} 1/a)^r / 2`
  (via `⌊u/P⌋ ≥ u/(2P)` and `∑_f 1/∏ f = (∑ 1/a)^r`).
* Each `n` has at most `dA A n ^ r` preimages: a tuple with
  `∏ f ∣ n` is an `r`-tuple of elements of `A` dividing `n`
  (`Anatomy.card_tuples_dvd`).
* Hence some `n ≤ u` has `dA A n ^ r ≥ T / |image|`.
-/

namespace JSP361

open Finset
open scoped Classical

/-- The large-prime `Ω` is monotone under divisibility. -/
private theorem omY_le_of_dvd {Y a n : ℕ} (hd : a ∣ n) (hn : n ≠ 0) :
    ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p), a.factorization p ≤
      ∑ p ∈ n.primeFactors.filter (fun p ↦ Y < p), n.factorization p := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact hn (zero_dvd_iff.mp hd)
  have hsub : a.primeFactors.filter (fun p ↦ Y < p) ⊆
      n.primeFactors.filter (fun p ↦ Y < p) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨(Nat.prime_of_mem_primeFactors hp.1).mem_primeFactors
      ((Nat.dvd_of_mem_primeFactors hp.1).trans hd) hn, hp.2⟩
  calc ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p), a.factorization p
      ≤ ∑ p ∈ n.primeFactors.filter (fun p ↦ Y < p), a.factorization p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ Nat.zero_le _)
    _ ≤ ∑ p ∈ n.primeFactors.filter (fun p ↦ Y < p), n.factorization p :=
        Finset.sum_le_sum fun p _ ↦
          ((Nat.factorization_le_iff_dvd ha hn).mpr hd) p

/-- `Ω_{>Y}` of a product of nonzero naturals dominates the sum of the
individual `Ω_{>Y}`. -/
private theorem omY_prod_le {Y : ℕ} {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {g : ι → ℕ} (hg : ∀ i ∈ s, g i ≠ 0) :
    ∑ i ∈ s, ∑ p ∈ (g i).primeFactors.filter (fun p ↦ Y < p), (g i).factorization p
      ≤ ∑ p ∈ (∏ i ∈ s, g i).primeFactors.filter (fun p ↦ Y < p),
          (∏ i ∈ s, g i).factorization p := by
  have hP : (∏ i ∈ s, g i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hg
  have hsub : ∀ i ∈ s, (g i).primeFactors.filter (fun p ↦ Y < p) ⊆
      (∏ j ∈ s, g j).primeFactors.filter (fun p ↦ Y < p) := by
    intro i hi p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨(Nat.prime_of_mem_primeFactors hp.1).mem_primeFactors
      ((Nat.dvd_of_mem_primeFactors hp.1).trans (Finset.dvd_prod_of_mem g hi)) hP, hp.2⟩
  calc ∑ i ∈ s, ∑ p ∈ (g i).primeFactors.filter (fun p ↦ Y < p), (g i).factorization p
      ≤ ∑ i ∈ s, ∑ p ∈ (∏ j ∈ s, g j).primeFactors.filter (fun p ↦ Y < p),
          (g i).factorization p :=
        Finset.sum_le_sum fun i hi ↦
          Finset.sum_le_sum_of_subset_of_nonneg (hsub i hi) (fun p _ _ ↦ Nat.zero_le _)
    _ = ∑ p ∈ (∏ j ∈ s, g j).primeFactors.filter (fun p ↦ Y < p),
          ∑ i ∈ s, (g i).factorization p := Finset.sum_comm
    _ = ∑ p ∈ (∏ j ∈ s, g j).primeFactors.filter (fun p ↦ Y < p),
          (∏ i ∈ s, g i).factorization p :=
        Finset.sum_congr rfl fun p _ ↦ (Nat.factorization_prod_apply hg).symm

/-- For `1 ≤ P ≤ u`, the number of multiples `⌊u/P⌋` is at least
`u / (2P)` as a real number. -/
private theorem cast_div_ge_div_two {u P : ℕ} (hP : 1 ≤ P) (hPu : P ≤ u) :
    (u : ℝ) / (2 * P) ≤ (u / P : ℕ) := by
  have hP0n : 0 < P := hP
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hlt : (u : ℝ) / P < (u / P : ℕ) + 1 := by
    rw [div_lt_iff₀ hP0]
    have h' : u < P * (u / P + 1) := by
      have h1 := Nat.div_add_mod u P
      have h2 := Nat.mod_lt u hP0n
      have h3 : P * (u / P + 1) = P * (u / P) + P := by ring
      omega
    calc (u : ℝ) < (P : ℝ) * ((u / P : ℕ) + 1) := by exact_mod_cast h'
      _ = ((u / P : ℕ) + 1) * P := by ring
  by_cases h : u < 2 * P
  · have h1 : (1 : ℝ) ≤ (u / P : ℕ) := by
      have h1n : 1 ≤ u / P := (Nat.le_div_iff_mul_le hP0n).mpr (by rwa [one_mul])
      exact_mod_cast h1n
    have h2 : (u : ℝ) / (2 * P) < 1 := by
      rw [div_lt_one (by positivity : (0 : ℝ) < 2 * P)]
      have h' : (u : ℝ) < 2 * P := by exact_mod_cast h
      linarith
    linarith
  · have hge2 : 2 * P ≤ u := not_lt.mp h
    have h2 : 2 ≤ u / P := (Nat.le_div_iff_mul_le hP0n).mpr hge2
    have hcast2 : (2 : ℝ) ≤ (u / P : ℕ) := by exact_mod_cast h2
    have hcast3 : ((u / P : ℕ) : ℝ) ≤ (u : ℝ) / P := Nat.cast_div_le
    have hge : (u : ℝ) / (2 * P) ≤ (u : ℝ) / P - 1 := by
      have heq : (u : ℝ) / (2 * P) = ((u : ℝ) / P) / 2 := by ring
      linarith
    linarith

/-- Multinomial expansion: `∑_{f : Fin r → B} 1 / ∏ f = (∑_{a ∈ B} 1/a)^r`. -/
private theorem sum_inv_prod_piFinset (B : Finset ℕ) (r : ℕ) :
    (∑ f ∈ Fintype.piFinset (fun _ : Fin r ↦ B), (1 : ℝ) / ∏ i, f i)
      = (∑ a ∈ B, (1 : ℝ) / a) ^ r := by
  have key := Finset.prod_univ_sum (fun _ : Fin r ↦ B) (fun (_ : Fin r) (a : ℕ) ↦ (1 : ℝ) / a)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at key
  rw [key]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  rw [one_div, Nat.cast_prod, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ (one_div _).symm

/-- Tuple-product pigeonhole: under a bound `SB` on the number of
`n ≤ u` with `Ω_{>Y}(n) ≥ r·(t+1)`, some such `n` satisfies
`dA A n ^ r ≥ (∑_{a∈B} 1/a)^r · u / (2·SB)`. -/
theorem exists_dA_pow_ge (A : Set ℕ) {B : Finset ℕ} {r t Y x u : ℕ}
    (hr : 1 ≤ r) (hx1 : 1 ≤ x) (hu : u = x ^ r)
    (hBA : ∀ a ∈ B, a ∈ A) (hBlt : ∀ a ∈ B, a < x) (hB1 : ∀ a ∈ B, 1 ≤ a)
    (hOm : ∀ a ∈ B, t + 1 ≤
        ∑ p ∈ a.primeFactors.filter (fun p ↦ Y < p), a.factorization p)
    (hfB : (2 : ℝ) ≤ (∑ a ∈ B, (1 : ℝ) / a) ^ r)
    {SB : ℝ} (hSB : 0 < SB)
    (hS : (((Finset.range (u + 1)).filter (fun n ↦ r * (t + 1) ≤
        ∑ p ∈ n.primeFactors.filter (fun p ↦ Y < p),
          n.factorization p)).card : ℝ) ≤ SB) :
    ∃ n : ℕ, n ≤ u ∧
      (∑ a ∈ B, (1 : ℝ) / a) ^ r * (u : ℝ) / (2 * SB)
        ≤ (dA A n : ℝ) ^ r := by
  classical
  set F : Finset (Fin r → ℕ) := Fintype.piFinset (fun _ : Fin r ↦ B) with hF
  set S : Finset ℕ := (Finset.range (u + 1)).filter (fun n ↦ r * (t + 1) ≤
      ∑ p ∈ n.primeFactors.filter (fun p ↦ Y < p), n.factorization p) with hSd
  -- Every tuple coordinate lies in `B`, so `1 ≤ ∏ f ≤ x^r = u`.
  have hmem : ∀ f ∈ F, ∀ i, f i ∈ B := fun f hf i ↦ Fintype.mem_piFinset.mp hf i
  have hP1 : ∀ f ∈ F, 1 ≤ ∏ i, f i :=
    fun f hf ↦ Finset.one_le_prod fun i _ ↦ hB1 _ (hmem f hf i)
  have hPu : ∀ f ∈ F, ∏ i, f i ≤ u := by
    intro f hf
    have hle : ∏ i : Fin r, f i ≤ ∏ _i : Fin r, x :=
      Finset.prod_le_prod fun i _ ↦ Nat.le_of_lt (hBlt _ (hmem f hf i))
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hu] at hle
  -- Every tuple product has `Ω_{>Y} ≥ r·(t+1)`.
  have hOmP : ∀ f ∈ F, r * (t + 1) ≤
      ∑ p ∈ (∏ i, f i).primeFactors.filter (fun p ↦ Y < p),
        (∏ i, f i).factorization p := by
    intro f hf
    have hbig := omY_prod_le (Y := Y) (s := Finset.univ)
      (g := fun i : Fin r ↦ f i) (fun i _ ↦ Nat.ne_of_gt (hB1 _ (hmem f hf i)))
    refine le_trans ?_ hbig
    have heq : r * (t + 1) = ∑ _i : Fin r, (t + 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [heq]
    exact Finset.sum_le_sum fun i _ ↦ hOm _ (hmem f hf i)
  -- The pair set `(f, m)` with `1 ≤ m ≤ u / ∏ f`.
  set pairs : Finset (Σ _f : Fin r → ℕ, ℕ) :=
    F.sigma (fun f ↦ Finset.Icc 1 (u / ∏ i, f i)) with hpairs
  -- Each pair maps to `n = (∏ f)·m ∈ S`.
  have hmap : ∀ p ∈ pairs, (∏ i, p.1 i) * p.2 ∈ S := by
    rintro ⟨f, m⟩ hp
    rw [hpairs, Finset.mem_sigma] at hp
    obtain ⟨hf, hm⟩ := hp
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hm2⟩ := hm
    show (∏ i, f i) * m ∈ S
    rw [hSd, Finset.mem_filter, Finset.mem_range]
    have hle : (∏ i, f i) * m ≤ u := by
      calc (∏ i, f i) * m ≤ (∏ i, f i) * (u / ∏ i, f i) :=
            Nat.mul_le_mul le_rfl hm2
        _ ≤ u := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
    have hn0 : (∏ i, f i) * m ≠ 0 :=
      mul_ne_zero (Nat.ne_of_gt (hP1 f hf)) (ne_of_gt hm1)
    exact ⟨Nat.lt_succ_of_le hle,
      le_trans (hOmP f hf) (omY_le_of_dvd (dvd_mul_right _ m) hn0)⟩
  -- The pair count as a sum.
  have hcardpairs : pairs.card = ∑ f ∈ F, u / ∏ i, f i := by
    rw [hpairs, Finset.card_sigma]
    refine Finset.sum_congr rfl fun f hf ↦ ?_
    rw [Nat.card_Icc]
    have hge : 1 ≤ u / ∏ i, f i :=
      (Nat.le_div_iff_mul_le (hP1 f hf)).mpr (by simpa using hPu f hf)
    omega
  -- Fiber bound: at most `dA A n ^ r` pairs land on a given `n`.
  have hfib : ∀ n ∈ S,
      ((pairs.filter fun p ↦ (∏ i, p.1 i) * p.2 = n).card : ℝ) ≤ (dA A n : ℝ) ^ r := by
    intro n hn
    rw [hSd, Finset.mem_filter] at hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      have hpos : 1 ≤ r * (t + 1) := Nat.mul_pos hr (Nat.succ_pos t)
      simp only [Nat.primeFactors_zero, Finset.filter_empty, Finset.sum_empty] at hn
      omega
    have h1 : (pairs.filter fun p ↦ (∏ i, p.1 i) * p.2 = n).card ≤
        (F.filter fun f ↦ (∏ i, f i) ∣ n).card := by
      apply Finset.card_le_card_of_injOn (fun p ↦ p.1)
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        rw [Finset.mem_coe, Finset.mem_filter]
        obtain ⟨hp1, hp2⟩ := hp
        rw [hpairs, Finset.mem_sigma] at hp1
        have hp2' : (∏ i, p.1 i) * p.2 = n := hp2
        exact ⟨hp1.1, p.2, hp2'.symm⟩
      · intro p hp q hq hpq
        rw [Finset.mem_coe, Finset.mem_filter] at hp hq
        obtain ⟨hp1, hpe⟩ := hp
        obtain ⟨hq1, hqe⟩ := hq
        rw [hpairs, Finset.mem_sigma] at hp1 hq1
        have hpq' : p.1 = q.1 := hpq
        have h2 : p.2 = q.2 := by
          apply mul_left_cancel₀ (Nat.ne_of_gt (hP1 p.1 hp1.1))
          calc (∏ i, p.1 i) * p.2 = n := hpe
            _ = (∏ i, q.1 i) * q.2 := hqe.symm
            _ = (∏ i, p.1 i) * q.2 := by rw [hpq']
        exact Sigma.ext hpq' (heq_of_eq h2)
    have h2 : (F.filter fun f ↦ (∏ i, f i) ∣ n).card ≤ dA A n ^ r := by
      have hsub : F.filter (fun f ↦ (∏ i, f i) ∣ n) ⊆
          Fintype.piFinset (fun _ : Fin r ↦ n.divisors.filter (· ∈ A)) := by
        intro f hf
        rw [Finset.mem_filter] at hf
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr
            ⟨(Finset.dvd_prod_of_mem (fun j ↦ f j) (Finset.mem_univ i)).trans hf.2, hn0⟩,
            hBA _ (hmem f hf.1 i)⟩
      calc (F.filter fun f ↦ (∏ i, f i) ∣ n).card
          ≤ (Fintype.piFinset (fun _ : Fin r ↦ n.divisors.filter (· ∈ A))).card :=
            Finset.card_le_card hsub
        _ = ∏ _i : Fin r, (n.divisors.filter (· ∈ A)).card := Fintype.card_piFinset _
        _ = ((n.divisors.filter (· ∈ A)).card) ^ r := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ = dA A n ^ r := rfl
    exact_mod_cast (h1.trans h2)
  -- Double counting.
  have hcardfib : pairs.card =
      ∑ n ∈ S, (pairs.filter fun p ↦ (∏ i, p.1 i) * p.2 = n).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hup : (pairs.card : ℝ) ≤ ∑ n ∈ S, (dA A n : ℝ) ^ r := by
    rw [hcardfib, Nat.cast_sum]
    exact Finset.sum_le_sum fun n hn ↦ hfib n hn
  -- Lower bound on the pair count.
  have hlow : (u : ℝ) / 2 * (∑ a ∈ B, (1 : ℝ) / a) ^ r ≤ (pairs.card : ℝ) := by
    rw [hcardpairs, Nat.cast_sum, ← sum_inv_prod_piFinset B r, Finset.mul_sum]
    refine Finset.sum_le_sum fun f hf ↦ ?_
    rw [mul_one_div, div_div]
    exact cast_div_ge_div_two (hP1 f hf) (hPu f hf)
  -- Positivity of the lower bound forces `S` to be nonempty.
  have hu1n : 1 ≤ u := by rw [hu]; exact pow_pos (by omega : 0 < x) r
  have hpos : (0 : ℝ) < (u : ℝ) / 2 * (∑ a ∈ B, (1 : ℝ) / a) ^ r := by
    have huR : (0 : ℝ) < u := by exact_mod_cast hu1n
    exact mul_pos (by positivity) (by linarith)
  have hcardpos : (0 : ℝ) < (pairs.card : ℝ) := hpos.trans_le hlow
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    by_contra hcon
    have hle0 : (S.card : ℝ) ≤ 0 := not_lt.mp hcon
    have hS0 : S = ∅ := by
      rw [← Finset.card_eq_zero]
      exact_mod_cast (le_antisymm hle0 (Nat.cast_nonneg _))
    rw [hS0, Finset.sum_empty] at hup
    linarith
  -- Take the maximizer of `dA A n ^ r` over `S`.
  obtain ⟨n₀, hn₀, hmax⟩ :=
    Finset.exists_max_image S (fun n ↦ (dA A n : ℝ) ^ r) (Finset.card_pos.mp (by
      exact_mod_cast hSpos))
  have hsum : ∑ n ∈ S, (dA A n : ℝ) ^ r ≤ (S.card : ℝ) * (dA A n₀ : ℝ) ^ r := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun n hn ↦ hmax n hn
  have hchain : (u : ℝ) / 2 * (∑ a ∈ B, (1 : ℝ) / a) ^ r
      ≤ (S.card : ℝ) * (dA A n₀ : ℝ) ^ r := (hlow.trans hup).trans hsum
  have hn₀u : n₀ ≤ u := by
    rw [hSd] at hn₀
    obtain ⟨h1, _⟩ := Finset.mem_filter.mp hn₀
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp h1)
  refine ⟨n₀, hn₀u, ?_⟩
  have hdiv : (u : ℝ) / 2 * (∑ a ∈ B, (1 : ℝ) / a) ^ r / (S.card : ℝ)
      ≤ (dA A n₀ : ℝ) ^ r := by
    rw [div_le_iff₀ hSpos]
    linarith [hchain]
  calc (∑ a ∈ B, (1 : ℝ) / a) ^ r * (u : ℝ) / (2 * SB)
      = (u : ℝ) / 2 * (∑ a ∈ B, (1 : ℝ) / a) ^ r / SB := by ring
    _ ≤ (u : ℝ) / 2 * (∑ a ∈ B, (1 : ℝ) / a) ^ r / (S.card : ℝ) :=
        div_le_div_of_nonneg_left (le_of_lt hpos) hSpos hS
    _ ≤ (dA A n₀ : ℝ) ^ r := hdiv

end JSP361
