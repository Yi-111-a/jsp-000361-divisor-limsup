import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Operations
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complement-mass bound ("Lemma 2") for Erdős–Sárközy Part II

For `Ω_{>Y}(a) := ∑_{Y < p < X, p prime} a.factorization p` (the prime factors of
`a` above `Y`, counted with multiplicity), we prove the Rankin-trick estimate

    `∑_{a < X : Ω_{>Y}(a) ≤ t} 1/a
       ≤ z^{-t} · (∏_{p ≤ Y} (1 - 1/p)⁻¹) · (∏_{Y < p < X} (1 - z/p)⁻¹)`

for `0 < z ≤ 1` (`recipSum_le_of_largeOmegaFac_le_z`), and the packaged corollary

    `∑_{a < X : Ω_{>Y}(a) ≤ t} 1/a
       ≤ (∏_{p ≤ Y} (1 - 1/p)⁻¹) · (2e(E' + 1)/t)^t`

for `1 ≤ t ≤ E' + 1`, where `E' = ∑_{Y < p < X} 1/p`
(`recipSum_le_of_largeOmegaFac_le`).

## Proof outline

For `0 < a < X` we have `∏_{p ∈ P} w p ^ (a.factorization p) = z^{Ω_{>Y}(a)} / a`
with `w p = 1/p` for `p ≤ Y` and `w p = z/p` for `Y < p < X` (this is
`P = P₁ ∪ P₂`, the prime factorization split `a = u·v`).  Since `z ≤ 1` and
`Ω_{>Y}(a) ≤ t` we get `z^{Ω_{>Y}(a)} ≥ z^t`, hence `1/a ≤ z^{-t} ∏ w p^{f_p}`.
The map `a ↦ (a.factorization p)_{p ∈ P}` is injective on nonzero `a` (recover `a`
via `Nat.prod_factorization_pow_eq_self`), so the sum over `a` is bounded by the
sum over all bounded exponent tuples, which factors into
`∏_{p} (∑_{e < B} w p ^ e) ≤ ∏_p (1 - w p)⁻¹`.
-/

namespace JSP361

open Finset

/-- `massWeight Y z p = 1/p` for `p ≤ Y` and `z/p` for `p > Y`. -/
noncomputable def massWeight (Y : ℕ) (z : ℝ) (p : ℕ) : ℝ :=
  if p ≤ Y then 1/(p:ℝ) else z/(p:ℝ)

/-- A finite geometric sum is bounded by the full geometric series. -/
theorem sum_range_pow_le_inv_one_sub {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (B : ℕ) :
    ∑ e ∈ Finset.range B, w ^ e ≤ (1 - w)⁻¹ := by
  have hw : (0:ℝ) < 1 - w := sub_pos.mpr hw1
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp only [Finset.range_zero, Finset.sum_empty]
    exact inv_nonneg.mpr hw.le
  rw [geom_sum_eq hw1.ne B, inv_eq_one_div]
  have h2 : (w ^ B - 1) / (w - 1) = (1 - w ^ B) / (1 - w) := by
    rw [show w - 1 = -(1 - w) by ring, show w ^ B - 1 = -(1 - w ^ B) by ring,
      neg_div_neg_eq]
  rw [h2, div_le_div_iff₀ hw hw, one_mul]
  simpa using mul_le_mul_of_nonneg_right (sub_le_self 1 (pow_nonneg hw0 B)) hw.le

/-- **Finite Euler-product bound.**  For a finite set `P` of primes and weights
`0 ≤ w p < 1`, the sum of `∏_{p ∈ P} w p ^ (a.factorization p)` over nonzero
`a < X` whose prime factors all lie in `P` is at most `∏_{p ∈ P} (1 - w p)⁻¹`.

The exponent map `a ↦ (a.factorization p)_{p ∈ P}` injects the summands into the
pi finset `P.pi (fun p ↦ range (Nat.log p (X-1) + 1))`, where the sum factors as
a product of finite geometric sums. -/
theorem sum_factorization_prod_le (X : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hw0 : ∀ p ∈ P, 0 ≤ w p) (hw1 : ∀ p ∈ P, w p < 1) :
    ∑ a ∈ (Finset.range X).filter (fun a ↦ a ≠ 0 ∧ ∀ p ∈ a.primeFactors, p ∈ P),
        ∏ p ∈ P, w p ^ a.factorization p
      ≤ ∏ p ∈ P, (1 - w p)⁻¹ := by
  classical
  set S := (Finset.range X).filter
    (fun a ↦ a ≠ 0 ∧ ∀ p ∈ a.primeFactors, p ∈ P) with hS
  have hRHS : 0 ≤ ∏ p ∈ P, (1 - w p)⁻¹ :=
    Finset.prod_nonneg fun p hp ↦ inv_nonneg.mpr (sub_nonneg.mpr (hw1 p hp).le)
  rcases Nat.lt_or_ge X 2 with hX | hX
  · -- `X ≤ 1`: the filtered set is empty.
    have hSe : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have haX : a < X := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have ha0 : a ≠ 0 := (Finset.mem_filter.mp ha).2.1
      omega
    rw [hSe, Finset.sum_empty]
    exact hRHS
  have hX1 : X - 1 ≠ 0 := by omega
  -- exponent tuples land in the pi finset
  have hφmem : ∀ a ∈ S,
      (fun p (_ : p ∈ P) ↦ a.factorization p) ∈
        P.pi (fun p ↦ Finset.range (Nat.log p (X - 1) + 1)) := by
    intro a ha
    rw [Finset.mem_pi]
    intro p hp
    have haX : a < X := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have ha0 : a ≠ 0 := (Finset.mem_filter.mp ha).2.1
    have hpow : p ^ a.factorization p ≤ a :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) (Nat.ordProj_dvd a p)
    have hlog : a.factorization p ≤ Nat.log p (X - 1) :=
      (Nat.le_log_iff_pow_le (hP p hp).one_lt hX1).mpr
        (le_trans hpow (Nat.le_pred_of_lt haX))
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hlog)
  -- `a` is recovered from its exponent tuple
  have hφinj : Set.InjOn (fun (a : ℕ) p (_ : p ∈ P) ↦ a.factorization p) ↑S := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    have key : ∀ c ∈ S, c = ∏ p ∈ P, p ^ c.factorization p := by
      intro c hc
      have hc0 : c ≠ 0 := (Finset.mem_filter.mp hc).2.1
      have hsub : c.primeFactors ⊆ P := (Finset.mem_filter.mp hc).2.2
      have hself : ∏ p ∈ c.primeFactors, p ^ c.factorization p = c :=
        Nat.prod_factorization_pow_eq_self hc0
      conv_lhs => rw [← hself]
      exact Finset.prod_subset hsub fun p hpP hpn ↦ by
        show p ^ c.factorization p = 1
        rw [Nat.factorization_eq_zero_of_not_dvd
          (fun hdvd ↦ hpn (Nat.mem_primeFactors.mpr ⟨hP p hpP, hdvd, hc0⟩)),
          pow_zero]
    rw [key a ha, key b hb]
    apply Finset.prod_congr rfl
    intro p hp
    have hh : a.factorization p = b.factorization p :=
      congrFun (congrFun hab p) hp
    rw [hh]
  calc ∑ a ∈ S, ∏ p ∈ P, w p ^ a.factorization p
      = ∑ a ∈ S, ∏ x ∈ P.attach, w x.1 ^ a.factorization x.1 :=
          Finset.sum_congr rfl fun a _ ↦
            (Finset.prod_attach P (fun p ↦ w p ^ a.factorization p)).symm
    _ = ∑ f ∈ S.image (fun a p (_ : p ∈ P) ↦ a.factorization p),
          ∏ x ∈ P.attach, w x.1 ^ f x.1 x.2 := by
        exact (Finset.sum_image
          (f := fun f ↦ ∏ x ∈ P.attach, w x.1 ^ f x.1 x.2) hφinj).symm
    _ ≤ ∑ f ∈ P.pi (fun p ↦ Finset.range (Nat.log p (X - 1) + 1)),
          ∏ x ∈ P.attach, w x.1 ^ f x.1 x.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · rwa [Finset.image_subset_iff]
        · intro f _ _
          exact Finset.prod_nonneg fun x _ ↦ pow_nonneg (hw0 x.1 x.2) _
    _ = ∏ p ∈ P, ∑ e ∈ Finset.range (Nat.log p (X - 1) + 1), w p ^ e := by
        exact (Finset.prod_sum P (fun p ↦ Finset.range (Nat.log p (X - 1) + 1))
          (fun p e ↦ w p ^ e)).symm
    _ ≤ ∏ p ∈ P, (1 - w p)⁻¹ :=
        Finset.prod_le_prod₀
          (fun p hp ↦ Finset.sum_nonneg fun e _ ↦ pow_nonneg (hw0 p hp) e)
          (fun p hp ↦ sum_range_pow_le_inv_one_sub (hw0 p hp) (hw1 p hp) _)

/-- **Rankin form of the complement-mass bound.**
For `0 < z ≤ 1`:

  `∑_{a < X : Ω_{>Y}(a) ≤ t} 1/a
     ≤ z^{-t} · (∏_{p ≤ Y} (1 - 1/p)⁻¹) · (∏_{Y < p < X} (1 - z/p)⁻¹)`. -/
theorem recipSum_le_of_largeOmegaFac_le_z (X Y t : ℕ) {z : ℝ} (hz : 0 < z)
    (hz1 : z ≤ 1) :
    (∑ a ∈ Finset.range X,
      if (∑ p ∈ (Nat.primesBelow X).filter (fun p ↦ Y < p), a.factorization p) ≤ t
        then (1:ℝ)/a else 0)
      ≤ (z ^ t)⁻¹ *
          ((∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1:ℝ)/p)⁻¹) *
            ∏ p ∈ (Nat.primesBelow X).filter (fun p ↦ Y < p), (1 - z/(p:ℝ))⁻¹) := by
  classical
  set P₂ : Finset ℕ := (Nat.primesBelow X).filter (fun p ↦ Y < p) with hP₂
  set P₁ : Finset ℕ := Nat.primesBelow (Y + 1) with hP₁
  set P : Finset ℕ := P₁ ∪ P₂ with hP
  have hP₁mem : ∀ p ∈ P₁, p.Prime ∧ p ≤ Y := by
    intro p hp
    have h := Nat.mem_primesBelow.mp (hP₁ ▸ hp)
    exact ⟨h.2, by omega⟩
  have hP₂mem : ∀ p ∈ P₂, p.Prime ∧ Y < p ∧ p < X := by
    intro p hp
    have h := Finset.mem_filter.mp (hP₂ ▸ hp)
    have h' := Nat.mem_primesBelow.mp h.1
    exact ⟨h'.2, h.2, h'.1⟩
  have hdisj : Disjoint P₁ P₂ := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (hP₁mem p hp1).2
    have h2 := (hP₂mem p hp2).2.1
    omega
  have hprimeP : ∀ p ∈ P, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp (hP ▸ hp) with hp1 | hp2
    · exact (hP₁mem p hp1).1
    · exact (hP₂mem p hp2).1
  have hsupp : ∀ a ∈ Finset.range X, a ≠ 0 → ∀ p ∈ a.primeFactors, p ∈ P := by
    intro a haX ha0 p hp
    have hpa : p ≤ a :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) (Nat.dvd_of_mem_primeFactors hp)
    have hpX : p < X := lt_of_le_of_lt hpa (Finset.mem_range.mp haX)
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [hP]
    rcases le_or_gt p Y with h | h
    · exact Finset.mem_union_left _
        (hP₁ ▸ Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩)
    · exact Finset.mem_union_right _
        (hP₂ ▸ Finset.mem_filter.mpr
          ⟨Nat.mem_primesBelow.mpr ⟨hpX, hprime⟩, h⟩)
  have hwP₁ : ∀ p ∈ P₁, massWeight Y z p = 1/(p:ℝ) :=
    fun p hp ↦ if_pos (hP₁mem p hp).2
  have hwP₂ : ∀ p ∈ P₂, massWeight Y z p = z/(p:ℝ) := fun p hp ↦ by
    have h := (hP₂mem p hp).2.1
    exact if_neg (by omega)
  have hw_nonneg : ∀ p ∈ P, 0 ≤ massWeight Y z p := by
    intro p hp
    rcases Finset.mem_union.mp (hP ▸ hp) with hp1 | hp2
    · rw [hwP₁ p hp1]; positivity
    · rw [hwP₂ p hp2]; exact div_nonneg hz.le (Nat.cast_nonneg _)
  have hw_lt : ∀ p ∈ P, massWeight Y z p < 1 := by
    intro p hp
    rcases Finset.mem_union.mp (hP ▸ hp) with hp1 | hp2
    · rw [hwP₁ p hp1]
      have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (hP₁mem p hp1).1.two_le
      have hpos : (0:ℝ) < (p:ℝ) := by positivity
      calc (1:ℝ)/p ≤ 1/2 := (one_div_le_one_div_of_le (by norm_num) h2)
        _ < 1 := by norm_num
    · rw [hwP₂ p hp2]
      have hpos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (hP₂mem p hp2).1.pos
      rw [div_lt_iff₀ hpos, one_mul]
      exact lt_of_le_of_lt hz1
        (by exact_mod_cast (hP₂mem p hp2).1.one_lt)
  -- rewrite the `ite` sum as a filtered sum and drop `a = 0` (whose term is `1/0 = 0`)
  have hstep : (∑ a ∈ Finset.range X,
        if (∑ p ∈ P₂, a.factorization p) ≤ t then (1:ℝ)/a else 0)
      = ∑ a ∈ (Finset.range X).filter
          (fun a ↦ (∑ p ∈ P₂, a.factorization p) ≤ t ∧ a ≠ 0), (1:ℝ)/a := by
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro a ha
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1⟩
    · intro a ha hun
      have ha0 : a = 0 := by
        by_contra hne
        exact hun (Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2, hne⟩)
      rw [ha0]
      simp
  rw [hstep]
  -- pointwise Rankin bound: `1/a ≤ z^{-t} ∏_{p ∈ P} w p^{a.factorization p}`
  have hpoint : ∀ a ∈ (Finset.range X).filter
        (fun a ↦ (∑ p ∈ P₂, a.factorization p) ≤ t ∧ a ≠ 0),
      (1:ℝ)/a ≤ (z ^ t)⁻¹ * ∏ p ∈ P, massWeight Y z p ^ a.factorization p := by
    intro a ha
    have haX : a < X := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hcond : (∑ p ∈ P₂, a.factorization p) ≤ t := (Finset.mem_filter.mp ha).2.1
    have ha0 : a ≠ 0 := (Finset.mem_filter.mp ha).2.2
    have hsupp_a : ∀ p ∈ a.primeFactors, p ∈ P :=
      hsupp a (Finset.mem_range.mpr haX) ha0
    have hself : ∏ p ∈ a.primeFactors, p ^ a.factorization p = a :=
      Nat.prod_factorization_pow_eq_self ha0
    have hprodP : ∏ p ∈ P, (p:ℝ) ^ a.factorization p = (a:ℝ) := by
      have hsub2 : ∏ p ∈ a.primeFactors, (p:ℝ) ^ a.factorization p =
          ∏ p ∈ P, (p:ℝ) ^ a.factorization p :=
        Finset.prod_subset hsupp_a fun p hpP hpn ↦ by
          rw [Nat.factorization_eq_zero_of_not_dvd
            (fun hdvd ↦ hpn (Nat.mem_primeFactors.mpr
              ⟨hprimeP p hpP, hdvd, ha0⟩)), pow_zero]
      rw [← hsub2]
      exact_mod_cast hself
    -- the `P₁`-factors give `1/u`, the `P₂`-factors give `z^{Ω_{>Y}}/v`
    have hA : ∏ p ∈ P₁, massWeight Y z p ^ a.factorization p =
        (∏ p ∈ P₁, (p:ℝ) ^ a.factorization p)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [hwP₁ p hp, one_div, inv_pow]
    have hB : ∏ p ∈ P₂, massWeight Y z p ^ a.factorization p =
        z ^ (∑ p ∈ P₂, a.factorization p) /
          (∏ p ∈ P₂, (p:ℝ) ^ a.factorization p) := by
      calc ∏ p ∈ P₂, massWeight Y z p ^ a.factorization p
          = ∏ p ∈ P₂, (z/(p:ℝ)) ^ a.factorization p :=
            Finset.prod_congr rfl fun p hp ↦ by rw [hwP₂ p hp]
        _ = ∏ p ∈ P₂, z ^ a.factorization p / (p:ℝ) ^ a.factorization p :=
            Finset.prod_congr rfl fun p hp ↦ by rw [div_pow]
        _ = (∏ p ∈ P₂, z ^ a.factorization p) /
              ∏ p ∈ P₂, (p:ℝ) ^ a.factorization p :=
            Finset.prod_div_distrib _ _
        _ = z ^ (∑ p ∈ P₂, a.factorization p) /
              ∏ p ∈ P₂, (p:ℝ) ^ a.factorization p := by
            rw [Finset.prod_pow_eq_pow_sum]
    have hkey : ∏ p ∈ P, massWeight Y z p ^ a.factorization p =
        z ^ (∑ p ∈ P₂, a.factorization p) / (a:ℝ) := by
      have huv : (∏ p ∈ P₁, (p:ℝ) ^ a.factorization p) *
          ∏ p ∈ P₂, (p:ℝ) ^ a.factorization p = (a:ℝ) := by
        have h := hprodP
        rw [hP, Finset.prod_union hdisj] at h
        exact h
      rw [hP, Finset.prod_union hdisj, hA, hB]
      calc (∏ p ∈ P₁, (p:ℝ) ^ a.factorization p)⁻¹ *
            (z ^ (∑ p ∈ P₂, a.factorization p) /
              ∏ p ∈ P₂, (p:ℝ) ^ a.factorization p)
          = z ^ (∑ p ∈ P₂, a.factorization p) *
              ((∏ p ∈ P₁, (p:ℝ) ^ a.factorization p)⁻¹ *
                (∏ p ∈ P₂, (p:ℝ) ^ a.factorization p)⁻¹) := by
            rw [div_eq_mul_inv]; ring
        _ = z ^ (∑ p ∈ P₂, a.factorization p) /
              ((∏ p ∈ P₁, (p:ℝ) ^ a.factorization p) *
                ∏ p ∈ P₂, (p:ℝ) ^ a.factorization p) := by
            rw [← mul_inv, ← div_eq_mul_inv]
        _ = z ^ (∑ p ∈ P₂, a.factorization p) / (a:ℝ) := by rw [huv]
    -- `z^{S₂} ≥ z^t` because `S₂ ≤ t` and `z ≤ 1`
    have hdec : t = (∑ p ∈ P₂, a.factorization p) +
        (t - ∑ p ∈ P₂, a.factorization p) := (Nat.add_sub_of_le hcond).symm
    have hzpow : z ^ t ≤ z ^ (∑ p ∈ P₂, a.factorization p) := by
      conv_lhs => rw [hdec, pow_add]
      calc z ^ (∑ p ∈ P₂, a.factorization p) * z ^ (t - ∑ p ∈ P₂, a.factorization p)
          ≤ z ^ (∑ p ∈ P₂, a.factorization p) * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hz.le hz1) (pow_pos hz _).le
        _ = z ^ (∑ p ∈ P₂, a.factorization p) := mul_one _
    have hapos : (0:ℝ) < (a:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha0)
    have h5 : (1:ℝ)/a ≤ (z ^ (∑ p ∈ P₂, a.factorization p) / z ^ t) / a := by
      apply div_le_div_of_nonneg_right _ hapos.le
      rw [one_le_div (pow_pos hz t)]
      exact hzpow
    calc (1:ℝ)/a ≤ (z ^ (∑ p ∈ P₂, a.factorization p) / z ^ t) / a := h5
      _ = (z ^ t)⁻¹ * (z ^ (∑ p ∈ P₂, a.factorization p) / a) := by
          rw [div_div, div_eq_mul_inv, mul_inv, div_eq_mul_inv]
          ring
      _ = (z ^ t)⁻¹ * ∏ p ∈ P, massWeight Y z p ^ a.factorization p := by
          rw [hkey]
  calc ∑ a ∈ (Finset.range X).filter
          (fun a ↦ (∑ p ∈ P₂, a.factorization p) ≤ t ∧ a ≠ 0), (1:ℝ)/a
      ≤ ∑ a ∈ (Finset.range X).filter
          (fun a ↦ (∑ p ∈ P₂, a.factorization p) ≤ t ∧ a ≠ 0),
          (z ^ t)⁻¹ * ∏ p ∈ P, massWeight Y z p ^ a.factorization p :=
        Finset.sum_le_sum hpoint
    _ = (z ^ t)⁻¹ * ∑ a ∈ (Finset.range X).filter
          (fun a ↦ (∑ p ∈ P₂, a.factorization p) ≤ t ∧ a ≠ 0),
          ∏ p ∈ P, massWeight Y z p ^ a.factorization p := by
        rw [Finset.mul_sum]
    _ ≤ (z ^ t)⁻¹ * ∑ a ∈ (Finset.range X).filter
          (fun a ↦ a ≠ 0 ∧ ∀ p ∈ a.primeFactors, p ∈ P),
          ∏ p ∈ P, massWeight Y z p ^ a.factorization p := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_pos hz t).le)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          have ha' := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨ha'.1, ha'.2.2, hsupp a ha'.1 ha'.2.2⟩
        · intro a _ _
          exact Finset.prod_nonneg fun p hp ↦ pow_nonneg (hw_nonneg p hp) _
    _ ≤ (z ^ t)⁻¹ * ∏ p ∈ P, (1 - massWeight Y z p)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_pos hz t).le)
        exact sum_factorization_prod_le X P (massWeight Y z) hprimeP hw_nonneg hw_lt
    _ = (z ^ t)⁻¹ * ((∏ p ∈ P₁, (1 - (1:ℝ)/p)⁻¹) *
          ∏ p ∈ P₂, (1 - z/(p:ℝ))⁻¹) := by
        rw [hP, Finset.prod_union hdisj]
        have e1 : ∏ p ∈ P₁, (1 - massWeight Y z p)⁻¹ =
            ∏ p ∈ P₁, (1 - (1:ℝ)/p)⁻¹ :=
          Finset.prod_congr rfl fun p hp ↦ by rw [hwP₁ p hp]
        have e2 : ∏ p ∈ P₂, (1 - massWeight Y z p)⁻¹ =
            ∏ p ∈ P₂, (1 - z/(p:ℝ))⁻¹ :=
          Finset.prod_congr rfl fun p hp ↦ by rw [hwP₂ p hp]
        rw [e1, e2]

/-- `(1 - x)⁻¹ ≤ exp (2x)` for `0 ≤ x ≤ 1/2`. -/
theorem inv_one_sub_le_exp_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have h1 : (0:ℝ) < 1 - x := by linarith
  have h2 : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ h1]
    nlinarith [mul_nonneg hx0 (by linarith : (0:ℝ) ≤ 1 - 2 * x)]
  have h3 := Real.add_one_le_exp (2 * x)
  linarith

/-- `∏_{p ∈ P} (1 - z/p)⁻¹ ≤ exp (2z · ∑_{p ∈ P} 1/p)` for `0 ≤ z ≤ 1` and
`2 ≤ p` on `P`. -/
theorem prod_one_sub_zdiv_inv_le_exp (P : Finset ℕ) {z : ℝ} (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) (hP : ∀ p ∈ P, 2 ≤ p) :
    ∏ p ∈ P, (1 - z/(p:ℝ))⁻¹ ≤ Real.exp (2 * z * ∑ p ∈ P, (1:ℝ)/p) := by
  calc ∏ p ∈ P, (1 - z/(p:ℝ))⁻¹
      ≤ ∏ p ∈ P, Real.exp (2 * (z/(p:ℝ))) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hP p hp
          have hpos : (0:ℝ) < (p:ℝ) := by positivity
          apply inv_nonneg.mpr
          have hzp : z/(p:ℝ) ≤ 1/2 := by
            rw [div_le_iff₀ hpos]
            linarith
          linarith
        · intro p hp
          have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hP p hp
          have hpos : (0:ℝ) < (p:ℝ) := by positivity
          apply inv_one_sub_le_exp_two_mul
          · exact div_nonneg hz0 (Nat.cast_nonneg _)
          · rw [div_le_iff₀ hpos]
            linarith
    _ = Real.exp (∑ p ∈ P, 2 * (z/(p:ℝ))) := by
        rw [← Real.exp_sum]
    _ = Real.exp (2 * z * ∑ p ∈ P, (1:ℝ)/p) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring

/-- **Packaged complement-mass bound.**  For `1 ≤ t ≤ E' + 1` with
`E' = ∑_{Y < p < X, p prime} 1/p`,

  `∑_{a < X : Ω_{>Y}(a) ≤ t} 1/a
     ≤ (∏_{p ≤ Y} (1 - 1/p)⁻¹) · (2e(E' + 1)/t)^t`.

Take `z = t/(2(E'+1))` in `recipSum_le_of_largeOmegaFac_le_z` and use
`∏_{p} (1 - z/p)⁻¹ ≤ exp(2zE') ≤ e^t`. -/
theorem recipSum_le_of_largeOmegaFac_le (X Y t : ℕ) (ht : 1 ≤ t)
    (htE : (t : ℝ) ≤
      (∑ p ∈ (Nat.primesBelow X).filter (fun p ↦ Y < p), (1:ℝ)/p) + 1) :
    (∑ a ∈ Finset.range X,
      if (∑ p ∈ (Nat.primesBelow X).filter (fun p ↦ Y < p), a.factorization p) ≤ t
        then (1:ℝ)/a else 0)
      ≤ (∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1:ℝ)/p)⁻¹) *
          (2 * Real.exp 1 *
            ((∑ p ∈ (Nat.primesBelow X).filter (fun p ↦ Y < p), (1:ℝ)/p) + 1) /
            (t:ℝ)) ^ t := by
  classical
  set P₂ : Finset ℕ := (Nat.primesBelow X).filter (fun p ↦ Y < p) with hP₂
  set E' : ℝ := ∑ p ∈ P₂, (1:ℝ)/p with hE'
  set S : ℝ := E' + 1 with hS
  set z : ℝ := (t:ℝ)/(2*S) with hz
  have hE'0 : 0 ≤ E' := Finset.sum_nonneg fun p _ ↦ by positivity
  have hS0 : (0:ℝ) < S := by rw [hS]; linarith
  have hSne : S ≠ 0 := hS0.ne'
  have ht0 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hz0 : (0:ℝ) < z := by
    rw [hz]
    apply div_pos (by linarith) (by linarith)
  have hz1 : z ≤ 1 := by
    rw [hz]
    rw [div_le_one (by linarith : (0:ℝ) < 2*S)]
    linarith [htE]
  have hmain := recipSum_le_of_largeOmegaFac_le_z X Y t hz0 hz1
  -- `∏_{p ∈ P₂} (1 - z/p)⁻¹ ≤ e^t`
  have hprod2 : ∏ p ∈ P₂, (1 - z/(p:ℝ))⁻¹ ≤ Real.exp (2 * z * E') := by
    apply prod_one_sub_zdiv_inv_le_exp P₂ hz0.le hz1
    intro p hp
    exact (Nat.prime_of_mem_primesBelow
      (Finset.mem_filter.mp (hP₂ ▸ hp)).1).two_le
  have hz_eq : 2 * z * E' = (t:ℝ) * E' / S := by
    rw [hz, ← mul_div_assoc, mul_div_mul_left _ _ (two_ne_zero),
      div_mul_eq_mul_div₀]
  have h2z : 2 * z * E' ≤ (t:ℝ) := by
    rw [hz_eq, div_le_iff₀ hS0]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg t)
    rw [hS]; linarith
  have hexp2 : ∏ p ∈ P₂, (1 - z/(p:ℝ))⁻¹ ≤ Real.exp 1 ^ t := by
    calc ∏ p ∈ P₂, (1 - z/(p:ℝ))⁻¹ ≤ Real.exp (2 * z * E') := hprod2
      _ ≤ Real.exp (t:ℝ) := Real.exp_le_exp_of_le h2z
      _ = Real.exp 1 ^ t := (Real.exp_one_pow t).symm
  have hzinv : (z ^ t)⁻¹ = (2 * S / (t:ℝ)) ^ t := by
    rw [← inv_pow]
    congr 1
    rw [hz, inv_div]
  have hP₁nonneg : 0 ≤ ∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1:ℝ)/p)⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    have h2 : (2:ℝ) ≤ (p:ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    apply inv_nonneg.mpr
    have h1p : (1:ℝ)/p ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < (p:ℝ))]
      linarith
    linarith
  have hP₂nonneg : 0 ≤ ∏ p ∈ P₂, (1 - z/(p:ℝ))⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    have h2 : (2:ℝ) ≤ (p:ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow
        (Finset.mem_filter.mp (hP₂ ▸ hp)).1).two_le
    apply inv_nonneg.mpr
    have hzp : z/(p:ℝ) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (p:ℝ))]
      linarith [hz1]
    linarith
  have hbase : 0 ≤ (2 * S / (t:ℝ)) ^ t := by
    apply pow_nonneg
    apply div_nonneg (by linarith) (by linarith)
  calc (∑ a ∈ Finset.range X,
        if (∑ p ∈ P₂, a.factorization p) ≤ t then (1:ℝ)/a else 0)
      ≤ (z ^ t)⁻¹ * ((∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1:ℝ)/p)⁻¹) *
          ∏ p ∈ P₂, (1 - z/(p:ℝ))⁻¹) := hmain
    _ = (∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1:ℝ)/p)⁻¹) *
          ((z ^ t)⁻¹ * ∏ p ∈ P₂, (1 - z/(p:ℝ))⁻¹) := by ring
    _ ≤ (∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1:ℝ)/p)⁻¹) *
          ((2 * S / (t:ℝ)) ^ t * Real.exp 1 ^ t) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (le_of_eq hzinv) hexp2 hP₂nonneg hbase) hP₁nonneg
    _ = (∏ p ∈ Nat.primesBelow (Y + 1), (1 - (1:ℝ)/p)⁻¹) *
          (2 * Real.exp 1 * S / (t:ℝ)) ^ t := by
        congr 1
        rw [show (2 * Real.exp 1 * S / (t:ℝ)) = (2 * S / (t:ℝ)) * Real.exp 1
            by ring, mul_pow]