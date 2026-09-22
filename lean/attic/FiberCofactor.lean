import JSP361.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic

/-!
# JSP-000361 — cofactor-fiber pigeonhole

`exists_pp_fiber`: every `a ∈ S` is divisible by a prime power `p^e > s`;
writing `a = p^e * m` with `m = a / p^e ≤ a / s ≤ y / s` puts `a` in the
`m`-th "fiber".  A pigeonhole over `m ∈ range (y/s + 1)` gives a fiber `F`
of size `≥ S.card / (y/s + 1)` whose elements share the cofactor `m₀`.

`dA_fiber_prod_ge`: the elements of such a fiber all divide
`m₀ * ∏_{a ∈ F} a / m₀`, hence `F.card ≤ dA A (m₀ * ∏ a / m₀)`.

`fiber_prod_le`: `m₀ * ∏_{a ∈ F} a / m₀ ≤ y ^ (F.card + 1)`.
-/

namespace JSP361

open Finset
open scoped Classical

theorem exists_pp_fiber {A : Set ℕ} {S : Finset ℕ} (hSA : ∀ a ∈ S, a ∈ A)
    (hS0 : ∀ a ∈ S, a ≠ 0) {s y : ℕ} (hs : 0 < s) (hy : 0 < y)
    (hSy : ∀ a ∈ S, a < y)
    (hp : ∀ a ∈ S, ∃ p : ℕ, p.Prime ∧ ∃ e : ℕ, 1 ≤ e ∧ s < p ^ e ∧ p ^ e ∣ a) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ m₀ ≤ y / s ∧ ∃ F : Finset ℕ, F ⊆ S ∧
      S.card ≤ F.card * (y / s + 1) ∧
      ∀ a ∈ F, m₀ ∣ a ∧ s < a / m₀ := by
  classical
  -- index set of cofactors
  have hne : (Finset.range (y / s + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  obtain ⟨m₀, hm₀mem, hmax⟩ := Finset.exists_max_image (Finset.range (y / s + 1))
    (fun m ↦ (S.filter fun a ↦ ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ s < p ^ e ∧
      a = p ^ e * m).card) hne
  have hm₀le : m₀ ≤ y / s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm₀mem)
  -- every a ∈ S lands in the fiber of its cofactor a / p^e
  have hsub : S ⊆ (Finset.range (y / s + 1)).biUnion
      (fun m ↦ S.filter fun a ↦ ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ s < p ^ e ∧
        a = p ^ e * m) := by
    intro a ha
    obtain ⟨p, hpP, e, he1, hspe, hdvd⟩ := hp a ha
    rw [Finset.mem_biUnion]
    refine ⟨a / p ^ e, Finset.mem_range.mpr ?_, Finset.mem_filter.mpr ?_⟩
    · have h1 : a / p ^ e ≤ a / s := Nat.div_le_div_left (le_of_lt hspe) hs
      have h2 : a / s ≤ y / s := Nat.div_le_div_right (Nat.le_of_lt (hSy a ha))
      omega
    · exact ⟨ha, p, e, hpP, he1, hspe, (Nat.mul_div_cancel' hdvd).symm⟩
  have hbound : S.card ≤ (S.filter fun a ↦ ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧
      s < p ^ e ∧ a = p ^ e * m₀).card * (y / s + 1) := by
    have h := ((Finset.card_le_card hsub).trans Finset.card_biUnion_le).trans
      (Finset.sum_le_card_nsmul _ _ _ fun m hm ↦ hmax m hm)
    rw [Finset.card_range, nsmul_eq_mul] at h
    exact h.trans (le_of_eq (Nat.mul_comm _ _))
  rcases (S.filter fun a ↦ ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ s < p ^ e ∧
      a = p ^ e * m₀).eq_empty_or_nonempty with hFe | hFne
  · -- the max fiber is empty ⇒ S.card ≤ 0 ⇒ S = ∅
    have hSe : S = ∅ := by
      rw [hFe] at hbound
      simp only [Finset.card_empty, Nat.zero_mul] at hbound
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hbound)
    subst hSe
    rcases Nat.lt_or_ge y s with hsy | hsy
    · rw [Nat.div_eq_of_lt hsy]
      omega
    · exact ⟨1, Nat.one_pos,
        (Nat.le_div_iff_mul_le hs).mpr (by rwa [Nat.one_mul]),
        ∅, Finset.empty_subset _, by simp,
        fun a ha ↦ absurd ha (Finset.notMem_empty a)⟩
  · obtain ⟨a, haF⟩ := hFne
    rw [Finset.mem_filter] at haF
    obtain ⟨haS, p, e, hpP, he1, hspe, haeq⟩ := haF
    have hm₀pos : 0 < m₀ := by
      rcases Nat.eq_zero_or_pos m₀ with h0 | h0
      · rw [h0, Nat.mul_zero] at haeq
        exact absurd haeq (hS0 a haS)
      · exact h0
    refine ⟨m₀, hm₀pos, hm₀le,
      S.filter fun a ↦ ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ s < p ^ e ∧ a = p ^ e * m₀,
      Finset.filter_subset _ _, hbound, fun b hbF ↦ ?_⟩
    rw [Finset.mem_filter] at hbF
    obtain ⟨hbS, q, f, hqP, hf1, hqsf, hbeq⟩ := hbF
    refine ⟨?_, ?_⟩
    · rw [hbeq]
      exact dvd_mul_left m₀ (q ^ f)
    · rw [hbeq, Nat.mul_div_cancel _ hm₀pos]
      exact hqsf

theorem dA_fiber_prod_ge (A : Set ℕ) {m₀ : ℕ} {F : Finset ℕ} (hm : 0 < m₀)
    (hF : ∀ a ∈ F, a ∈ A ∧ m₀ ∣ a ∧ a ≠ 0) :
    F.card ≤ dA A (m₀ * ∏ a ∈ F, a / m₀) := by
  apply card_le_dA
  · intro a ha
    obtain ⟨hAa, hdvd, _⟩ := hF a ha
    refine ⟨hAa, ?_⟩
    have h1 : a / m₀ ∣ ∏ b ∈ F, b / m₀ := Finset.dvd_prod_of_mem _ ha
    exact (Nat.mul_div_cancel' hdvd) ▸ mul_dvd_mul_left m₀ h1
  · have hprod : (∏ a ∈ F, a / m₀) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro b hb
      obtain ⟨_, hdvd, hb0⟩ := hF b hb
      exact Nat.pos_iff_ne_zero.mp
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hb0) hdvd) hm)
    exact mul_ne_zero (Nat.pos_iff_ne_zero.mp hm) hprod

theorem fiber_prod_le {m₀ : ℕ} {F : Finset ℕ} {y : ℕ} (hm : m₀ ≤ y)
    (hb : ∀ a ∈ F, a < y) :
    m₀ * ∏ a ∈ F, a / m₀ ≤ y ^ (F.card + 1) := by
  have hprod : (∏ a ∈ F, a / m₀) ≤ y ^ F.card :=
    Finset.prod_le_pow_card F (fun a ↦ a / m₀) y fun a ha ↦
      (Nat.div_le_self a m₀).trans (Nat.le_of_lt (hb a ha))
  calc m₀ * ∏ a ∈ F, a / m₀
      ≤ y * y ^ F.card := Nat.mul_le_mul hm hprod
    _ = y ^ (F.card + 1) := (pow_succ' y F.card).symm

end JSP361
