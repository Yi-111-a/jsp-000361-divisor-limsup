import JSP361.Defs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Card

/-!
# Rough elements and prime powers dividing `lcmUpto`

An element `a` divides `Nat.lcmUpto t` iff every prime power `p^e`
(with `p` prime, `e ≥ 1`) dividing `a` satisfies `p^e ≤ t`.
Consequently, elements of `A \ {0}` all of whose prime-power factors
are at most `s` are counted by `dA A (Nat.lcmUpto s)`.
-/

namespace JSP361

open Finset
open scoped Classical

/-- A prime power `p^e` with `e ≥ 1` divides `lcmUpto t` iff `p^e ≤ t`. -/
theorem pow_dvd_lcmUpto_iff {p e t : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    p ^ e ∣ Nat.lcmUpto t ↔ p ^ e ≤ t := by
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp.prime (Nat.lcmUpto_ne_zero t),
    Nat.factorization_lcmUpto t hp]
  rcases eq_or_ne t 0 with rfl | ht
  · rw [Nat.log_zero_right]
    exact ⟨fun h ↦ absurd h (by omega),
      fun h ↦ absurd h (Nat.not_le.mpr (Nat.pow_pos hp.pos))⟩
  · exact Nat.le_log_iff_pow_le hp.one_lt ht

/-- `a ∣ lcmUpto t` iff every prime power `p^e` dividing `a` with `p` prime
    and `e ≥ 1` satisfies `p^e ≤ t`. -/
theorem dvd_lcmUpto_iff {a t : ℕ} (ha : a ≠ 0) :
    a ∣ Nat.lcmUpto t ↔
      ∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e → p ^ e ∣ a → p ^ e ≤ t := by
  constructor
  · intro had p hp e he hpe
    exact (pow_dvd_lcmUpto_iff hp he).1 (hpe.trans had)
  · intro h
    rw [← Nat.factorization_prime_le_iff_dvd ha (Nat.lcmUpto_ne_zero t)]
    intro p hp
    rw [Nat.factorization_lcmUpto t hp]
    rcases eq_or_ne (a.factorization p) 0 with h0 | h0
    · rw [h0]
      exact Nat.zero_le _
    · have h1 : 1 ≤ a.factorization p := Nat.one_le_iff_ne_zero.mpr h0
      have hdvd : p ^ a.factorization p ∣ a :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp.prime ha).mpr le_rfl
      exact Nat.le_log_of_pow_le hp.one_lt (h p hp _ h1 hdvd)

/-- Every `a ∈ A \ {0}` all of whose prime-power factors are `≤ s`
divides `lcmUpto s`; hence the number of such `a` is `≤ dA A (lcmUpto s)`. -/
theorem powSmooth_le_dA_lcmUpto (A : Set ℕ) (s : ℕ) :
    ((Finset.range (Nat.lcmUpto s + 1)).filter (fun a ↦ a ∈ A \ {0} ∧
        ∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e → p ^ e ∣ a → p ^ e ≤ s)).card
      ≤ dA A (Nat.lcmUpto s) := by
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter] at ha ⊢
  rw [Finset.mem_range] at ha
  obtain ⟨hlt, haA, hcond⟩ := ha
  have ha0 : a ≠ 0 := fun h0 ↦ haA.2 (Set.mem_singleton_iff.mpr h0)
  exact ⟨Nat.mem_divisors.mpr
    ⟨(dvd_lcmUpto_iff ha0).2 hcond, Nat.lcmUpto_ne_zero s⟩, haA.1⟩

/-- Elements of `A` below `y` that have no prime-power factor `> s`
all divide `lcmUpto s`, hence their count is at most `dA A (lcmUpto s)`. -/
theorem countA_powSmooth_le (A : Set ℕ) (s y : ℕ) :
    (((Finset.range y).filter (fun a ↦ a ∈ A \ {0} ∧
        ∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e → p ^ e ∣ a → p ^ e ≤ s)).card : ℕ)
      ≤ dA A (Nat.lcmUpto s) := by
  refine le_trans ?_ (powSmooth_le_dA_lcmUpto A s)
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter] at ha ⊢
  rw [Finset.mem_range] at ha ⊢
  obtain ⟨hlt, haA, hcond⟩ := ha
  have ha0 : a ≠ 0 := fun h0 ↦ haA.2 (Set.mem_singleton_iff.mpr h0)
  have hdvd : a ∣ Nat.lcmUpto s := (dvd_lcmUpto_iff ha0).2 hcond
  exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.lcmUpto_pos s) hdvd)
    (Nat.lt_succ_self _), haA, hcond⟩

end JSP361
