/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Roots.Antichain
public import WordCertDensity.Roots.Charge
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Reciprocal charge for nonrecurrent root pools

Actual visits fix both root and whole word. Distinct codes in any finite
catalogue therefore pay one reciprocal charge in total. Deterministic parsing
supplies code injectivity; extra metadata still requires identification.
-/

@[expose] public section

namespace WordCertDensity

namespace PhysicalHistory

/-- A nonrecurrent pool determines the root and whole word of a physical history. -/
theorem pool_unique {P : Set ℕ} (hP : NonrecurrentPool acceleratedStep P)
    {u v : ValuationWord} {root₁ root₂ x : ℕ}
    (hu : PhysicalHistory u root₁ x) (hv : PhysicalHistory v root₂ x)
    (h₁ : root₁ ∈ P) (h₂ : root₂ ∈ P) : root₁ = root₂ ∧ u = v := by
  obtain ⟨hlen, hroot⟩ := hP.visit_unique h₁ h₂ hu.accelerated_iterate hv.accelerated_iterate
  exact ⟨hroot, hu.word_eq_of_length_eq hv hlen⟩

end PhysicalHistory

namespace Roots

/-- Normalized realized charge, with an actual root value as the first coordinate. -/
noncomputable def poolWordCharge (code : ℕ × ValuationWord) (x : ℕ) : ℚ := by
  classical
  exact if PhysicalHistory code.2 code.1 x then code.2.slope / code.1 else 0

/-- Realized charge is the affine slope divided by the actual root. -/
theorem poolWordCharge_eq {code : ℕ × ValuationWord} {x : ℕ}
    (h : PhysicalHistory code.2 code.1 x) :
    poolWordCharge code x = code.2.slope / code.1 := by
  simp [poolWordCharge, h]

/-- An unrealized word contributes zero. -/
theorem poolWordCharge_eq_zero {code : ℕ × ValuationWord} {x : ℕ}
    (h : ¬ PhysicalHistory code.2 code.1 x) : poolWordCharge code x = 0 := by
  simp [poolWordCharge, h]

/-- Actual-root charge agrees exactly with the existing indexed-root charge. -/
theorem poolWordCharge_value (s x : ℕ) (w : ValuationWord) :
    poolWordCharge (value s, w) x = wordCharge (s, w) x := by
  rfl

/-- Distinct realized root/word codes in a nonrecurrent pool pay one total charge. -/
theorem sum_poolWordCharge_le_of_injOn {ι : Type*} {P : Set ℕ}
    (hP : NonrecurrentPool acceleratedStep P) (catalogue : Finset ι)
    (code : ι → ℕ × ValuationWord) (x : ℕ)
    (hroot : ∀ i ∈ catalogue, (code i).1 ∈ P)
    (hinj : Set.InjOn code (↑catalogue : Set ι)) :
    (∑ i ∈ catalogue, poolWordCharge (code i) x) ≤ 1 / (x : ℚ) := by
  classical
  by_cases hex : ∃ i ∈ catalogue, PhysicalHistory (code i).2 (code i).1 x
  · obtain ⟨i, hi, hphysical⟩ := hex
    calc
      (∑ j ∈ catalogue, poolWordCharge (code j) x) = poolWordCharge (code i) x := by
        apply Finset.sum_eq_single_of_mem i hi
        intro j hj hji
        apply poolWordCharge_eq_zero
        intro hjphysical
        obtain ⟨hroot_eq, hword⟩ :=
          hjphysical.pool_unique hP hphysical (hroot j hj) (hroot i hi)
        exact hji (hinj hj hi (Prod.ext hroot_eq hword))
      _ ≤ 1 / (x : ℚ) := by
        rw [poolWordCharge_eq hphysical]
        exact hphysical.normalized_charge
  · have hzero : (∑ i ∈ catalogue, poolWordCharge (code i) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact poolWordCharge_eq_zero (fun h => hex ⟨i, hi, h⟩)
    rw [hzero]
    positivity

/-- A finite set of actual-root/whole-word pairs identifies duplicate codes. -/
theorem sum_poolWordCharge_le {P : Set ℕ} (hP : NonrecurrentPool acceleratedStep P)
    (catalogue : Finset (ℕ × ValuationWord)) (x : ℕ)
    (hroot : ∀ code ∈ catalogue, code.1 ∈ P) :
    (∑ code ∈ catalogue, poolWordCharge code x) ≤ 1 / (x : ℚ) :=
  sum_poolWordCharge_le_of_injOn hP catalogue id x hroot
    (by intro a ha b hb h; exact h)

/-- The literal root-by-word double sum has one reciprocal charge at each source. -/
theorem sum_poolWordCharge_double_le (pool : Finset ℕ)
    (hP : NonrecurrentPool acceleratedStep (↑pool : Set ℕ))
    (words : ℕ → Finset ValuationWord) (x : ℕ) :
    (∑ root ∈ pool, ∑ w ∈ words root, poolWordCharge (root, w) x) ≤ 1 / (x : ℚ) := by
  classical
  rw [Finset.sum_sigma']
  apply sum_poolWordCharge_le_of_injOn hP (pool.sigma words) (fun a => (a.1, a.2)) x
  · intro a ha
    exact (Finset.mem_sigma.mp ha).1
  · intro a ha b hb h
    exact Sigma.ext (congrArg Prod.fst h) (heq_of_eq (congrArg Prod.snd h))

end Roots

namespace BlockRule

/-- Deterministically parsed histories over a nonrecurrent pool pay one total charge. -/
theorem sum_parsedPoolCharge_le (rule : BlockRule) (stage : ℕ) {P : Set ℕ}
    (hP : NonrecurrentPool acceleratedStep P)
    (catalogue : Finset (ℕ × List ValuationWord)) (x : ℕ)
    (hp : ∀ entry ∈ catalogue, rule.Parses stage entry.2)
    (hroot : ∀ entry ∈ catalogue, entry.1 ∈ P) :
    (∑ entry ∈ catalogue, Roots.poolWordCharge (entry.1, entry.2.flatten) x) ≤
      1 / (x : ℚ) :=
  Roots.sum_poolWordCharge_le_of_injOn hP catalogue
    (fun entry => (entry.1, entry.2.flatten)) x hroot
    (rule.parsed_code_injOn stage catalogue hp)

end BlockRule

end WordCertDensity
