/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Roots.Basins
public import WordCertDensity.Words.Parsing
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# One grouped charge per actual source

A source determines its nontrivial root and full physical word. A finite
catalogue of distinct such codes therefore contributes at most `1 / x`.
Prefix-free parsing discharges the distinct-code premise for parsed block
lists. Extra metadata or compression preimages still require identification
before applying this result; they cannot be counted as extra histories.
-/

@[expose] public section

namespace WordCertDensity

namespace Roots

/-- The normalized weight of a root/word code when it is realized at the source. -/
noncomputable def wordCharge (code : ℕ × ValuationWord) (x : ℕ) : ℚ := by
  classical
  exact if PhysicalHistory code.2 (value code.1) x then code.2.slope / value code.1 else 0

/-- A realized code pays its affine slope divided by the root. -/
theorem wordCharge_eq {code : ℕ × ValuationWord} {x : ℕ}
    (h : PhysicalHistory code.2 (value code.1) x) :
    wordCharge code x = code.2.slope / value code.1 := by
  simp [wordCharge, h]

/-- An unrealized code contributes no weight at this source. -/
theorem wordCharge_eq_zero {code : ℕ × ValuationWord} {x : ℕ}
    (h : ¬ PhysicalHistory code.2 (value code.1) x) : wordCharge code x = 0 := by
  simp [wordCharge, h]

/-- Distinct complete root/word codes pay at most one reciprocal source charge. -/
theorem sum_wordCharge_le_of_injOn {ι : Type*} (catalogue : Finset ι)
    (code : ι → ℕ × ValuationWord) (x : ℕ)
    (hroot : ∀ i ∈ catalogue, 1 < (code i).1)
    (hinj : Set.InjOn code (↑catalogue : Set ι)) :
    (∑ i ∈ catalogue, wordCharge (code i) x) ≤ 1 / (x : ℚ) := by
  classical
  by_cases hex : ∃ i ∈ catalogue, PhysicalHistory (code i).2 (value (code i).1) x
  · obtain ⟨i, hi, hphysical⟩ := hex
    calc
      (∑ j ∈ catalogue, wordCharge (code j) x) = wordCharge (code i) x := by
        apply Finset.sum_eq_single_of_mem i hi
        intro j hj hji
        apply wordCharge_eq_zero
        intro hjphysical
        obtain ⟨hindex, hword⟩ :=
          hjphysical.root_index_word_unique hphysical (hroot j hj) (hroot i hi)
        exact hji (hinj hj hi (Prod.ext hindex hword))
      _ ≤ 1 / (x : ℚ) := by
        rw [wordCharge_eq hphysical]
        exact hphysical.normalized_charge
  · have hzero : (∑ i ∈ catalogue, wordCharge (code i) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact wordCharge_eq_zero (fun h => hex ⟨i, hi, h⟩)
    rw [hzero]
    positivity

/-- A finite set of root/whole-word pairs already identifies duplicate codes. -/
theorem sum_wordCharge_le (catalogue : Finset (ℕ × ValuationWord)) (x : ℕ)
    (hroot : ∀ code ∈ catalogue, 1 < code.1) :
    (∑ code ∈ catalogue, wordCharge code x) ≤ 1 / (x : ℚ) :=
  sum_wordCharge_le_of_injOn catalogue id x hroot (by intro a ha b hb h; exact h)

end Roots

namespace BlockRule

/-- Valid parsed histories have distinct root/whole-word codes in a finite catalogue. -/
theorem parsed_code_injOn (rule : BlockRule) (stage : ℕ)
    (catalogue : Finset (ℕ × List ValuationWord))
    (hp : ∀ entry ∈ catalogue, rule.Parses stage entry.2) :
    Set.InjOn (fun entry : ℕ × List ValuationWord => (entry.1, entry.2.flatten))
      (↑catalogue : Set (ℕ × List ValuationWord)) := by
  intro a ha b hb he
  exact Prod.ext (congrArg (fun code : ℕ × ValuationWord => code.1) he)
    (flatten_injective (hp a ha) (hp b hb) (congrArg (fun code : ℕ × ValuationWord => code.2) he))

/-- Prefix-free parsed histories pooled over distinct roots have one total charge per source. -/
theorem sum_parsedCharge_le (rule : BlockRule) (stage : ℕ)
    (catalogue : Finset (ℕ × List ValuationWord)) (x : ℕ)
    (hp : ∀ entry ∈ catalogue, rule.Parses stage entry.2)
    (hroot : ∀ entry ∈ catalogue, 1 < entry.1) :
    (∑ entry ∈ catalogue, Roots.wordCharge (entry.1, entry.2.flatten) x) ≤ 1 / (x : ℚ) :=
  Roots.sum_wordCharge_le_of_injOn catalogue (fun entry => (entry.1, entry.2.flatten))
    x hroot (rule.parsed_code_injOn stage catalogue hp)

end BlockRule

end WordCertDensity
