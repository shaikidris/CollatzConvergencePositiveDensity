/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.Data.InitialFractional
import WordCertDensity.Certificates.LevelThreeBounds

/-! # The initial fractional rows for the actual reference law -/

namespace WordCertDensity.Certificates

/-- The first integer tree encloses the exact first reference law. -/
theorem seedOne48_upper (x : ZMod (3 ^ 1)) :
    (2 : ℝ) ^ 48 * Reference.density 1 x ≤ seedOne48.lookup x.val := by
  obtain ⟨h0, h1, h2⟩ := Reference.density_one_values
  have hv (i : Fin 3) : Reference.density 1 i =
      (([0, 1, 2] : List ℝ)[i.val]?.getD 0) := by
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hu (i : Fin 3) :
      (2 : ℝ) ^ 48 * Reference.density 1 i ≤ seedOne48.lookup i.val := by
    rw [hv]
    fin_cases i <;> norm_num [seedOne48, Entries.lookup]
  exact hu x

/-- The retained first fractional row uses all three actual residues. -/
theorem fractional_one : Reference.moment (3 / 2) 1 ≤ 1276143 / 1000000 := by
  apply integer_fractional_even_certificate 1 24 1276143 1000000 (by decide)
    (fun x => seedOne48.lookup x.val) (fun x => seedOne48Roots.lookup x.val)
  · exact seedOne48_upper
  · exact seedOne48_square_enclosures
  · change 1000000 * (∑ x : ZMod (2 + 1),
      seedOne48.lookup x.val * seedOne48Roots.lookup x.val) ≤ _
    rw [sum_zmod_succ_list 2 (fun i => seedOne48.lookup i * seedOne48Roots.lookup i)]
    exact seedOne48_fractional_comparison

/-- The retained second fractional row uses all nine actual residues. -/
theorem fractional_two : Reference.moment (3 / 2) 2 ≤ 711317 / 500000 := by
  apply integer_fractional_even_certificate 2 24 711317 500000 (by decide)
    (fun x => seedTwo48.lookup x.val) (fun x => seedTwo48Roots.lookup x.val)
  · exact seedTwo48_upper
  · exact seedTwo48_square_enclosures
  · change 500000 * (∑ x : ZMod (8 + 1),
      seedTwo48.lookup x.val * seedTwo48Roots.lookup x.val) ≤ _
    rw [sum_zmod_succ_list 8 (fun i => seedTwo48.lookup i * seedTwo48Roots.lookup i)]
    exact seedTwo48_fractional_comparison

end WordCertDensity.Certificates
