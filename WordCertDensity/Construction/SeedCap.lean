/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Transfer.LetterCap
public import WordCertDensity.Construction.SeedPhysical

/-! # Explicit pointwise caps for the actual finite seed marks -/

@[expose] public section

namespace WordCertDensity.Construction

/-- The actual finite seed mark satisfies the manuscript's pointwise conductor cap. -/
theorem seedMark_cap (b n : ℕ) (y : ZMod (3 ^ seedConductor b n)) :
    0 ≤ seedMark b n y ∧ seedMark b n y ≤ (2 / 3 : ℝ) * 2 ^ seedConductor b n :=
  ⟨seedMark_nonneg b n y,
    (seedMark_le_marker b n y).trans (Reference.marker_le_two_pow _ y)⟩

/-- The same explicit cap holds for the literal physical mark at every guarded odd root. -/
theorem physicalSeedMark_cap {b root : ℕ} (hb : 32 ^ 5 ≤ b) (hr : 16 ^ b ≤ root)
    (hodd : Odd root) (n : ℕ) :
    0 ≤ physicalSeedMark b n root ∧
      physicalSeedMark b n root ≤ (2 / 3 : ℝ) * 2 ^ seedConductor b n := by
  rw [← seedMark_eq_physicalSeedMark hb hr hodd]
  exact seedMark_cap b n _

end WordCertDensity.Construction
