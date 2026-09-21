/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The affine-tail Fourier argument is adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The source LICENSE and
NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This version identifies the local unrestricted word law and actual affine word map.
-/
module

public import WordCertDensity.Analytic.ConductorFourier
public import WordCertDensity.Transfer.AffineMap
import Mathlib.Tactic.Ring

/-!
# The unrestricted affine tail

The tail has exactly T independent geometric valuations. Its residue offset
is multiplied by 3^q 2^(-l) in the ambient group at level T+q. The original
PMF has total mass one; neither conditioning nor success normalization occurs.
-/

@[expose] public section

namespace WordCertDensity
namespace AffineTail

/-- The ambient scaled embedding of a residue at the tail level. -/
noncomputable def embed (q T l : ℕ) (z : ZMod (3 ^ T)) : ZMod (3 ^ (T + q)) :=
  (3 : ZMod (3 ^ (T + q))) ^ q * Reference.inverseTwoPow (T + q) l *
    (z.val : ZMod (3 ^ (T + q)))

/-- The actual unrestricted affine tail distribution. -/
noncomputable def law (q T l : ℕ) : PMF (ZMod (3 ^ (T + q))) :=
  (Reference.law T).map (embed q T l)

/-- Original real tail probability mass. -/
noncomputable def mass (q T l : ℕ) (x : ZMod (3 ^ (T + q))) : ℝ :=
  (law q T l x).toReal

/-- The tail is a direct pushforward of the unrestricted iid valuation-word PMF. -/
theorem law_eq_wordPMF (q T l : ℕ) :
    law q T l = (Reference.wordPMF T).map
      (fun w => embed q T l (ValuationWord.residueOffset T w)) := by
  simp only [law, Reference.law, PMF.map_comp, Function.comp_def]

/-- The affine word map consists of its head offset plus this scaled tail. -/
theorem wordMap_eq_offset_add_embed (w : ValuationWord) (T : ℕ) (z : ZMod (3 ^ T)) :
    Transfer.wordMap w (T + w.length)
        (z.val : ZMod (3 ^ (T + w.length - w.length))) =
      ValuationWord.residueOffset (T + w.length) w + embed w.length T w.total z := by
  rw [Transfer.wordMap_natCast w (Nat.le_add_left _ _)]
  rfl

private theorem residueOffset_natCast_of_eq {a b : ℕ} (h : a = b) (v : ValuationWord) :
    ValuationWord.residueOffset a v =
      ((ValuationWord.residueOffset b v).val : ZMod (3 ^ a)) := by
  subst b
  exact (ZMod.natCast_zmod_val (ValuationWord.residueOffset a v)).symm

/-- Appending a word gives the head offset plus the actual embedded tail offset. -/
theorem offset_append (w v : ValuationWord) (T : ℕ) :
    ValuationWord.residueOffset (T + w.length) (w ++ v) =
      ValuationWord.residueOffset (T + w.length) w +
        embed w.length T w.total (ValuationWord.residueOffset T v) := by
  rw [Transfer.wordMap_offset_append w v (Nat.le_add_left _ _)]
  rw [← wordMap_eq_offset_add_embed]
  apply congrArg (Transfer.wordMap w (T + w.length))
  exact residueOffset_natCast_of_eq (Nat.add_sub_cancel T w.length) v

/-- Every original tail atom is nonnegative. -/
theorem mass_nonneg (q T l : ℕ) (x : ZMod (3 ^ (T + q))) : 0 ≤ mass q T l x :=
  ENNReal.toReal_nonneg

/-- The unrestricted tail keeps total probability mass one. -/
theorem mass_sum (q T l : ℕ) : ∑ x, mass q T l x = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe (law q T l))
  rw [tsum_fintype, ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top _ x),
    ENNReal.toReal_one] at h
  exact h

/-- The lower frequency includes the binary unit from the head's valuation total. -/
noncomputable def scaledFrequency {T n : ℕ} (h : T ≤ n) (l : ℕ)
    (ξ : ZMod (3 ^ n)) : ZMod (3 ^ T) :=
  Reference.inverseTwoPow T l * Reference.project h ξ

/-- The actual embedding transports the positive character to its unit-scaled frequency. -/
theorem character_embed (q T l : ℕ) (z : ZMod (3 ^ T)) (ξ : ZMod (3 ^ (T + q))) :
    ZMod.stdAddChar (ξ * embed q T l z) =
      ZMod.stdAddChar (scaledFrequency (Nat.le_add_right T q) l ξ * z) := by
  have he : ξ * embed q T l z =
      ξ * ((3 : ZMod (3 ^ (T + q))) ^ q *
        (Reference.inverseTwoPow (T + q) l * (z.val : ZMod (3 ^ (T + q))))) := by
    simp only [embed, mul_assoc]
  rw [he, FiniteFourier.character_three_pow_mul,
    map_mul (Reference.project (Nat.le_add_right T q)),
    Reference.project_inverseTwoPow, Reference.project_natCast, ZMod.natCast_zmod_val]
  simp only [scaledFrequency]
  congr 1
  ring

/-- The positive Fourier transform of the actual tail is the lower reference transform. -/
theorem fourier_mass (q T l : ℕ) (ξ : ZMod (3 ^ (T + q))) :
    (∑ x, (mass q T l x : ℂ) * ZMod.stdAddChar (ξ * x)) =
      Reference.fourierMass T (scaledFrequency (Nat.le_add_right T q) l ξ) := by
  change (∑ x, (((Reference.law T).map (embed q T l) x).toReal : ℂ) *
    ZMod.stdAddChar (ξ * x)) = _
  rw [FiniteFourier.sum_pmf_map_mul]
  simp only [character_embed, Reference.fourierMass, Reference.mass]

end AffineTail
end WordCertDensity
