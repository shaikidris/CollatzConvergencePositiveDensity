/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.MixtureCoefficients
public import WordCertDensity.Transfer.AffineMap

/-! # Independent reversed-word blocks of the reference law -/

@[expose] public section

namespace WordCertDensity.Reference

/-- The last forward block acts by its reversed inverse offset and binary unit. -/
noncomputable def blockMap (u v : ℕ) (w : ValuationWord) (x : ZMod (3 ^ u)) :
    ZMod (3 ^ (u + v)) :=
  ValuationWord.residueOffset (u + v) w.reverse +
    (3 : ZMod (3 ^ (u + v))) ^ v * inverseTwoPow (u + v) w.total * x.val

/-- Independent prefix reversal preserves the complete concatenated iid word law. -/
theorem wordPMF_reverse_prefix (u v : ℕ) :
    wordPMF (u + v) = (wordPMF v).bind
      (fun w => (wordPMF u).map (fun t => w.reverse ++ t)) := by
  calc
    _ = (wordPMF v).bind (fun w => (wordPMF u).map (fun t => w ++ t)) := by
      rw [wordPMF_append, Nat.add_comm]
    _ = ((wordPMF v).map List.reverse).bind
        (fun w => (wordPMF u).map (fun t => w ++ t)) := by rw [wordPMF_map_reverse]
    _ = _ := by rw [PMF.bind_map]; rfl


end WordCertDensity.Reference
