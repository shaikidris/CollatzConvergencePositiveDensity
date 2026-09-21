/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.LevelElevenRoots

/-! # Bounded depth-eleven moment certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_60928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 60928 128 =
      34969009795946791379106842237429 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_60928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60928 128 =
      935591644938308796223501 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_60928 : ∀ i : Fin 128,
    levelEleven.lookup (60928 + i.val) ≤ levelElevenRoots.lookup (60928 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_61056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 61056 128 =
      57442134097868895116994644246695 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_61056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61056 128 =
      1340594977971758261210012 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_61056 : ∀ i : Fin 128,
    levelEleven.lookup (61056 + i.val) ≤ levelElevenRoots.lookup (61056 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_61184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 61184 128 =
      51653953809721659373592386605054 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_61184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61184 128 =
      1146834938624579482490140 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_61184 : ∀ i : Fin 128,
    levelEleven.lookup (61184 + i.val) ≤ levelElevenRoots.lookup (61184 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_61312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 61312 128 =
      160152087932850457245108141336195 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_61312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61312 128 =
      2378572220780208202851761 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_61312 : ∀ i : Fin 128,
    levelEleven.lookup (61312 + i.val) ≤ levelElevenRoots.lookup (61312 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_119 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 60928 512 =
      304217185636387803114802014425373 := by
  have h0 := levelEleven_energy_60928
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 60928 256 =
      92411143893815686496101486484124 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 60928 128 128
      34969009795946791379106842237429 57442134097868895116994644246695 h0 levelEleven_energy_61056
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 60928 384 =
      144065097703537345869693873089178 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 60928 256 128
      92411143893815686496101486484124 51653953809721659373592386605054 h1 levelEleven_energy_61184
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 60928 512 =
      304217185636387803114802014425373 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 60928 384 128
      144065097703537345869693873089178 160152087932850457245108141336195 h2 levelEleven_energy_61312
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_119 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60928 512 =
      5801593782314854742775414 := by
  have h0 := levelEleven_fractional_60928
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60928 256 =
      2276186622910067057433513 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60928 128 128
      935591644938308796223501 1340594977971758261210012 h0 levelEleven_fractional_61056
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60928 384 =
      3423021561534646539923653 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60928 256 128
      2276186622910067057433513 1146834938624579482490140 h1 levelEleven_fractional_61184
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60928 512 =
      5801593782314854742775414 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60928 384 128
      3423021561534646539923653 2378572220780208202851761 h2 levelEleven_fractional_61312
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_119 : ∀ i : Fin 512,
    levelEleven.lookup (60928 + i.val) ≤ levelElevenRoots.lookup (60928 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_60928
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 60928 128 128
    h0 levelEleven_squares_61056
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 60928 256 128
    h1 levelEleven_squares_61184
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 60928 384 128
    h2 levelEleven_squares_61312
  exact h3

end WordCertDensity.Certificates
