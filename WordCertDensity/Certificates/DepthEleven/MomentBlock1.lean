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
theorem levelEleven_energy_512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 512 128 =
      58486971934704416731891241532592 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 512 128 =
      1259258143162359043391098 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_512 : ∀ i : Fin 128,
    levelEleven.lookup (512 + i.val) ≤ levelElevenRoots.lookup (512 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 640 128 =
      59256130734085112726863485129376 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 640 128 =
      1354097425596531282781697 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_640 : ∀ i : Fin 128,
    levelEleven.lookup (640 + i.val) ≤ levelElevenRoots.lookup (640 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 768 128 =
      66445272802225971095178438599414 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 768 128 =
      1334059831263700026459915 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_768 : ∀ i : Fin 128,
    levelEleven.lookup (768 + i.val) ≤ levelElevenRoots.lookup (768 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 896 128 =
      40310201044723636285830986776119 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 896 128 =
      1038179713250656279290696 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_896 : ∀ i : Fin 128,
    levelEleven.lookup (896 + i.val) ≤ levelElevenRoots.lookup (896 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_1 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 512 512 =
      224498576515739136839764152037501 := by
  have h0 := levelEleven_energy_512
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 512 256 =
      117743102668789529458754726661968 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 512 128 128
      58486971934704416731891241532592 59256130734085112726863485129376 h0 levelEleven_energy_640
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 512 384 =
      184188375471015500553933165261382 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 512 256 128
      117743102668789529458754726661968 66445272802225971095178438599414 h1 levelEleven_energy_768
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 512 512 =
      224498576515739136839764152037501 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 512 384 128
      184188375471015500553933165261382 40310201044723636285830986776119 h2 levelEleven_energy_896
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_1 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 512 512 =
      4985595113273246631923406 := by
  have h0 := levelEleven_fractional_512
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 512 256 =
      2613355568758890326172795 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 512 128 128
      1259258143162359043391098 1354097425596531282781697 h0 levelEleven_fractional_640
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 512 384 =
      3947415400022590352632710 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 512 256 128
      2613355568758890326172795 1334059831263700026459915 h1 levelEleven_fractional_768
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 512 512 =
      4985595113273246631923406 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 512 384 128
      3947415400022590352632710 1038179713250656279290696 h2 levelEleven_fractional_896
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_1 : ∀ i : Fin 512,
    levelEleven.lookup (512 + i.val) ≤ levelElevenRoots.lookup (512 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_512
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 512 128 128
    h0 levelEleven_squares_640
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 512 256 128
    h1 levelEleven_squares_768
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 512 384 128
    h2 levelEleven_squares_896
  exact h3

end WordCertDensity.Certificates
