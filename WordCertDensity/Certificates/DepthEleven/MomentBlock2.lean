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
theorem levelEleven_energy_1024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 1024 128 =
      31104403691688530135015435521615 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_1024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1024 128 =
      901863902553150446301581 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_1024 : ∀ i : Fin 128,
    levelEleven.lookup (1024 + i.val) ≤ levelElevenRoots.lookup (1024 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_1152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 1152 128 =
      28636534710569288160988704607363 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_1152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1152 128 =
      842409821033422530278658 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_1152 : ∀ i : Fin 128,
    levelEleven.lookup (1152 + i.val) ≤ levelElevenRoots.lookup (1152 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_1280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 1280 128 =
      61042600141906376150335982141829 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_1280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1280 128 =
      1399358559981079910734375 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_1280 : ∀ i : Fin 128,
    levelEleven.lookup (1280 + i.val) ≤ levelElevenRoots.lookup (1280 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_1408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 1408 128 =
      18426884202293174307351680819552 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_1408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1408 128 =
      639822875892798625829282 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_1408 : ∀ i : Fin 128,
    levelEleven.lookup (1408 + i.val) ≤ levelElevenRoots.lookup (1408 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_2 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 1024 512 =
      139210422746457368753691803090359 := by
  have h0 := levelEleven_energy_1024
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 1024 256 =
      59740938402257818296004140128978 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 1024 128 128
      31104403691688530135015435521615 28636534710569288160988704607363 h0 levelEleven_energy_1152
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 1024 384 =
      120783538544164194446340122270807 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 1024 256 128
      59740938402257818296004140128978 61042600141906376150335982141829 h1 levelEleven_energy_1280
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 1024 512 =
      139210422746457368753691803090359 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 1024 384 128
      120783538544164194446340122270807 18426884202293174307351680819552 h2 levelEleven_energy_1408
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_2 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1024 512 =
      3783455159460451513143896 := by
  have h0 := levelEleven_fractional_1024
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1024 256 =
      1744273723586572976580239 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1024 128 128
      901863902553150446301581 842409821033422530278658 h0 levelEleven_fractional_1152
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1024 384 =
      3143632283567652887314614 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1024 256 128
      1744273723586572976580239 1399358559981079910734375 h1 levelEleven_fractional_1280
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1024 512 =
      3783455159460451513143896 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 1024 384 128
      3143632283567652887314614 639822875892798625829282 h2 levelEleven_fractional_1408
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_2 : ∀ i : Fin 512,
    levelEleven.lookup (1024 + i.val) ≤ levelElevenRoots.lookup (1024 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_1024
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 1024 128 128
    h0 levelEleven_squares_1152
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 1024 256 128
    h1 levelEleven_squares_1280
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 1024 384 128
    h2 levelEleven_squares_1408
  exact h3

end WordCertDensity.Certificates
