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
theorem levelEleven_energy_142848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 142848 128 =
      19351272181482434811491370416343 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_142848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142848 128 =
      700110226339258147284239 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_142848 : ∀ i : Fin 128,
    levelEleven.lookup (142848 + i.val) ≤ levelElevenRoots.lookup (142848 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_142976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 142976 128 =
      40312397454184504076804028384173 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_142976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142976 128 =
      1142545272466894246846977 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_142976 : ∀ i : Fin 128,
    levelEleven.lookup (142976 + i.val) ≤ levelElevenRoots.lookup (142976 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_143104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 143104 128 =
      38080849320209719206204304173718 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_143104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143104 128 =
      1049905111319178515197534 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_143104 : ∀ i : Fin 128,
    levelEleven.lookup (143104 + i.val) ≤ levelElevenRoots.lookup (143104 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_143232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 143232 128 =
      36416274996030014807042742670526 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_143232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143232 128 =
      1043785297152611042799916 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_143232 : ∀ i : Fin 128,
    levelEleven.lookup (143232 + i.val) ≤ levelElevenRoots.lookup (143232 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_279 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 142848 512 =
      134160793951906672901542445644760 := by
  have h0 := levelEleven_energy_142848
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 142848 256 =
      59663669635666938888295398800516 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 142848 128 128
      19351272181482434811491370416343 40312397454184504076804028384173 h0 levelEleven_energy_142976
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 142848 384 =
      97744518955876658094499702974234 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 142848 256 128
      59663669635666938888295398800516 38080849320209719206204304173718 h1 levelEleven_energy_143104
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 142848 512 =
      134160793951906672901542445644760 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 142848 384 128
      97744518955876658094499702974234 36416274996030014807042742670526 h2 levelEleven_energy_143232
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_279 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142848 512 =
      3936345907277941952128666 := by
  have h0 := levelEleven_fractional_142848
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142848 256 =
      1842655498806152394131216 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142848 128 128
      700110226339258147284239 1142545272466894246846977 h0 levelEleven_fractional_142976
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142848 384 =
      2892560610125330909328750 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142848 256 128
      1842655498806152394131216 1049905111319178515197534 h1 levelEleven_fractional_143104
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142848 512 =
      3936345907277941952128666 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 142848 384 128
      2892560610125330909328750 1043785297152611042799916 h2 levelEleven_fractional_143232
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_279 : ∀ i : Fin 512,
    levelEleven.lookup (142848 + i.val) ≤ levelElevenRoots.lookup (142848 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_142848
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 142848 128 128
    h0 levelEleven_squares_142976
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 142848 256 128
    h1 levelEleven_squares_143104
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 142848 384 128
    h2 levelEleven_squares_143232
  exact h3

end WordCertDensity.Certificates
