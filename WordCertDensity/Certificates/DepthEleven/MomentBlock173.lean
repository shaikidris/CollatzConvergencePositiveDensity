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
theorem levelEleven_energy_88576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 88576 128 =
      27619729835169378318637874846014 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_88576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88576 128 =
      862768277482989906114043 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_88576 : ∀ i : Fin 128,
    levelEleven.lookup (88576 + i.val) ≤ levelElevenRoots.lookup (88576 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_88704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 88704 128 =
      30911233229936708895448414973302 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_88704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88704 128 =
      964556234702234562735398 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_88704 : ∀ i : Fin 128,
    levelEleven.lookup (88704 + i.val) ≤ levelElevenRoots.lookup (88704 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_88832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 88832 128 =
      119770371784520719997267084271186 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_88832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88832 128 =
      1994498265200888699784499 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_88832 : ∀ i : Fin 128,
    levelEleven.lookup (88832 + i.val) ≤ levelElevenRoots.lookup (88832 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_88960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 88960 128 =
      35568281567015302758233019490348 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_88960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88960 128 =
      891003362707833790929130 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_88960 : ∀ i : Fin 128,
    levelEleven.lookup (88960 + i.val) ≤ levelElevenRoots.lookup (88960 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_173 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 88576 512 =
      213869616416642109969586393580850 := by
  have h0 := levelEleven_energy_88576
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 88576 256 =
      58530963065106087214086289819316 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 88576 128 128
      27619729835169378318637874846014 30911233229936708895448414973302 h0 levelEleven_energy_88704
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 88576 384 =
      178301334849626807211353374090502 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 88576 256 128
      58530963065106087214086289819316 119770371784520719997267084271186 h1 levelEleven_energy_88832
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 88576 512 =
      213869616416642109969586393580850 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 88576 384 128
      178301334849626807211353374090502 35568281567015302758233019490348 h2 levelEleven_energy_88960
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_173 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88576 512 =
      4712826140093946959563070 := by
  have h0 := levelEleven_fractional_88576
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88576 256 =
      1827324512185224468849441 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88576 128 128
      862768277482989906114043 964556234702234562735398 h0 levelEleven_fractional_88704
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88576 384 =
      3821822777386113168633940 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88576 256 128
      1827324512185224468849441 1994498265200888699784499 h1 levelEleven_fractional_88832
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88576 512 =
      4712826140093946959563070 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 88576 384 128
      3821822777386113168633940 891003362707833790929130 h2 levelEleven_fractional_88960
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_173 : ∀ i : Fin 512,
    levelEleven.lookup (88576 + i.val) ≤ levelElevenRoots.lookup (88576 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_88576
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 88576 128 128
    h0 levelEleven_squares_88704
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 88576 256 128
    h1 levelEleven_squares_88832
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 88576 384 128
    h2 levelEleven_squares_88960
  exact h3

end WordCertDensity.Certificates
