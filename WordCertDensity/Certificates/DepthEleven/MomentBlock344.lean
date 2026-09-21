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
theorem levelEleven_energy_176128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 176128 128 =
      16673676413831580584272422427123 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_176128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176128 128 =
      636052082060863598240693 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_176128 : ∀ i : Fin 128,
    levelEleven.lookup (176128 + i.val) ≤ levelElevenRoots.lookup (176128 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_176256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 176256 128 =
      47289619842069209084500900536245 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_176256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176256 128 =
      1162437857842191956056304 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_176256 : ∀ i : Fin 128,
    levelEleven.lookup (176256 + i.val) ≤ levelElevenRoots.lookup (176256 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_176384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 176384 128 =
      23227202273172123856344518527769 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_176384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176384 128 =
      755398158087820344611420 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_176384 : ∀ i : Fin 128,
    levelEleven.lookup (176384 + i.val) ≤ levelElevenRoots.lookup (176384 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_176512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 176512 128 =
      32172150579388171835901094872978 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_176512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176512 128 =
      1002572080446127533826338 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_176512 : ∀ i : Fin 128,
    levelEleven.lookup (176512 + i.val) ≤ levelElevenRoots.lookup (176512 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 176128 512 =
      119362649108461085361018936364115 := by
  have h0 := levelEleven_energy_176128
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 176128 256 =
      63963296255900789668773322963368 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 176128 128 128
      16673676413831580584272422427123 47289619842069209084500900536245 h0 levelEleven_energy_176256
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 176128 384 =
      87190498529072913525117841491137 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 176128 256 128
      63963296255900789668773322963368 23227202273172123856344518527769 h1 levelEleven_energy_176384
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 176128 512 =
      119362649108461085361018936364115 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 176128 384 128
      87190498529072913525117841491137 32172150579388171835901094872978 h2 levelEleven_energy_176512
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176128 512 =
      3556460178437003432734755 := by
  have h0 := levelEleven_fractional_176128
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176128 256 =
      1798489939903055554296997 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176128 128 128
      636052082060863598240693 1162437857842191956056304 h0 levelEleven_fractional_176256
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176128 384 =
      2553888097990875898908417 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176128 256 128
      1798489939903055554296997 755398158087820344611420 h1 levelEleven_fractional_176384
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176128 512 =
      3556460178437003432734755 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176128 384 128
      2553888097990875898908417 1002572080446127533826338 h2 levelEleven_fractional_176512
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_344 : ∀ i : Fin 512,
    levelEleven.lookup (176128 + i.val) ≤ levelElevenRoots.lookup (176128 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_176128
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 176128 128 128
    h0 levelEleven_squares_176256
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 176128 256 128
    h1 levelEleven_squares_176384
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 176128 384 128
    h2 levelEleven_squares_176512
  exact h3

end WordCertDensity.Certificates
