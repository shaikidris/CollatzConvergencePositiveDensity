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
theorem levelEleven_energy_168960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 168960 128 =
      25957833537363555750719079967066 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_168960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168960 128 =
      826236567913101766701393 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_168960 : ∀ i : Fin 128,
    levelEleven.lookup (168960 + i.val) ≤ levelElevenRoots.lookup (168960 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_169088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 169088 128 =
      25561099115426435696819039445227 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_169088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169088 128 =
      792162708900378668866415 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_169088 : ∀ i : Fin 128,
    levelEleven.lookup (169088 + i.val) ≤ levelElevenRoots.lookup (169088 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_169216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 169216 128 =
      40941970946954094701913485052940 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_169216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169216 128 =
      1115854199151698423903881 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_169216 : ∀ i : Fin 128,
    levelEleven.lookup (169216 + i.val) ≤ levelElevenRoots.lookup (169216 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_169344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 169344 128 =
      76221416083037639471139628977414 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_169344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169344 128 =
      1362508188417604986644483 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_169344 : ∀ i : Fin 128,
    levelEleven.lookup (169344 + i.val) ≤ levelElevenRoots.lookup (169344 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_330 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 168960 512 =
      168682319682781725620591233442647 := by
  have h0 := levelEleven_energy_168960
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 168960 256 =
      51518932652789991447538119412293 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 168960 128 128
      25957833537363555750719079967066 25561099115426435696819039445227 h0 levelEleven_energy_169088
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 168960 384 =
      92460903599744086149451604465233 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 168960 256 128
      51518932652789991447538119412293 40941970946954094701913485052940 h1 levelEleven_energy_169216
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 168960 512 =
      168682319682781725620591233442647 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 168960 384 128
      92460903599744086149451604465233 76221416083037639471139628977414 h2 levelEleven_energy_169344
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_330 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168960 512 =
      4096761664382783846116172 := by
  have h0 := levelEleven_fractional_168960
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168960 256 =
      1618399276813480435567808 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168960 128 128
      826236567913101766701393 792162708900378668866415 h0 levelEleven_fractional_169088
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168960 384 =
      2734253475965178859471689 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168960 256 128
      1618399276813480435567808 1115854199151698423903881 h1 levelEleven_fractional_169216
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168960 512 =
      4096761664382783846116172 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168960 384 128
      2734253475965178859471689 1362508188417604986644483 h2 levelEleven_fractional_169344
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_330 : ∀ i : Fin 512,
    levelEleven.lookup (168960 + i.val) ≤ levelElevenRoots.lookup (168960 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_168960
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 168960 128 128
    h0 levelEleven_squares_169088
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 168960 256 128
    h1 levelEleven_squares_169216
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 168960 384 128
    h2 levelEleven_squares_169344
  exact h3

end WordCertDensity.Certificates
