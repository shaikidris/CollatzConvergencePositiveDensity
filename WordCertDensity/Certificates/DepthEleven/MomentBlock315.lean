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
theorem levelEleven_energy_161280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 161280 128 =
      57105788799350647689796801462166 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_161280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161280 128 =
      1260101712947008877119998 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_161280 : ∀ i : Fin 128,
    levelEleven.lookup (161280 + i.val) ≤ levelElevenRoots.lookup (161280 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_161408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 161408 128 =
      37520952499876486149654663965869 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_161408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161408 128 =
      1056845060600226163406991 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_161408 : ∀ i : Fin 128,
    levelEleven.lookup (161408 + i.val) ≤ levelElevenRoots.lookup (161408 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_161536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 161536 128 =
      16819567378757598842575024553955 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_161536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161536 128 =
      632313544322841551763610 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_161536 : ∀ i : Fin 128,
    levelEleven.lookup (161536 + i.val) ≤ levelElevenRoots.lookup (161536 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_161664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 161664 128 =
      118549085125121433160957717065177 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_161664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161664 128 =
      2060345708154346364736110 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_161664 : ∀ i : Fin 128,
    levelEleven.lookup (161664 + i.val) ≤ levelElevenRoots.lookup (161664 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_315 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 161280 512 =
      229995393803106165842984207047167 := by
  have h0 := levelEleven_energy_161280
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 161280 256 =
      94626741299227133839451465428035 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 161280 128 128
      57105788799350647689796801462166 37520952499876486149654663965869 h0 levelEleven_energy_161408
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 161280 384 =
      111446308677984732682026489981990 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 161280 256 128
      94626741299227133839451465428035 16819567378757598842575024553955 h1 levelEleven_energy_161536
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 161280 512 =
      229995393803106165842984207047167 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 161280 384 128
      111446308677984732682026489981990 118549085125121433160957717065177 h2 levelEleven_energy_161664
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_315 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161280 512 =
      5009606026024422957026709 := by
  have h0 := levelEleven_fractional_161280
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161280 256 =
      2316946773547235040526989 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161280 128 128
      1260101712947008877119998 1056845060600226163406991 h0 levelEleven_fractional_161408
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161280 384 =
      2949260317870076592290599 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161280 256 128
      2316946773547235040526989 632313544322841551763610 h1 levelEleven_fractional_161536
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161280 512 =
      5009606026024422957026709 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161280 384 128
      2949260317870076592290599 2060345708154346364736110 h2 levelEleven_fractional_161664
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_315 : ∀ i : Fin 512,
    levelEleven.lookup (161280 + i.val) ≤ levelElevenRoots.lookup (161280 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_161280
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 161280 128 128
    h0 levelEleven_squares_161408
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 161280 256 128
    h1 levelEleven_squares_161536
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 161280 384 128
    h2 levelEleven_squares_161664
  exact h3

end WordCertDensity.Certificates
