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
theorem levelEleven_energy_119296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 119296 128 =
      18373217530995191426206359204247 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_119296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119296 128 =
      707057589226015567544291 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_119296 : ∀ i : Fin 128,
    levelEleven.lookup (119296 + i.val) ≤ levelElevenRoots.lookup (119296 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_119424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 119424 128 =
      42335210895275769239767036702662 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_119424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119424 128 =
      1116581805706748194632257 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_119424 : ∀ i : Fin 128,
    levelEleven.lookup (119424 + i.val) ≤ levelElevenRoots.lookup (119424 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_119552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 119552 128 =
      30081571378992729929869324375210 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_119552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119552 128 =
      865962157535339650947291 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_119552 : ∀ i : Fin 128,
    levelEleven.lookup (119552 + i.val) ≤ levelElevenRoots.lookup (119552 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_119680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 119680 128 =
      266577718228505189607845398896416 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_119680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119680 128 =
      3094204947610988862786895 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_119680 : ∀ i : Fin 128,
    levelEleven.lookup (119680 + i.val) ≤ levelElevenRoots.lookup (119680 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_233 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 119296 512 =
      357367718033768880203688119178535 := by
  have h0 := levelEleven_energy_119296
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 119296 256 =
      60708428426270960665973395906909 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 119296 128 128
      18373217530995191426206359204247 42335210895275769239767036702662 h0 levelEleven_energy_119424
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 119296 384 =
      90789999805263690595842720282119 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 119296 256 128
      60708428426270960665973395906909 30081571378992729929869324375210 h1 levelEleven_energy_119552
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 119296 512 =
      357367718033768880203688119178535 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 119296 384 128
      90789999805263690595842720282119 266577718228505189607845398896416 h2 levelEleven_energy_119680
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_233 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119296 512 =
      5783806500079092275910734 := by
  have h0 := levelEleven_fractional_119296
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119296 256 =
      1823639394932763762176548 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119296 128 128
      707057589226015567544291 1116581805706748194632257 h0 levelEleven_fractional_119424
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119296 384 =
      2689601552468103413123839 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119296 256 128
      1823639394932763762176548 865962157535339650947291 h1 levelEleven_fractional_119552
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119296 512 =
      5783806500079092275910734 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 119296 384 128
      2689601552468103413123839 3094204947610988862786895 h2 levelEleven_fractional_119680
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_233 : ∀ i : Fin 512,
    levelEleven.lookup (119296 + i.val) ≤ levelElevenRoots.lookup (119296 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_119296
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 119296 128 128
    h0 levelEleven_squares_119424
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 119296 256 128
    h1 levelEleven_squares_119552
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 119296 384 128
    h2 levelEleven_squares_119680
  exact h3

end WordCertDensity.Certificates
