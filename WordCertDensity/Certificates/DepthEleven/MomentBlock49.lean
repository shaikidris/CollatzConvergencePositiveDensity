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
theorem levelEleven_energy_25088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 25088 128 =
      33341688286904935368875062311807 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_25088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25088 128 =
      1006596702360666201619481 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_25088 : ∀ i : Fin 128,
    levelEleven.lookup (25088 + i.val) ≤ levelElevenRoots.lookup (25088 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_25216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 25216 128 =
      23275287714823638181589225715998 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_25216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25216 128 =
      770084676790630270116590 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_25216 : ∀ i : Fin 128,
    levelEleven.lookup (25216 + i.val) ≤ levelElevenRoots.lookup (25216 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_25344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 25344 128 =
      53555940737252479474893892312602 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_25344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25344 128 =
      1221853828736110660063447 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_25344 : ∀ i : Fin 128,
    levelEleven.lookup (25344 + i.val) ≤ levelElevenRoots.lookup (25344 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_25472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 25472 128 =
      29025135300899547762080563120158 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_25472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25472 128 =
      846985673531281731825291 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_25472 : ∀ i : Fin 128,
    levelEleven.lookup (25472 + i.val) ≤ levelElevenRoots.lookup (25472 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_49 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 25088 512 =
      139198052039880600787438743460565 := by
  have h0 := levelEleven_energy_25088
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 25088 256 =
      56616976001728573550464288027805 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 25088 128 128
      33341688286904935368875062311807 23275287714823638181589225715998 h0 levelEleven_energy_25216
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 25088 384 =
      110172916738981053025358180340407 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 25088 256 128
      56616976001728573550464288027805 53555940737252479474893892312602 h1 levelEleven_energy_25344
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 25088 512 =
      139198052039880600787438743460565 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 25088 384 128
      110172916738981053025358180340407 29025135300899547762080563120158 h2 levelEleven_energy_25472
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_49 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25088 512 =
      3845520881418688863624809 := by
  have h0 := levelEleven_fractional_25088
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25088 256 =
      1776681379151296471736071 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25088 128 128
      1006596702360666201619481 770084676790630270116590 h0 levelEleven_fractional_25216
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25088 384 =
      2998535207887407131799518 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25088 256 128
      1776681379151296471736071 1221853828736110660063447 h1 levelEleven_fractional_25344
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25088 512 =
      3845520881418688863624809 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 25088 384 128
      2998535207887407131799518 846985673531281731825291 h2 levelEleven_fractional_25472
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_49 : ∀ i : Fin 512,
    levelEleven.lookup (25088 + i.val) ≤ levelElevenRoots.lookup (25088 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_25088
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 25088 128 128
    h0 levelEleven_squares_25216
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 25088 256 128
    h1 levelEleven_squares_25344
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 25088 384 128
    h2 levelEleven_squares_25472
  exact h3

end WordCertDensity.Certificates
