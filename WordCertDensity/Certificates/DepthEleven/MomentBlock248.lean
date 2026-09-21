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
theorem levelEleven_energy_126976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 126976 128 =
      58024693146834920965678734126447 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_126976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126976 128 =
      1363219148495872165909489 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_126976 : ∀ i : Fin 128,
    levelEleven.lookup (126976 + i.val) ≤ levelElevenRoots.lookup (126976 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_127104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 127104 128 =
      21296091828170036873921356896959 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_127104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127104 128 =
      749832425315640389195514 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_127104 : ∀ i : Fin 128,
    levelEleven.lookup (127104 + i.val) ≤ levelElevenRoots.lookup (127104 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_127232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 127232 128 =
      226399107592803601134573044324161 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_127232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127232 128 =
      2693742666462551618626245 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_127232 : ∀ i : Fin 128,
    levelEleven.lookup (127232 + i.val) ≤ levelElevenRoots.lookup (127232 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_127360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 127360 128 =
      31165360575128387682390599022800 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_127360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127360 128 =
      893843446521516010422700 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_127360 : ∀ i : Fin 128,
    levelEleven.lookup (127360 + i.val) ≤ levelElevenRoots.lookup (127360 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 126976 512 =
      336885253142936946656563734370367 := by
  have h0 := levelEleven_energy_126976
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 126976 256 =
      79320784975004957839600091023406 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 126976 128 128
      58024693146834920965678734126447 21296091828170036873921356896959 h0 levelEleven_energy_127104
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 126976 384 =
      305719892567808558974173135347567 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 126976 256 128
      79320784975004957839600091023406 226399107592803601134573044324161 h1 levelEleven_energy_127232
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 126976 512 =
      336885253142936946656563734370367 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 126976 384 128
      305719892567808558974173135347567 31165360575128387682390599022800 h2 levelEleven_energy_127360
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126976 512 =
      5700637686795580184153948 := by
  have h0 := levelEleven_fractional_126976
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126976 256 =
      2113051573811512555105003 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126976 128 128
      1363219148495872165909489 749832425315640389195514 h0 levelEleven_fractional_127104
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126976 384 =
      4806794240274064173731248 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126976 256 128
      2113051573811512555105003 2693742666462551618626245 h1 levelEleven_fractional_127232
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126976 512 =
      5700637686795580184153948 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 126976 384 128
      4806794240274064173731248 893843446521516010422700 h2 levelEleven_fractional_127360
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_248 : ∀ i : Fin 512,
    levelEleven.lookup (126976 + i.val) ≤ levelElevenRoots.lookup (126976 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_126976
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 126976 128 128
    h0 levelEleven_squares_127104
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 126976 256 128
    h1 levelEleven_squares_127232
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 126976 384 128
    h2 levelEleven_squares_127360
  exact h3

end WordCertDensity.Certificates
