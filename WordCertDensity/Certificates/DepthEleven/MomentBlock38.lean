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
theorem levelEleven_energy_19456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 19456 128 =
      31394505497060257176886900504571 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_19456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19456 128 =
      880652069094869869438113 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_19456 : ∀ i : Fin 128,
    levelEleven.lookup (19456 + i.val) ≤ levelElevenRoots.lookup (19456 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_19584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 19584 128 =
      153776166612366545877565392804266 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_19584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19584 128 =
      2242713917566474315179824 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_19584 : ∀ i : Fin 128,
    levelEleven.lookup (19584 + i.val) ≤ levelElevenRoots.lookup (19584 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_19712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 19712 128 =
      34274854901231578611906776434298 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_19712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19712 128 =
      939250421644807077188146 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_19712 : ∀ i : Fin 128,
    levelEleven.lookup (19712 + i.val) ≤ levelElevenRoots.lookup (19712 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_19840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 19840 128 =
      43452281114439262234816969442676 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_19840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19840 128 =
      1166465529262137030198287 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_19840 : ∀ i : Fin 128,
    levelEleven.lookup (19840 + i.val) ≤ levelElevenRoots.lookup (19840 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_38 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 19456 512 =
      262897808125097643901176039185811 := by
  have h0 := levelEleven_energy_19456
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 19456 256 =
      185170672109426803054452293308837 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 19456 128 128
      31394505497060257176886900504571 153776166612366545877565392804266 h0 levelEleven_energy_19584
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 19456 384 =
      219445527010658381666359069743135 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 19456 256 128
      185170672109426803054452293308837 34274854901231578611906776434298 h1 levelEleven_energy_19712
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 19456 512 =
      262897808125097643901176039185811 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 19456 384 128
      219445527010658381666359069743135 43452281114439262234816969442676 h2 levelEleven_energy_19840
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_38 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19456 512 =
      5229081937568288292004370 := by
  have h0 := levelEleven_fractional_19456
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19456 256 =
      3123365986661344184617937 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19456 128 128
      880652069094869869438113 2242713917566474315179824 h0 levelEleven_fractional_19584
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19456 384 =
      4062616408306151261806083 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19456 256 128
      3123365986661344184617937 939250421644807077188146 h1 levelEleven_fractional_19712
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19456 512 =
      5229081937568288292004370 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19456 384 128
      4062616408306151261806083 1166465529262137030198287 h2 levelEleven_fractional_19840
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_38 : ∀ i : Fin 512,
    levelEleven.lookup (19456 + i.val) ≤ levelElevenRoots.lookup (19456 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_19456
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 19456 128 128
    h0 levelEleven_squares_19584
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 19456 256 128
    h1 levelEleven_squares_19712
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 19456 384 128
    h2 levelEleven_squares_19840
  exact h3

end WordCertDensity.Certificates
