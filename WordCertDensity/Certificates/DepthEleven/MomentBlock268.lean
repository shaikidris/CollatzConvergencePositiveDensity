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
theorem levelEleven_energy_137216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 137216 128 =
      41207136722221061353659968626373 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_137216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137216 128 =
      1042363087913875299835728 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_137216 : ∀ i : Fin 128,
    levelEleven.lookup (137216 + i.val) ≤ levelElevenRoots.lookup (137216 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_137344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 137344 128 =
      34359447000998311431291834035999 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_137344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137344 128 =
      960364648152772504948451 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_137344 : ∀ i : Fin 128,
    levelEleven.lookup (137344 + i.val) ≤ levelElevenRoots.lookup (137344 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_137472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 137472 128 =
      39520868722009035078059221769868 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_137472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137472 128 =
      1031714537703309561905602 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_137472 : ∀ i : Fin 128,
    levelEleven.lookup (137472 + i.val) ≤ levelElevenRoots.lookup (137472 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_137600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 137600 128 =
      65121250240991662113584204927944 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_137600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137600 128 =
      1461091881080622532228901 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_137600 : ∀ i : Fin 128,
    levelEleven.lookup (137600 + i.val) ≤ levelElevenRoots.lookup (137600 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_268 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 137216 512 =
      180208702686220069976595229360184 := by
  have h0 := levelEleven_energy_137216
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 137216 256 =
      75566583723219372784951802662372 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 137216 128 128
      41207136722221061353659968626373 34359447000998311431291834035999 h0 levelEleven_energy_137344
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 137216 384 =
      115087452445228407863011024432240 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 137216 256 128
      75566583723219372784951802662372 39520868722009035078059221769868 h1 levelEleven_energy_137472
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 137216 512 =
      180208702686220069976595229360184 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 137216 384 128
      115087452445228407863011024432240 65121250240991662113584204927944 h2 levelEleven_energy_137600
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_268 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137216 512 =
      4495534154850579898918682 := by
  have h0 := levelEleven_fractional_137216
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137216 256 =
      2002727736066647804784179 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137216 128 128
      1042363087913875299835728 960364648152772504948451 h0 levelEleven_fractional_137344
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137216 384 =
      3034442273769957366689781 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137216 256 128
      2002727736066647804784179 1031714537703309561905602 h1 levelEleven_fractional_137472
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137216 512 =
      4495534154850579898918682 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137216 384 128
      3034442273769957366689781 1461091881080622532228901 h2 levelEleven_fractional_137600
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_268 : ∀ i : Fin 512,
    levelEleven.lookup (137216 + i.val) ≤ levelElevenRoots.lookup (137216 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_137216
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 137216 128 128
    h0 levelEleven_squares_137344
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 137216 256 128
    h1 levelEleven_squares_137472
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 137216 384 128
    h2 levelEleven_squares_137600
  exact h3

end WordCertDensity.Certificates
