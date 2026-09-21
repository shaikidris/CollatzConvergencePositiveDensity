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
theorem levelEleven_energy_70144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 70144 128 =
      62758659186697893733540710093637 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_70144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70144 128 =
      1406806581113558147300796 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_70144 : ∀ i : Fin 128,
    levelEleven.lookup (70144 + i.val) ≤ levelElevenRoots.lookup (70144 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_70272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 70272 128 =
      26704254068179741075042648512924 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_70272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70272 128 =
      857162523587203463168294 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_70272 : ∀ i : Fin 128,
    levelEleven.lookup (70272 + i.val) ≤ levelElevenRoots.lookup (70272 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_70400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 70400 128 =
      49960408540308965159623849048347 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_70400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70400 128 =
      1181723624012197703345448 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_70400 : ∀ i : Fin 128,
    levelEleven.lookup (70400 + i.val) ≤ levelElevenRoots.lookup (70400 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_70528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 70528 128 =
      30208853921392057813533078565687 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_70528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70528 128 =
      902403611661627862338081 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_70528 : ∀ i : Fin 128,
    levelEleven.lookup (70528 + i.val) ≤ levelElevenRoots.lookup (70528 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_137 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 70144 512 =
      169632175716578657781740286220595 := by
  have h0 := levelEleven_energy_70144
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 70144 256 =
      89462913254877634808583358606561 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 70144 128 128
      62758659186697893733540710093637 26704254068179741075042648512924 h0 levelEleven_energy_70272
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 70144 384 =
      139423321795186599968207207654908 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 70144 256 128
      89462913254877634808583358606561 49960408540308965159623849048347 h1 levelEleven_energy_70400
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 70144 512 =
      169632175716578657781740286220595 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 70144 384 128
      139423321795186599968207207654908 30208853921392057813533078565687 h2 levelEleven_energy_70528
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_137 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70144 512 =
      4348096340374587176152619 := by
  have h0 := levelEleven_fractional_70144
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70144 256 =
      2263969104700761610469090 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70144 128 128
      1406806581113558147300796 857162523587203463168294 h0 levelEleven_fractional_70272
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70144 384 =
      3445692728712959313814538 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70144 256 128
      2263969104700761610469090 1181723624012197703345448 h1 levelEleven_fractional_70400
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70144 512 =
      4348096340374587176152619 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70144 384 128
      3445692728712959313814538 902403611661627862338081 h2 levelEleven_fractional_70528
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_137 : ∀ i : Fin 512,
    levelEleven.lookup (70144 + i.val) ≤ levelElevenRoots.lookup (70144 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_70144
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 70144 128 128
    h0 levelEleven_squares_70272
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 70144 256 128
    h1 levelEleven_squares_70400
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 70144 384 128
    h2 levelEleven_squares_70528
  exact h3

end WordCertDensity.Certificates
