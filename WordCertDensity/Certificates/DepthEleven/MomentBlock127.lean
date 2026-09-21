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
theorem levelEleven_energy_65024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 65024 128 =
      55466854018509216464900180968527 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_65024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65024 128 =
      1342719891159642814236813 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_65024 : ∀ i : Fin 128,
    levelEleven.lookup (65024 + i.val) ≤ levelElevenRoots.lookup (65024 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_65152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 65152 128 =
      42868562289494263798106257875894 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_65152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65152 128 =
      1035529173610612724746433 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_65152 : ∀ i : Fin 128,
    levelEleven.lookup (65152 + i.val) ≤ levelElevenRoots.lookup (65152 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_65280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 65280 128 =
      26236634595990607233341013058964 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_65280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65280 128 =
      864662698423230097261528 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_65280 : ∀ i : Fin 128,
    levelEleven.lookup (65280 + i.val) ≤ levelElevenRoots.lookup (65280 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_65408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 65408 128 =
      55019455245271251687181386836654 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_65408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65408 128 =
      1286646558631803983361485 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_65408 : ∀ i : Fin 128,
    levelEleven.lookup (65408 + i.val) ≤ levelElevenRoots.lookup (65408 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_127 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 65024 512 =
      179591506149265339183528838740039 := by
  have h0 := levelEleven_energy_65024
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 65024 256 =
      98335416308003480263006438844421 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 65024 128 128
      55466854018509216464900180968527 42868562289494263798106257875894 h0 levelEleven_energy_65152
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 65024 384 =
      124572050903994087496347451903385 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 65024 256 128
      98335416308003480263006438844421 26236634595990607233341013058964 h1 levelEleven_energy_65280
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 65024 512 =
      179591506149265339183528838740039 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 65024 384 128
      124572050903994087496347451903385 55019455245271251687181386836654 h2 levelEleven_energy_65408
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_127 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65024 512 =
      4529558321825289619606259 := by
  have h0 := levelEleven_fractional_65024
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65024 256 =
      2378249064770255538983246 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65024 128 128
      1342719891159642814236813 1035529173610612724746433 h0 levelEleven_fractional_65152
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65024 384 =
      3242911763193485636244774 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65024 256 128
      2378249064770255538983246 864662698423230097261528 h1 levelEleven_fractional_65280
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65024 512 =
      4529558321825289619606259 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 65024 384 128
      3242911763193485636244774 1286646558631803983361485 h2 levelEleven_fractional_65408
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_127 : ∀ i : Fin 512,
    levelEleven.lookup (65024 + i.val) ≤ levelElevenRoots.lookup (65024 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_65024
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 65024 128 128
    h0 levelEleven_squares_65152
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 65024 256 128
    h1 levelEleven_squares_65280
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 65024 384 128
    h2 levelEleven_squares_65408
  exact h3

end WordCertDensity.Certificates
