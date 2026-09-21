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
theorem levelEleven_energy_174592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 174592 128 =
      53072516422266555438438949375036 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_174592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174592 128 =
      1328527004821588829926486 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_174592 : ∀ i : Fin 128,
    levelEleven.lookup (174592 + i.val) ≤ levelElevenRoots.lookup (174592 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_174720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 174720 128 =
      44266844109529372032161300303908 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_174720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174720 128 =
      1133053638997254568304729 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_174720 : ∀ i : Fin 128,
    levelEleven.lookup (174720 + i.val) ≤ levelElevenRoots.lookup (174720 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_174848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 174848 128 =
      41461415826404655501783388782948 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_174848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174848 128 =
      1105646647977877097780271 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_174848 : ∀ i : Fin 128,
    levelEleven.lookup (174848 + i.val) ≤ levelElevenRoots.lookup (174848 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_174976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 174976 128 =
      29767369602814972841011080064089 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_174976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174976 128 =
      870448718847077075322600 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_174976 : ∀ i : Fin 128,
    levelEleven.lookup (174976 + i.val) ≤ levelElevenRoots.lookup (174976 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_341 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 174592 512 =
      168568145961015555813394718525981 := by
  have h0 := levelEleven_energy_174592
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 174592 256 =
      97339360531795927470600249678944 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 174592 128 128
      53072516422266555438438949375036 44266844109529372032161300303908 h0 levelEleven_energy_174720
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 174592 384 =
      138800776358200582972383638461892 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 174592 256 128
      97339360531795927470600249678944 41461415826404655501783388782948 h1 levelEleven_energy_174848
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 174592 512 =
      168568145961015555813394718525981 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 174592 384 128
      138800776358200582972383638461892 29767369602814972841011080064089 h2 levelEleven_energy_174976
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_341 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174592 512 =
      4437676010643797571334086 := by
  have h0 := levelEleven_fractional_174592
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174592 256 =
      2461580643818843398231215 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174592 128 128
      1328527004821588829926486 1133053638997254568304729 h0 levelEleven_fractional_174720
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174592 384 =
      3567227291796720496011486 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174592 256 128
      2461580643818843398231215 1105646647977877097780271 h1 levelEleven_fractional_174848
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174592 512 =
      4437676010643797571334086 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 174592 384 128
      3567227291796720496011486 870448718847077075322600 h2 levelEleven_fractional_174976
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_341 : ∀ i : Fin 512,
    levelEleven.lookup (174592 + i.val) ≤ levelElevenRoots.lookup (174592 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_174592
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 174592 128 128
    h0 levelEleven_squares_174720
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 174592 256 128
    h1 levelEleven_squares_174848
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 174592 384 128
    h2 levelEleven_squares_174976
  exact h3

end WordCertDensity.Certificates
