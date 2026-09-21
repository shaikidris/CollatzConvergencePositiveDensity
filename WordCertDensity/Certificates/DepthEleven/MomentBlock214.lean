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
theorem levelEleven_energy_109568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 109568 128 =
      40575349163117998753884718168153 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_109568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109568 128 =
      1063179951923347394434328 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_109568 : ∀ i : Fin 128,
    levelEleven.lookup (109568 + i.val) ≤ levelElevenRoots.lookup (109568 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_109696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 109696 128 =
      93114433677746043872225084072871 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_109696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109696 128 =
      1665113061140362042347541 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_109696 : ∀ i : Fin 128,
    levelEleven.lookup (109696 + i.val) ≤ levelElevenRoots.lookup (109696 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_109824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 109824 128 =
      39179356687691693838678785354800 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_109824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109824 128 =
      1027199862202630796224400 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_109824 : ∀ i : Fin 128,
    levelEleven.lookup (109824 + i.val) ≤ levelElevenRoots.lookup (109824 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_109952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 109952 128 =
      34481046306697446494256123442649 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_109952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109952 128 =
      1008298368412732972102203 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_109952 : ∀ i : Fin 128,
    levelEleven.lookup (109952 + i.val) ≤ levelElevenRoots.lookup (109952 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_214 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 109568 512 =
      207350185835253182959044711038473 := by
  have h0 := levelEleven_energy_109568
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 109568 256 =
      133689782840864042626109802241024 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 109568 128 128
      40575349163117998753884718168153 93114433677746043872225084072871 h0 levelEleven_energy_109696
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 109568 384 =
      172869139528555736464788587595824 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 109568 256 128
      133689782840864042626109802241024 39179356687691693838678785354800 h1 levelEleven_energy_109824
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 109568 512 =
      207350185835253182959044711038473 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 109568 384 128
      172869139528555736464788587595824 34481046306697446494256123442649 h2 levelEleven_energy_109952
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_214 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109568 512 =
      4763791243679073205108472 := by
  have h0 := levelEleven_fractional_109568
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109568 256 =
      2728293013063709436781869 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109568 128 128
      1063179951923347394434328 1665113061140362042347541 h0 levelEleven_fractional_109696
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109568 384 =
      3755492875266340233006269 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109568 256 128
      2728293013063709436781869 1027199862202630796224400 h1 levelEleven_fractional_109824
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109568 512 =
      4763791243679073205108472 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 109568 384 128
      3755492875266340233006269 1008298368412732972102203 h2 levelEleven_fractional_109952
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_214 : ∀ i : Fin 512,
    levelEleven.lookup (109568 + i.val) ≤ levelElevenRoots.lookup (109568 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_109568
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 109568 128 128
    h0 levelEleven_squares_109696
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 109568 256 128
    h1 levelEleven_squares_109824
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 109568 384 128
    h2 levelEleven_squares_109952
  exact h3

end WordCertDensity.Certificates
