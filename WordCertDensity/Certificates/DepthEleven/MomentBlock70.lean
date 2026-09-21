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
theorem levelEleven_energy_35840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 35840 128 =
      85856936950428693463504374073553 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_35840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35840 128 =
      1654431676515027780456233 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_35840 : ∀ i : Fin 128,
    levelEleven.lookup (35840 + i.val) ≤ levelElevenRoots.lookup (35840 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_35968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 35968 128 =
      222434039187169203518965692648713 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_35968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35968 128 =
      2627897961560354884430227 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_35968 : ∀ i : Fin 128,
    levelEleven.lookup (35968 + i.val) ≤ levelElevenRoots.lookup (35968 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_36096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 36096 128 =
      23237768690342953435978040670717 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_36096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36096 128 =
      790175792727032644440621 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_36096 : ∀ i : Fin 128,
    levelEleven.lookup (36096 + i.val) ≤ levelElevenRoots.lookup (36096 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_36224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 36224 128 =
      19634642489359330848102528775565 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_36224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36224 128 =
      714609113068007080757738 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_36224 : ∀ i : Fin 128,
    levelEleven.lookup (36224 + i.val) ≤ levelElevenRoots.lookup (36224 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_70 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 35840 512 =
      351163387317300181266550636168548 := by
  have h0 := levelEleven_energy_35840
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 35840 256 =
      308290976137597896982470066722266 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 35840 128 128
      85856936950428693463504374073553 222434039187169203518965692648713 h0 levelEleven_energy_35968
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 35840 384 =
      331528744827940850418448107392983 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 35840 256 128
      308290976137597896982470066722266 23237768690342953435978040670717 h1 levelEleven_energy_36096
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 35840 512 =
      351163387317300181266550636168548 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 35840 384 128
      331528744827940850418448107392983 19634642489359330848102528775565 h2 levelEleven_energy_36224
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_70 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35840 512 =
      5787114543870422390084819 := by
  have h0 := levelEleven_fractional_35840
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35840 256 =
      4282329638075382664886460 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35840 128 128
      1654431676515027780456233 2627897961560354884430227 h0 levelEleven_fractional_35968
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35840 384 =
      5072505430802415309327081 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35840 256 128
      4282329638075382664886460 790175792727032644440621 h1 levelEleven_fractional_36096
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35840 512 =
      5787114543870422390084819 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35840 384 128
      5072505430802415309327081 714609113068007080757738 h2 levelEleven_fractional_36224
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_70 : ∀ i : Fin 512,
    levelEleven.lookup (35840 + i.val) ≤ levelElevenRoots.lookup (35840 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_35840
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 35840 128 128
    h0 levelEleven_squares_35968
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 35840 256 128
    h1 levelEleven_squares_36096
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 35840 384 128
    h2 levelEleven_squares_36224
  exact h3

end WordCertDensity.Certificates
