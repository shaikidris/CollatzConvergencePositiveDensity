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
theorem levelEleven_energy_63488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 63488 128 =
      57491159736313965389360457792041 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_63488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63488 128 =
      1317868631049820424063037 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_63488 : ∀ i : Fin 128,
    levelEleven.lookup (63488 + i.val) ≤ levelElevenRoots.lookup (63488 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_63616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 63616 128 =
      739333426982814547714209861838439 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_63616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63616 128 =
      5218141458843210110324595 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_63616 : ∀ i : Fin 128,
    levelEleven.lookup (63616 + i.val) ≤ levelElevenRoots.lookup (63616 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_63744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 63744 128 =
      51868554929226547255032804132458 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_63744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63744 128 =
      1196290333592396187116982 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_63744 : ∀ i : Fin 128,
    levelEleven.lookup (63744 + i.val) ≤ levelElevenRoots.lookup (63744 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_63872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 63872 128 =
      18902731413878833942043879746091 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_63872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63872 128 =
      672294945492024551244744 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_63872 : ∀ i : Fin 128,
    levelEleven.lookup (63872 + i.val) ≤ levelElevenRoots.lookup (63872 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_124 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 63488 512 =
      867595873062233894300647003509029 := by
  have h0 := levelEleven_energy_63488
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 63488 256 =
      796824586719128513103570319630480 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 63488 128 128
      57491159736313965389360457792041 739333426982814547714209861838439 h0 levelEleven_energy_63616
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 63488 384 =
      848693141648355060358603123762938 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 63488 256 128
      796824586719128513103570319630480 51868554929226547255032804132458 h1 levelEleven_energy_63744
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 63488 512 =
      867595873062233894300647003509029 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 63488 384 128
      848693141648355060358603123762938 18902731413878833942043879746091 h2 levelEleven_energy_63872
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_124 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63488 512 =
      8404595368977451272749358 := by
  have h0 := levelEleven_fractional_63488
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63488 256 =
      6536010089893030534387632 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63488 128 128
      1317868631049820424063037 5218141458843210110324595 h0 levelEleven_fractional_63616
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63488 384 =
      7732300423485426721504614 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63488 256 128
      6536010089893030534387632 1196290333592396187116982 h1 levelEleven_fractional_63744
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63488 512 =
      8404595368977451272749358 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63488 384 128
      7732300423485426721504614 672294945492024551244744 h2 levelEleven_fractional_63872
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_124 : ∀ i : Fin 512,
    levelEleven.lookup (63488 + i.val) ≤ levelElevenRoots.lookup (63488 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_63488
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 63488 128 128
    h0 levelEleven_squares_63616
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 63488 256 128
    h1 levelEleven_squares_63744
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 63488 384 128
    h2 levelEleven_squares_63872
  exact h3

end WordCertDensity.Certificates
