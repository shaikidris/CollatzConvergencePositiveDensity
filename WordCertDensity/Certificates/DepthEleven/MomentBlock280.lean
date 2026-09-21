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
theorem levelEleven_energy_143360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 143360 128 =
      37467871078624820167861233634779 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_143360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143360 128 =
      982273105520286994143900 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_143360 : ∀ i : Fin 128,
    levelEleven.lookup (143360 + i.val) ≤ levelElevenRoots.lookup (143360 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_143488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 143488 128 =
      42058395136187644774012879912138 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_143488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143488 128 =
      1133629938040273344914632 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_143488 : ∀ i : Fin 128,
    levelEleven.lookup (143488 + i.val) ≤ levelElevenRoots.lookup (143488 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_143616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 143616 128 =
      18436813988631078273460092018752 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_143616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143616 128 =
      656423536874402571176539 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_143616 : ∀ i : Fin 128,
    levelEleven.lookup (143616 + i.val) ≤ levelElevenRoots.lookup (143616 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_143744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 143744 128 =
      55131807313850686423599842168166 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_143744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143744 128 =
      1256220811186744441778364 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_143744 : ∀ i : Fin 128,
    levelEleven.lookup (143744 + i.val) ≤ levelElevenRoots.lookup (143744 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 143360 512 =
      153094887517294229638934047733835 := by
  have h0 := levelEleven_energy_143360
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 143360 256 =
      79526266214812464941874113546917 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 143360 128 128
      37467871078624820167861233634779 42058395136187644774012879912138 h0 levelEleven_energy_143488
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 143360 384 =
      97963080203443543215334205565669 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 143360 256 128
      79526266214812464941874113546917 18436813988631078273460092018752 h1 levelEleven_energy_143616
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 143360 512 =
      153094887517294229638934047733835 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 143360 384 128
      97963080203443543215334205565669 55131807313850686423599842168166 h2 levelEleven_energy_143744
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143360 512 =
      4028547391621707352013435 := by
  have h0 := levelEleven_fractional_143360
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143360 256 =
      2115903043560560339058532 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143360 128 128
      982273105520286994143900 1133629938040273344914632 h0 levelEleven_fractional_143488
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143360 384 =
      2772326580434962910235071 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143360 256 128
      2115903043560560339058532 656423536874402571176539 h1 levelEleven_fractional_143616
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143360 512 =
      4028547391621707352013435 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 143360 384 128
      2772326580434962910235071 1256220811186744441778364 h2 levelEleven_fractional_143744
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_280 : ∀ i : Fin 512,
    levelEleven.lookup (143360 + i.val) ≤ levelElevenRoots.lookup (143360 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_143360
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 143360 128 128
    h0 levelEleven_squares_143488
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 143360 256 128
    h1 levelEleven_squares_143616
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 143360 384 128
    h2 levelEleven_squares_143744
  exact h3

end WordCertDensity.Certificates
