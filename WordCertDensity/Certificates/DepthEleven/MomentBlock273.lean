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
theorem levelEleven_energy_139776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 139776 128 =
      94229682639495060472814603907204 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_139776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139776 128 =
      1631160658178918402522838 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_139776 : ∀ i : Fin 128,
    levelEleven.lookup (139776 + i.val) ≤ levelElevenRoots.lookup (139776 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_139904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 139904 128 =
      253160268058840036426426833519612 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_139904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139904 128 =
      2800445306572753419702404 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_139904 : ∀ i : Fin 128,
    levelEleven.lookup (139904 + i.val) ≤ levelElevenRoots.lookup (139904 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_140032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 140032 128 =
      138271926541637830914449010470744 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_140032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140032 128 =
      2110853937499454451853748 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_140032 : ∀ i : Fin 128,
    levelEleven.lookup (140032 + i.val) ≤ levelElevenRoots.lookup (140032 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_140160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 140160 128 =
      54007085968124091290400659723979 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_140160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 140160 128 =
      1254325027638339122627808 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_140160 : ∀ i : Fin 128,
    levelEleven.lookup (140160 + i.val) ≤ levelElevenRoots.lookup (140160 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_273 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 139776 512 =
      539668963208097019104091107621539 := by
  have h0 := levelEleven_energy_139776
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 139776 256 =
      347389950698335096899241437426816 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 139776 128 128
      94229682639495060472814603907204 253160268058840036426426833519612 h0 levelEleven_energy_139904
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 139776 384 =
      485661877239972927813690447897560 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 139776 256 128
      347389950698335096899241437426816 138271926541637830914449010470744 h1 levelEleven_energy_140032
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 139776 512 =
      539668963208097019104091107621539 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 139776 384 128
      485661877239972927813690447897560 54007085968124091290400659723979 h2 levelEleven_energy_140160
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_273 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139776 512 =
      7796784929889465396706798 := by
  have h0 := levelEleven_fractional_139776
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139776 256 =
      4431605964751671822225242 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139776 128 128
      1631160658178918402522838 2800445306572753419702404 h0 levelEleven_fractional_139904
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139776 384 =
      6542459902251126274078990 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139776 256 128
      4431605964751671822225242 2110853937499454451853748 h1 levelEleven_fractional_140032
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139776 512 =
      7796784929889465396706798 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139776 384 128
      6542459902251126274078990 1254325027638339122627808 h2 levelEleven_fractional_140160
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_273 : ∀ i : Fin 512,
    levelEleven.lookup (139776 + i.val) ≤ levelElevenRoots.lookup (139776 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_139776
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 139776 128 128
    h0 levelEleven_squares_139904
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 139776 256 128
    h1 levelEleven_squares_140032
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 139776 384 128
    h2 levelEleven_squares_140160
  exact h3

end WordCertDensity.Certificates
