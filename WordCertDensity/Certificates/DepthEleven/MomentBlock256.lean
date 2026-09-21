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
theorem levelEleven_energy_131072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 131072 128 =
      46348529943866211370300476341120 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_131072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131072 128 =
      1172941671951626645280223 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_131072 : ∀ i : Fin 128,
    levelEleven.lookup (131072 + i.val) ≤ levelElevenRoots.lookup (131072 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_131200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 131200 128 =
      65353026732216617367587497538732 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_131200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131200 128 =
      1291992112400153679005159 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_131200 : ∀ i : Fin 128,
    levelEleven.lookup (131200 + i.val) ≤ levelElevenRoots.lookup (131200 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_131328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 131328 128 =
      45789730791235287977421143785288 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_131328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131328 128 =
      1149899445561110108766569 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_131328 : ∀ i : Fin 128,
    levelEleven.lookup (131328 + i.val) ≤ levelElevenRoots.lookup (131328 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_131456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 131456 128 =
      52992687547206720715791734247002 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_131456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131456 128 =
      1296746033501545035201300 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_131456 : ∀ i : Fin 128,
    levelEleven.lookup (131456 + i.val) ≤ levelElevenRoots.lookup (131456 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 131072 512 =
      210483975014524837431100851912142 := by
  have h0 := levelEleven_energy_131072
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 131072 256 =
      111701556676082828737887973879852 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 131072 128 128
      46348529943866211370300476341120 65353026732216617367587497538732 h0 levelEleven_energy_131200
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 131072 384 =
      157491287467318116715309117665140 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 131072 256 128
      111701556676082828737887973879852 45789730791235287977421143785288 h1 levelEleven_energy_131328
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 131072 512 =
      210483975014524837431100851912142 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 131072 384 128
      157491287467318116715309117665140 52992687547206720715791734247002 h2 levelEleven_energy_131456
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131072 512 =
      4911579263414435468253251 := by
  have h0 := levelEleven_fractional_131072
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131072 256 =
      2464933784351780324285382 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131072 128 128
      1172941671951626645280223 1291992112400153679005159 h0 levelEleven_fractional_131200
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131072 384 =
      3614833229912890433051951 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131072 256 128
      2464933784351780324285382 1149899445561110108766569 h1 levelEleven_fractional_131328
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131072 512 =
      4911579263414435468253251 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 131072 384 128
      3614833229912890433051951 1296746033501545035201300 h2 levelEleven_fractional_131456
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_256 : ∀ i : Fin 512,
    levelEleven.lookup (131072 + i.val) ≤ levelElevenRoots.lookup (131072 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_131072
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 131072 128 128
    h0 levelEleven_squares_131200
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 131072 256 128
    h1 levelEleven_squares_131328
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 131072 384 128
    h2 levelEleven_squares_131456
  exact h3

end WordCertDensity.Certificates
