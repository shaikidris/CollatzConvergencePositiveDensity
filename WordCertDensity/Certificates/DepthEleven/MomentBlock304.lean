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
theorem levelEleven_energy_155648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 155648 128 =
      74957837338737037530183240005390 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_155648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155648 128 =
      1587502465351122563641745 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_155648 : ∀ i : Fin 128,
    levelEleven.lookup (155648 + i.val) ≤ levelElevenRoots.lookup (155648 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_155776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 155776 128 =
      17132212113299441399485550108631 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_155776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155776 128 =
      599282899405128076933212 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_155776 : ∀ i : Fin 128,
    levelEleven.lookup (155776 + i.val) ≤ levelElevenRoots.lookup (155776 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_155904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 155904 128 =
      58550486676084102360395216344990 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_155904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155904 128 =
      1338626125490293504772021 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_155904 : ∀ i : Fin 128,
    levelEleven.lookup (155904 + i.val) ≤ levelElevenRoots.lookup (155904 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_156032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 156032 128 =
      24972794290509047152923797609268 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_156032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156032 128 =
      737357253316613984209349 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_156032 : ∀ i : Fin 128,
    levelEleven.lookup (156032 + i.val) ≤ levelElevenRoots.lookup (156032 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 155648 512 =
      175613330418629628442987804068279 := by
  have h0 := levelEleven_energy_155648
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 155648 256 =
      92090049452036478929668790114021 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 155648 128 128
      74957837338737037530183240005390 17132212113299441399485550108631 h0 levelEleven_energy_155776
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 155648 384 =
      150640536128120581290064006459011 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 155648 256 128
      92090049452036478929668790114021 58550486676084102360395216344990 h1 levelEleven_energy_155904
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 155648 512 =
      175613330418629628442987804068279 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 155648 384 128
      150640536128120581290064006459011 24972794290509047152923797609268 h2 levelEleven_energy_156032
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155648 512 =
      4262768743563158129556327 := by
  have h0 := levelEleven_fractional_155648
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155648 256 =
      2186785364756250640574957 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155648 128 128
      1587502465351122563641745 599282899405128076933212 h0 levelEleven_fractional_155776
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155648 384 =
      3525411490246544145346978 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155648 256 128
      2186785364756250640574957 1338626125490293504772021 h1 levelEleven_fractional_155904
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155648 512 =
      4262768743563158129556327 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 155648 384 128
      3525411490246544145346978 737357253316613984209349 h2 levelEleven_fractional_156032
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_304 : ∀ i : Fin 512,
    levelEleven.lookup (155648 + i.val) ≤ levelElevenRoots.lookup (155648 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_155648
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 155648 128 128
    h0 levelEleven_squares_155776
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 155648 256 128
    h1 levelEleven_squares_155904
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 155648 384 128
    h2 levelEleven_squares_156032
  exact h3

end WordCertDensity.Certificates
