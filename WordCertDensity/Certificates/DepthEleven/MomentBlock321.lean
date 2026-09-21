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
theorem levelEleven_energy_164352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 164352 128 =
      32298262770918206308479166658670 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_164352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164352 128 =
      991940365122505307404682 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_164352 : ∀ i : Fin 128,
    levelEleven.lookup (164352 + i.val) ≤ levelElevenRoots.lookup (164352 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_164480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 164480 128 =
      21799156434879014503189093360581 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_164480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164480 128 =
      759646622389971916541797 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_164480 : ∀ i : Fin 128,
    levelEleven.lookup (164480 + i.val) ≤ levelElevenRoots.lookup (164480 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_164608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 164608 128 =
      220702078859091797027205927620932 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_164608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164608 128 =
      2541933643720236988950941 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_164608 : ∀ i : Fin 128,
    levelEleven.lookup (164608 + i.val) ≤ levelElevenRoots.lookup (164608 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_164736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 164736 128 =
      41302247578651030507800091854834 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_164736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164736 128 =
      994195143493791756979496 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_164736 : ∀ i : Fin 128,
    levelEleven.lookup (164736 + i.val) ≤ levelElevenRoots.lookup (164736 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_321 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 164352 512 =
      316101745643540048346674279495017 := by
  have h0 := levelEleven_energy_164352
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 164352 256 =
      54097419205797220811668260019251 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 164352 128 128
      32298262770918206308479166658670 21799156434879014503189093360581 h0 levelEleven_energy_164480
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 164352 384 =
      274799498064889017838874187640183 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 164352 256 128
      54097419205797220811668260019251 220702078859091797027205927620932 h1 levelEleven_energy_164608
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 164352 512 =
      316101745643540048346674279495017 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 164352 384 128
      274799498064889017838874187640183 41302247578651030507800091854834 h2 levelEleven_energy_164736
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_321 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164352 512 =
      5287715774726505969876916 := by
  have h0 := levelEleven_fractional_164352
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164352 256 =
      1751586987512477223946479 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164352 128 128
      991940365122505307404682 759646622389971916541797 h0 levelEleven_fractional_164480
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164352 384 =
      4293520631232714212897420 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164352 256 128
      1751586987512477223946479 2541933643720236988950941 h1 levelEleven_fractional_164608
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164352 512 =
      5287715774726505969876916 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164352 384 128
      4293520631232714212897420 994195143493791756979496 h2 levelEleven_fractional_164736
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_321 : ∀ i : Fin 512,
    levelEleven.lookup (164352 + i.val) ≤ levelElevenRoots.lookup (164352 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_164352
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 164352 128 128
    h0 levelEleven_squares_164480
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 164352 256 128
    h1 levelEleven_squares_164608
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 164352 384 128
    h2 levelEleven_squares_164736
  exact h3

end WordCertDensity.Certificates
