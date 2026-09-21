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
theorem levelEleven_energy_11776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 11776 128 =
      51900942863707429821128978898360 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_11776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11776 128 =
      1184396698935271270322065 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_11776 : ∀ i : Fin 128,
    levelEleven.lookup (11776 + i.val) ≤ levelElevenRoots.lookup (11776 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_11904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 11904 128 =
      57358549530012841093323302139495 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_11904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11904 128 =
      1326420848252746802935667 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_11904 : ∀ i : Fin 128,
    levelEleven.lookup (11904 + i.val) ≤ levelElevenRoots.lookup (11904 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_12032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 12032 128 =
      21624606837224396754437123498783 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_12032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12032 128 =
      738195553723335136804145 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_12032 : ∀ i : Fin 128,
    levelEleven.lookup (12032 + i.val) ≤ levelElevenRoots.lookup (12032 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_12160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 12160 128 =
      35325014605445927202173872365027 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_12160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12160 128 =
      986049115260831355889280 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_12160 : ∀ i : Fin 128,
    levelEleven.lookup (12160 + i.val) ≤ levelElevenRoots.lookup (12160 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_23 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 11776 512 =
      166209113836390594871063276901665 := by
  have h0 := levelEleven_energy_11776
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 11776 256 =
      109259492393720270914452281037855 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 11776 128 128
      51900942863707429821128978898360 57358549530012841093323302139495 h0 levelEleven_energy_11904
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 11776 384 =
      130884099230944667668889404536638 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 11776 256 128
      109259492393720270914452281037855 21624606837224396754437123498783 h1 levelEleven_energy_12032
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 11776 512 =
      166209113836390594871063276901665 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 11776 384 128
      130884099230944667668889404536638 35325014605445927202173872365027 h2 levelEleven_energy_12160
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_23 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11776 512 =
      4235062216172184565951157 := by
  have h0 := levelEleven_fractional_11776
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11776 256 =
      2510817547188018073257732 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11776 128 128
      1184396698935271270322065 1326420848252746802935667 h0 levelEleven_fractional_11904
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11776 384 =
      3249013100911353210061877 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11776 256 128
      2510817547188018073257732 738195553723335136804145 h1 levelEleven_fractional_12032
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11776 512 =
      4235062216172184565951157 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11776 384 128
      3249013100911353210061877 986049115260831355889280 h2 levelEleven_fractional_12160
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_23 : ∀ i : Fin 512,
    levelEleven.lookup (11776 + i.val) ≤ levelElevenRoots.lookup (11776 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_11776
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 11776 128 128
    h0 levelEleven_squares_11904
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 11776 256 128
    h1 levelEleven_squares_12032
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 11776 384 128
    h2 levelEleven_squares_12160
  exact h3

end WordCertDensity.Certificates
