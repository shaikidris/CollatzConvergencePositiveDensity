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
theorem levelEleven_energy_169472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 169472 128 =
      28664913921226954799045992948171 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_169472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169472 128 =
      889360174878935827952569 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_169472 : ∀ i : Fin 128,
    levelEleven.lookup (169472 + i.val) ≤ levelElevenRoots.lookup (169472 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_169600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 169600 128 =
      36006690620146868751171748686556 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_169600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169600 128 =
      973146609321741557159179 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_169600 : ∀ i : Fin 128,
    levelEleven.lookup (169600 + i.val) ≤ levelElevenRoots.lookup (169600 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_169728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 169728 128 =
      266039679407858852393831205861677 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_169728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169728 128 =
      2765471363218751420889698 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_169728 : ∀ i : Fin 128,
    levelEleven.lookup (169728 + i.val) ≤ levelElevenRoots.lookup (169728 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_169856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 169856 128 =
      32915813267587479067289596324087 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_169856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169856 128 =
      908673542454909018495110 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_169856 : ∀ i : Fin 128,
    levelEleven.lookup (169856 + i.val) ≤ levelElevenRoots.lookup (169856 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_331 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 169472 512 =
      363627097216820155011338543820491 := by
  have h0 := levelEleven_energy_169472
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 169472 256 =
      64671604541373823550217741634727 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 169472 128 128
      28664913921226954799045992948171 36006690620146868751171748686556 h0 levelEleven_energy_169600
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 169472 384 =
      330711283949232675944048947496404 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 169472 256 128
      64671604541373823550217741634727 266039679407858852393831205861677 h1 levelEleven_energy_169728
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 169472 512 =
      363627097216820155011338543820491 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 169472 384 128
      330711283949232675944048947496404 32915813267587479067289596324087 h2 levelEleven_energy_169856
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_331 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169472 512 =
      5536651689874337824496556 := by
  have h0 := levelEleven_fractional_169472
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169472 256 =
      1862506784200677385111748 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169472 128 128
      889360174878935827952569 973146609321741557159179 h0 levelEleven_fractional_169600
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169472 384 =
      4627978147419428806001446 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169472 256 128
      1862506784200677385111748 2765471363218751420889698 h1 levelEleven_fractional_169728
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169472 512 =
      5536651689874337824496556 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169472 384 128
      4627978147419428806001446 908673542454909018495110 h2 levelEleven_fractional_169856
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_331 : ∀ i : Fin 512,
    levelEleven.lookup (169472 + i.val) ≤ levelElevenRoots.lookup (169472 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_169472
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 169472 128 128
    h0 levelEleven_squares_169600
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 169472 256 128
    h1 levelEleven_squares_169728
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 169472 384 128
    h2 levelEleven_squares_169856
  exact h3

end WordCertDensity.Certificates
