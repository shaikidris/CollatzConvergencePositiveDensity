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
theorem levelEleven_energy_26624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 26624 128 =
      47104313807306992915574928912904 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_26624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26624 128 =
      1231289206857606374787333 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_26624 : ∀ i : Fin 128,
    levelEleven.lookup (26624 + i.val) ≤ levelElevenRoots.lookup (26624 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_26752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 26752 128 =
      43183138225978867716206815203611 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_26752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26752 128 =
      943981986226111903323553 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_26752 : ∀ i : Fin 128,
    levelEleven.lookup (26752 + i.val) ≤ levelElevenRoots.lookup (26752 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_26880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 26880 128 =
      59304704141416770072717151950407 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_26880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26880 128 =
      1346495348650860166700910 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_26880 : ∀ i : Fin 128,
    levelEleven.lookup (26880 + i.val) ≤ levelElevenRoots.lookup (26880 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_27008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 27008 128 =
      26538221199120320169338300949086 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_27008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27008 128 =
      781918776973525717957527 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_27008 : ∀ i : Fin 128,
    levelEleven.lookup (27008 + i.val) ≤ levelElevenRoots.lookup (27008 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_52 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 26624 512 =
      176130377373822950873837197016008 := by
  have h0 := levelEleven_energy_26624
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 26624 256 =
      90287452033285860631781744116515 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 26624 128 128
      47104313807306992915574928912904 43183138225978867716206815203611 h0 levelEleven_energy_26752
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 26624 384 =
      149592156174702630704498896066922 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 26624 256 128
      90287452033285860631781744116515 59304704141416770072717151950407 h1 levelEleven_energy_26880
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 26624 512 =
      176130377373822950873837197016008 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 26624 384 128
      149592156174702630704498896066922 26538221199120320169338300949086 h2 levelEleven_energy_27008
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_52 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26624 512 =
      4303685318708104162769323 := by
  have h0 := levelEleven_fractional_26624
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26624 256 =
      2175271193083718278110886 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26624 128 128
      1231289206857606374787333 943981986226111903323553 h0 levelEleven_fractional_26752
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26624 384 =
      3521766541734578444811796 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26624 256 128
      2175271193083718278110886 1346495348650860166700910 h1 levelEleven_fractional_26880
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26624 512 =
      4303685318708104162769323 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26624 384 128
      3521766541734578444811796 781918776973525717957527 h2 levelEleven_fractional_27008
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_52 : ∀ i : Fin 512,
    levelEleven.lookup (26624 + i.val) ≤ levelElevenRoots.lookup (26624 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_26624
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 26624 128 128
    h0 levelEleven_squares_26752
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 26624 256 128
    h1 levelEleven_squares_26880
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 26624 384 128
    h2 levelEleven_squares_27008
  exact h3

end WordCertDensity.Certificates
