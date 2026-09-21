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
theorem levelEleven_energy_157184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 157184 128 =
      27158334001352941098635920505698 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_157184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157184 128 =
      852970328497437035590955 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_157184 : ∀ i : Fin 128,
    levelEleven.lookup (157184 + i.val) ≤ levelElevenRoots.lookup (157184 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_157312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 157312 128 =
      75680703095568858690858682514643 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_157312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157312 128 =
      1598656536668726821491409 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_157312 : ∀ i : Fin 128,
    levelEleven.lookup (157312 + i.val) ≤ levelElevenRoots.lookup (157312 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_157440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 157440 128 =
      56642640177552026877467215857915 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_157440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157440 128 =
      1141150216156207481893625 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_157440 : ∀ i : Fin 128,
    levelEleven.lookup (157440 + i.val) ≤ levelElevenRoots.lookup (157440 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_157568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 157568 128 =
      116801568103296153307328979907106 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_157568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157568 128 =
      2025319675090046227331505 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_157568 : ∀ i : Fin 128,
    levelEleven.lookup (157568 + i.val) ≤ levelElevenRoots.lookup (157568 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_307 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 157184 512 =
      276283245377769979974290798785362 := by
  have h0 := levelEleven_energy_157184
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 157184 256 =
      102839037096921799789494603020341 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 157184 128 128
      27158334001352941098635920505698 75680703095568858690858682514643 h0 levelEleven_energy_157312
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 157184 384 =
      159481677274473826666961818878256 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 157184 256 128
      102839037096921799789494603020341 56642640177552026877467215857915 h1 levelEleven_energy_157440
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 157184 512 =
      276283245377769979974290798785362 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 157184 384 128
      159481677274473826666961818878256 116801568103296153307328979907106 h2 levelEleven_energy_157568
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_307 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157184 512 =
      5618096756412417566307494 := by
  have h0 := levelEleven_fractional_157184
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157184 256 =
      2451626865166163857082364 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157184 128 128
      852970328497437035590955 1598656536668726821491409 h0 levelEleven_fractional_157312
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157184 384 =
      3592777081322371338975989 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157184 256 128
      2451626865166163857082364 1141150216156207481893625 h1 levelEleven_fractional_157440
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157184 512 =
      5618096756412417566307494 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157184 384 128
      3592777081322371338975989 2025319675090046227331505 h2 levelEleven_fractional_157568
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_307 : ∀ i : Fin 512,
    levelEleven.lookup (157184 + i.val) ≤ levelElevenRoots.lookup (157184 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_157184
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 157184 128 128
    h0 levelEleven_squares_157312
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 157184 256 128
    h1 levelEleven_squares_157440
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 157184 384 128
    h2 levelEleven_squares_157568
  exact h3

end WordCertDensity.Certificates
