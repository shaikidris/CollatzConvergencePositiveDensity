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
theorem levelEleven_energy_79872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 79872 128 =
      20695531514006723431401296662670 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_79872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79872 128 =
      720043945331013803814853 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_79872 : ∀ i : Fin 128,
    levelEleven.lookup (79872 + i.val) ≤ levelElevenRoots.lookup (79872 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_80000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 80000 128 =
      84319964652586732384660385318047 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_80000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80000 128 =
      1485766549385541654524918 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_80000 : ∀ i : Fin 128,
    levelEleven.lookup (80000 + i.val) ≤ levelElevenRoots.lookup (80000 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_80128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 80128 128 =
      34418973973954429774631333647611 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_80128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80128 128 =
      915414898006832652116631 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_80128 : ∀ i : Fin 128,
    levelEleven.lookup (80128 + i.val) ≤ levelElevenRoots.lookup (80128 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_80256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 80256 128 =
      58124283385859318447662960546194 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_80256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80256 128 =
      1404597345135487849755653 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_80256 : ∀ i : Fin 128,
    levelEleven.lookup (80256 + i.val) ≤ levelElevenRoots.lookup (80256 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_156 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 79872 512 =
      197558753526407204038355976174522 := by
  have h0 := levelEleven_energy_79872
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 79872 256 =
      105015496166593455816061681980717 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 79872 128 128
      20695531514006723431401296662670 84319964652586732384660385318047 h0 levelEleven_energy_80000
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 79872 384 =
      139434470140547885590693015628328 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 79872 256 128
      105015496166593455816061681980717 34418973973954429774631333647611 h1 levelEleven_energy_80128
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 79872 512 =
      197558753526407204038355976174522 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 79872 384 128
      139434470140547885590693015628328 58124283385859318447662960546194 h2 levelEleven_energy_80256
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_156 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79872 512 =
      4525822737858875960212055 := by
  have h0 := levelEleven_fractional_79872
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79872 256 =
      2205810494716555458339771 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79872 128 128
      720043945331013803814853 1485766549385541654524918 h0 levelEleven_fractional_80000
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79872 384 =
      3121225392723388110456402 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79872 256 128
      2205810494716555458339771 915414898006832652116631 h1 levelEleven_fractional_80128
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79872 512 =
      4525822737858875960212055 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 79872 384 128
      3121225392723388110456402 1404597345135487849755653 h2 levelEleven_fractional_80256
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_156 : ∀ i : Fin 512,
    levelEleven.lookup (79872 + i.val) ≤ levelElevenRoots.lookup (79872 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_79872
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 79872 128 128
    h0 levelEleven_squares_80000
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 79872 256 128
    h1 levelEleven_squares_80128
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 79872 384 128
    h2 levelEleven_squares_80256
  exact h3

end WordCertDensity.Certificates
