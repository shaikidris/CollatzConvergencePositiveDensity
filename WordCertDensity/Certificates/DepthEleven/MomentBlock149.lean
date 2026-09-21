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
theorem levelEleven_energy_76288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 76288 128 =
      40356709981695376986846417457391 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_76288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76288 128 =
      1080032944037953400634941 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_76288 : ∀ i : Fin 128,
    levelEleven.lookup (76288 + i.val) ≤ levelElevenRoots.lookup (76288 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_76416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 76416 128 =
      49078456886678705246559528170758 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_76416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76416 128 =
      1239789887520239263477712 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_76416 : ∀ i : Fin 128,
    levelEleven.lookup (76416 + i.val) ≤ levelElevenRoots.lookup (76416 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_76544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 76544 128 =
      15724316952746572299064457194231 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_76544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76544 128 =
      607792786455393338378318 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_76544 : ∀ i : Fin 128,
    levelEleven.lookup (76544 + i.val) ≤ levelElevenRoots.lookup (76544 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_76672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 76672 128 =
      85597381938232375869065909928499 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_76672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76672 128 =
      1696994124634206076943347 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_76672 : ∀ i : Fin 128,
    levelEleven.lookup (76672 + i.val) ≤ levelElevenRoots.lookup (76672 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_149 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 76288 512 =
      190756865759353030401536312750879 := by
  have h0 := levelEleven_energy_76288
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 76288 256 =
      89435166868374082233405945628149 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 76288 128 128
      40356709981695376986846417457391 49078456886678705246559528170758 h0 levelEleven_energy_76416
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 76288 384 =
      105159483821120654532470402822380 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 76288 256 128
      89435166868374082233405945628149 15724316952746572299064457194231 h1 levelEleven_energy_76544
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 76288 512 =
      190756865759353030401536312750879 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 76288 384 128
      105159483821120654532470402822380 85597381938232375869065909928499 h2 levelEleven_energy_76672
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_149 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76288 512 =
      4624609742647792079434318 := by
  have h0 := levelEleven_fractional_76288
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76288 256 =
      2319822831558192664112653 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76288 128 128
      1080032944037953400634941 1239789887520239263477712 h0 levelEleven_fractional_76416
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76288 384 =
      2927615618013586002490971 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76288 256 128
      2319822831558192664112653 607792786455393338378318 h1 levelEleven_fractional_76544
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76288 512 =
      4624609742647792079434318 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 76288 384 128
      2927615618013586002490971 1696994124634206076943347 h2 levelEleven_fractional_76672
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_149 : ∀ i : Fin 512,
    levelEleven.lookup (76288 + i.val) ≤ levelElevenRoots.lookup (76288 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_76288
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 76288 128 128
    h0 levelEleven_squares_76416
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 76288 256 128
    h1 levelEleven_squares_76544
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 76288 384 128
    h2 levelEleven_squares_76672
  exact h3

end WordCertDensity.Certificates
