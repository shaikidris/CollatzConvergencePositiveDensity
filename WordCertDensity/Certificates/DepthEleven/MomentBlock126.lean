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
theorem levelEleven_energy_64512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 64512 128 =
      43382140282676992567408670217848 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_64512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64512 128 =
      1056474509057695141617379 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_64512 : ∀ i : Fin 128,
    levelEleven.lookup (64512 + i.val) ≤ levelElevenRoots.lookup (64512 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_64640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 64640 128 =
      25158660935930036319369868633748 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_64640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64640 128 =
      828281146963036322467490 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_64640 : ∀ i : Fin 128,
    levelEleven.lookup (64640 + i.val) ≤ levelElevenRoots.lookup (64640 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_64768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 64768 128 =
      148878706161601936211192707190022 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_64768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64768 128 =
      2171656806885424366680120 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_64768 : ∀ i : Fin 128,
    levelEleven.lookup (64768 + i.val) ≤ levelElevenRoots.lookup (64768 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_64896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 64896 128 =
      16062602091248916295308115502713 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_64896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64896 128 =
      603578779679670958954232 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_64896 : ∀ i : Fin 128,
    levelEleven.lookup (64896 + i.val) ≤ levelElevenRoots.lookup (64896 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_126 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 64512 512 =
      233482109471457881393279361544331 := by
  have h0 := levelEleven_energy_64512
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 64512 256 =
      68540801218607028886778538851596 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 64512 128 128
      43382140282676992567408670217848 25158660935930036319369868633748 h0 levelEleven_energy_64640
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 64512 384 =
      217419507380208965097971246041618 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 64512 256 128
      68540801218607028886778538851596 148878706161601936211192707190022 h1 levelEleven_energy_64768
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 64512 512 =
      233482109471457881393279361544331 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 64512 384 128
      217419507380208965097971246041618 16062602091248916295308115502713 h2 levelEleven_energy_64896
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_126 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64512 512 =
      4659991242585826789719221 := by
  have h0 := levelEleven_fractional_64512
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64512 256 =
      1884755656020731464084869 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64512 128 128
      1056474509057695141617379 828281146963036322467490 h0 levelEleven_fractional_64640
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64512 384 =
      4056412462906155830764989 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64512 256 128
      1884755656020731464084869 2171656806885424366680120 h1 levelEleven_fractional_64768
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64512 512 =
      4659991242585826789719221 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 64512 384 128
      4056412462906155830764989 603578779679670958954232 h2 levelEleven_fractional_64896
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_126 : ∀ i : Fin 512,
    levelEleven.lookup (64512 + i.val) ≤ levelElevenRoots.lookup (64512 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_64512
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 64512 128 128
    h0 levelEleven_squares_64640
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 64512 256 128
    h1 levelEleven_squares_64768
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 64512 384 128
    h2 levelEleven_squares_64896
  exact h3

end WordCertDensity.Certificates
