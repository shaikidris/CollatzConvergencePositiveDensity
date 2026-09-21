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
theorem levelEleven_energy_165888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 165888 128 =
      38043646252458859512602863094658 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_165888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165888 128 =
      998865416351812787446178 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_165888 : ∀ i : Fin 128,
    levelEleven.lookup (165888 + i.val) ≤ levelElevenRoots.lookup (165888 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_166016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 166016 128 =
      739530307704962580048332119899970 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_166016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166016 128 =
      5235544178977124150123127 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_166016 : ∀ i : Fin 128,
    levelEleven.lookup (166016 + i.val) ≤ levelElevenRoots.lookup (166016 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_166144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 166144 128 =
      44120094427605282695448952018789 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_166144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166144 128 =
      1151459235384208798189173 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_166144 : ∀ i : Fin 128,
    levelEleven.lookup (166144 + i.val) ≤ levelElevenRoots.lookup (166144 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_166272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 166272 128 =
      40242733618301340590807517923771 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_166272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166272 128 =
      1106230787729316871056186 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_166272 : ∀ i : Fin 128,
    levelEleven.lookup (166272 + i.val) ≤ levelElevenRoots.lookup (166272 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_324 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 165888 512 =
      861936782003328062847191452937188 := by
  have h0 := levelEleven_energy_165888
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 165888 256 =
      777573953957421439560934982994628 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 165888 128 128
      38043646252458859512602863094658 739530307704962580048332119899970 h0 levelEleven_energy_166016
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 165888 384 =
      821694048385026722256383935013417 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 165888 256 128
      777573953957421439560934982994628 44120094427605282695448952018789 h1 levelEleven_energy_166144
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 165888 512 =
      861936782003328062847191452937188 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 165888 384 128
      821694048385026722256383935013417 40242733618301340590807517923771 h2 levelEleven_energy_166272
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_324 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165888 512 =
      8492099618442462606814664 := by
  have h0 := levelEleven_fractional_165888
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165888 256 =
      6234409595328936937569305 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165888 128 128
      998865416351812787446178 5235544178977124150123127 h0 levelEleven_fractional_166016
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165888 384 =
      7385868830713145735758478 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165888 256 128
      6234409595328936937569305 1151459235384208798189173 h1 levelEleven_fractional_166144
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165888 512 =
      8492099618442462606814664 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165888 384 128
      7385868830713145735758478 1106230787729316871056186 h2 levelEleven_fractional_166272
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_324 : ∀ i : Fin 512,
    levelEleven.lookup (165888 + i.val) ≤ levelElevenRoots.lookup (165888 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_165888
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 165888 128 128
    h0 levelEleven_squares_166016
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 165888 256 128
    h1 levelEleven_squares_166144
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 165888 384 128
    h2 levelEleven_squares_166272
  exact h3

end WordCertDensity.Certificates
