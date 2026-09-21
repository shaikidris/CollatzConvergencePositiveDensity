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
theorem levelEleven_energy_133120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 133120 128 =
      40012273780233495764044192446343 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_133120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133120 128 =
      1054189763823592813656123 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_133120 : ∀ i : Fin 128,
    levelEleven.lookup (133120 + i.val) ≤ levelElevenRoots.lookup (133120 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_133248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 133248 128 =
      142853674635460604873739127021911 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_133248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133248 128 =
      2207523365410363511079639 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_133248 : ∀ i : Fin 128,
    levelEleven.lookup (133248 + i.val) ≤ levelElevenRoots.lookup (133248 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_133376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 133376 128 =
      65463337833528803128392866811617 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_133376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133376 128 =
      1190600359650240333848624 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_133376 : ∀ i : Fin 128,
    levelEleven.lookup (133376 + i.val) ≤ levelElevenRoots.lookup (133376 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_133504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 133504 128 =
      66967242739747150419460311507945 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_133504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133504 128 =
      1470699295592622064569216 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_133504 : ∀ i : Fin 128,
    levelEleven.lookup (133504 + i.val) ≤ levelElevenRoots.lookup (133504 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_260 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 133120 512 =
      315296528988970054185636497787816 := by
  have h0 := levelEleven_energy_133120
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 133120 256 =
      182865948415694100637783319468254 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 133120 128 128
      40012273780233495764044192446343 142853674635460604873739127021911 h0 levelEleven_energy_133248
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 133120 384 =
      248329286249222903766176186279871 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 133120 256 128
      182865948415694100637783319468254 65463337833528803128392866811617 h1 levelEleven_energy_133376
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 133120 512 =
      315296528988970054185636497787816 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 133120 384 128
      248329286249222903766176186279871 66967242739747150419460311507945 h2 levelEleven_energy_133504
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_260 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133120 512 =
      5923012784476818723153602 := by
  have h0 := levelEleven_fractional_133120
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133120 256 =
      3261713129233956324735762 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133120 128 128
      1054189763823592813656123 2207523365410363511079639 h0 levelEleven_fractional_133248
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133120 384 =
      4452313488884196658584386 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133120 256 128
      3261713129233956324735762 1190600359650240333848624 h1 levelEleven_fractional_133376
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133120 512 =
      5923012784476818723153602 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 133120 384 128
      4452313488884196658584386 1470699295592622064569216 h2 levelEleven_fractional_133504
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_260 : ∀ i : Fin 512,
    levelEleven.lookup (133120 + i.val) ≤ levelElevenRoots.lookup (133120 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_133120
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 133120 128 128
    h0 levelEleven_squares_133248
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 133120 256 128
    h1 levelEleven_squares_133376
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 133120 384 128
    h2 levelEleven_squares_133504
  exact h3

end WordCertDensity.Certificates
