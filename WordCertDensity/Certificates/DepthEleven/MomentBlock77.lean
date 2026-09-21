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
theorem levelEleven_energy_39424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 39424 128 =
      54557203727054612192423169679890 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_39424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39424 128 =
      1325615083210124940554642 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_39424 : ∀ i : Fin 128,
    levelEleven.lookup (39424 + i.val) ≤ levelElevenRoots.lookup (39424 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_39552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 39552 128 =
      57535801245796152784701167830822 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_39552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39552 128 =
      1278384847137409719414737 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_39552 : ∀ i : Fin 128,
    levelEleven.lookup (39552 + i.val) ≤ levelElevenRoots.lookup (39552 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_39680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 39680 128 =
      47870759732610422832426793459125 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_39680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39680 128 =
      1203444935572342838487870 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_39680 : ∀ i : Fin 128,
    levelEleven.lookup (39680 + i.val) ≤ levelElevenRoots.lookup (39680 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_39808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 39808 128 =
      29658205986194174646231659736837 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_39808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39808 128 =
      903637952421547911464132 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_39808 : ∀ i : Fin 128,
    levelEleven.lookup (39808 + i.val) ≤ levelElevenRoots.lookup (39808 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_77 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 39424 512 =
      189621970691655362455782790706674 := by
  have h0 := levelEleven_energy_39424
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 39424 256 =
      112093004972850764977124337510712 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 39424 128 128
      54557203727054612192423169679890 57535801245796152784701167830822 h0 levelEleven_energy_39552
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 39424 384 =
      159963764705461187809551130969837 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 39424 256 128
      112093004972850764977124337510712 47870759732610422832426793459125 h1 levelEleven_energy_39680
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 39424 512 =
      189621970691655362455782790706674 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 39424 384 128
      159963764705461187809551130969837 29658205986194174646231659736837 h2 levelEleven_energy_39808
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_77 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39424 512 =
      4711082818341425409921381 := by
  have h0 := levelEleven_fractional_39424
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39424 256 =
      2603999930347534659969379 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39424 128 128
      1325615083210124940554642 1278384847137409719414737 h0 levelEleven_fractional_39552
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39424 384 =
      3807444865919877498457249 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39424 256 128
      2603999930347534659969379 1203444935572342838487870 h1 levelEleven_fractional_39680
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39424 512 =
      4711082818341425409921381 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39424 384 128
      3807444865919877498457249 903637952421547911464132 h2 levelEleven_fractional_39808
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_77 : ∀ i : Fin 512,
    levelEleven.lookup (39424 + i.val) ≤ levelElevenRoots.lookup (39424 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_39424
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 39424 128 128
    h0 levelEleven_squares_39552
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 39424 256 128
    h1 levelEleven_squares_39680
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 39424 384 128
    h2 levelEleven_squares_39808
  exact h3

end WordCertDensity.Certificates
