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
theorem levelEleven_energy_113152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 113152 128 =
      141216071353970868924143432804426 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_113152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113152 128 =
      2123560976497193544987166 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_113152 : ∀ i : Fin 128,
    levelEleven.lookup (113152 + i.val) ≤ levelElevenRoots.lookup (113152 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_113280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 113280 128 =
      89051151871415920412045584995954 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_113280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113280 128 =
      1612494779842760156935363 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_113280 : ∀ i : Fin 128,
    levelEleven.lookup (113280 + i.val) ≤ levelElevenRoots.lookup (113280 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_113408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 113408 128 =
      46555773764582900472732747228099 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_113408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113408 128 =
      1187345510261843803113082 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_113408 : ∀ i : Fin 128,
    levelEleven.lookup (113408 + i.val) ≤ levelElevenRoots.lookup (113408 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_113536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 113536 128 =
      68668759474046216324641225489411 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_113536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113536 128 =
      1513658700463338640424612 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_113536 : ∀ i : Fin 128,
    levelEleven.lookup (113536 + i.val) ≤ levelElevenRoots.lookup (113536 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_221 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 113152 512 =
      345491756464015906133562990517890 := by
  have h0 := levelEleven_energy_113152
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 113152 256 =
      230267223225386789336189017800380 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 113152 128 128
      141216071353970868924143432804426 89051151871415920412045584995954 h0 levelEleven_energy_113280
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 113152 384 =
      276822996989969689808921765028479 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 113152 256 128
      230267223225386789336189017800380 46555773764582900472732747228099 h1 levelEleven_energy_113408
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 113152 512 =
      345491756464015906133562990517890 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 113152 384 128
      276822996989969689808921765028479 68668759474046216324641225489411 h2 levelEleven_energy_113536
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_221 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113152 512 =
      6437059967065136145460223 := by
  have h0 := levelEleven_fractional_113152
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113152 256 =
      3736055756339953701922529 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113152 128 128
      2123560976497193544987166 1612494779842760156935363 h0 levelEleven_fractional_113280
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113152 384 =
      4923401266601797505035611 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113152 256 128
      3736055756339953701922529 1187345510261843803113082 h1 levelEleven_fractional_113408
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113152 512 =
      6437059967065136145460223 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113152 384 128
      4923401266601797505035611 1513658700463338640424612 h2 levelEleven_fractional_113536
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_221 : ∀ i : Fin 512,
    levelEleven.lookup (113152 + i.val) ≤ levelElevenRoots.lookup (113152 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_113152
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 113152 128 128
    h0 levelEleven_squares_113280
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 113152 256 128
    h1 levelEleven_squares_113408
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 113152 384 128
    h2 levelEleven_squares_113536
  exact h3

end WordCertDensity.Certificates
