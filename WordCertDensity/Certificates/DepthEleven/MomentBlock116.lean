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
theorem levelEleven_energy_59392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 59392 128 =
      75014883222409272356915166267868 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_59392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59392 128 =
      1584358076315413644888123 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_59392 : ∀ i : Fin 128,
    levelEleven.lookup (59392 + i.val) ≤ levelElevenRoots.lookup (59392 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_59520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 59520 128 =
      35778484794793276461970656244996 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_59520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59520 128 =
      1035584539015092883522908 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_59520 : ∀ i : Fin 128,
    levelEleven.lookup (59520 + i.val) ≤ levelElevenRoots.lookup (59520 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_59648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 59648 128 =
      59089662801599431941098003283649 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_59648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59648 128 =
      1329517823329255451190173 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_59648 : ∀ i : Fin 128,
    levelEleven.lookup (59648 + i.val) ≤ levelElevenRoots.lookup (59648 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_59776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 59776 128 =
      39033306416373103066300854353613 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_59776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59776 128 =
      948008863930568016281415 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_59776 : ∀ i : Fin 128,
    levelEleven.lookup (59776 + i.val) ≤ levelElevenRoots.lookup (59776 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_116 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 59392 512 =
      208916337235175083826284680150126 := by
  have h0 := levelEleven_energy_59392
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 59392 256 =
      110793368017202548818885822512864 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 59392 128 128
      75014883222409272356915166267868 35778484794793276461970656244996 h0 levelEleven_energy_59520
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 59392 384 =
      169883030818801980759983825796513 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 59392 256 128
      110793368017202548818885822512864 59089662801599431941098003283649 h1 levelEleven_energy_59648
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 59392 512 =
      208916337235175083826284680150126 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 59392 384 128
      169883030818801980759983825796513 39033306416373103066300854353613 h2 levelEleven_energy_59776
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_116 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59392 512 =
      4897469302590329995882619 := by
  have h0 := levelEleven_fractional_59392
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59392 256 =
      2619942615330506528411031 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59392 128 128
      1584358076315413644888123 1035584539015092883522908 h0 levelEleven_fractional_59520
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59392 384 =
      3949460438659761979601204 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59392 256 128
      2619942615330506528411031 1329517823329255451190173 h1 levelEleven_fractional_59648
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59392 512 =
      4897469302590329995882619 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59392 384 128
      3949460438659761979601204 948008863930568016281415 h2 levelEleven_fractional_59776
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_116 : ∀ i : Fin 512,
    levelEleven.lookup (59392 + i.val) ≤ levelElevenRoots.lookup (59392 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_59392
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 59392 128 128
    h0 levelEleven_squares_59520
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 59392 256 128
    h1 levelEleven_squares_59648
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 59392 384 128
    h2 levelEleven_squares_59776
  exact h3

end WordCertDensity.Certificates
