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
theorem levelEleven_energy_59904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 59904 128 =
      39026919229850393531724844445407 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_59904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59904 128 =
      1021492621339079059175444 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_59904 : ∀ i : Fin 128,
    levelEleven.lookup (59904 + i.val) ≤ levelElevenRoots.lookup (59904 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_60032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 60032 128 =
      40303503989515069630177605917335 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_60032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60032 128 =
      1081667529426466117238795 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_60032 : ∀ i : Fin 128,
    levelEleven.lookup (60032 + i.val) ≤ levelElevenRoots.lookup (60032 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_60160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 60160 128 =
      68147243108973869031973403650466 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_60160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60160 128 =
      1256648712269784621868952 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_60160 : ∀ i : Fin 128,
    levelEleven.lookup (60160 + i.val) ≤ levelElevenRoots.lookup (60160 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_60288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 60288 128 =
      17409802866517594992658866909586 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_60288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 60288 128 =
      639206418920670981508060 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_60288 : ∀ i : Fin 128,
    levelEleven.lookup (60288 + i.val) ≤ levelElevenRoots.lookup (60288 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_117 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 59904 512 =
      164887469194856927186534720922794 := by
  have h0 := levelEleven_energy_59904
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 59904 256 =
      79330423219365463161902450362742 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 59904 128 128
      39026919229850393531724844445407 40303503989515069630177605917335 h0 levelEleven_energy_60032
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 59904 384 =
      147477666328339332193875854013208 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 59904 256 128
      79330423219365463161902450362742 68147243108973869031973403650466 h1 levelEleven_energy_60160
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 59904 512 =
      164887469194856927186534720922794 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 59904 384 128
      147477666328339332193875854013208 17409802866517594992658866909586 h2 levelEleven_energy_60288
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_117 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59904 512 =
      3999015281956000779791251 := by
  have h0 := levelEleven_fractional_59904
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59904 256 =
      2103160150765545176414239 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59904 128 128
      1021492621339079059175444 1081667529426466117238795 h0 levelEleven_fractional_60032
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59904 384 =
      3359808863035329798283191 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59904 256 128
      2103160150765545176414239 1256648712269784621868952 h1 levelEleven_fractional_60160
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59904 512 =
      3999015281956000779791251 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 59904 384 128
      3359808863035329798283191 639206418920670981508060 h2 levelEleven_fractional_60288
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_117 : ∀ i : Fin 512,
    levelEleven.lookup (59904 + i.val) ≤ levelElevenRoots.lookup (59904 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_59904
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 59904 128 128
    h0 levelEleven_squares_60032
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 59904 256 128
    h1 levelEleven_squares_60160
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 59904 384 128
    h2 levelEleven_squares_60288
  exact h3

end WordCertDensity.Certificates
