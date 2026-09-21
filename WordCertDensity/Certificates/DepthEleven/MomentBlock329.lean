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
theorem levelEleven_energy_168448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 168448 128 =
      41625143761609120358755267370340 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_168448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168448 128 =
      1109777278252848571768696 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_168448 : ∀ i : Fin 128,
    levelEleven.lookup (168448 + i.val) ≤ levelElevenRoots.lookup (168448 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_168576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 168576 128 =
      101326373519294109981453663494838 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_168576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168576 128 =
      1667652328047963953070027 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_168576 : ∀ i : Fin 128,
    levelEleven.lookup (168576 + i.val) ≤ levelElevenRoots.lookup (168576 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_168704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 168704 128 =
      38531130349329753783644821608562 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_168704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168704 128 =
      1106154489911706551882446 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_168704 : ∀ i : Fin 128,
    levelEleven.lookup (168704 + i.val) ≤ levelElevenRoots.lookup (168704 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_168832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 168832 128 =
      195746025996488247532917981239596 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_168832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168832 128 =
      2209379584260927839932153 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_168832 : ∀ i : Fin 128,
    levelEleven.lookup (168832 + i.val) ≤ levelElevenRoots.lookup (168832 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_329 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 168448 512 =
      377228673626721231656771733713336 := by
  have h0 := levelEleven_energy_168448
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 168448 256 =
      142951517280903230340208930865178 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 168448 128 128
      41625143761609120358755267370340 101326373519294109981453663494838 h0 levelEleven_energy_168576
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 168448 384 =
      181482647630232984123853752473740 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 168448 256 128
      142951517280903230340208930865178 38531130349329753783644821608562 h1 levelEleven_energy_168704
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 168448 512 =
      377228673626721231656771733713336 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 168448 384 128
      181482647630232984123853752473740 195746025996488247532917981239596 h2 levelEleven_energy_168832
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_329 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168448 512 =
      6092963680473446916653322 := by
  have h0 := levelEleven_fractional_168448
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168448 256 =
      2777429606300812524838723 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168448 128 128
      1109777278252848571768696 1667652328047963953070027 h0 levelEleven_fractional_168576
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168448 384 =
      3883584096212519076721169 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168448 256 128
      2777429606300812524838723 1106154489911706551882446 h1 levelEleven_fractional_168704
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168448 512 =
      6092963680473446916653322 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 168448 384 128
      3883584096212519076721169 2209379584260927839932153 h2 levelEleven_fractional_168832
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_329 : ∀ i : Fin 512,
    levelEleven.lookup (168448 + i.val) ≤ levelElevenRoots.lookup (168448 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_168448
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 168448 128 128
    h0 levelEleven_squares_168576
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 168448 256 128
    h1 levelEleven_squares_168704
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 168448 384 128
    h2 levelEleven_squares_168832
  exact h3

end WordCertDensity.Certificates
