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
theorem levelEleven_energy_93184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 93184 128 =
      91742180182058901997142059334841 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_93184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93184 128 =
      1725055743282366167189916 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_93184 : ∀ i : Fin 128,
    levelEleven.lookup (93184 + i.val) ≤ levelElevenRoots.lookup (93184 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_93312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 93312 128 =
      65946306357544070537658418875167 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_93312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93312 128 =
      1177715846623700371217754 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_93312 : ∀ i : Fin 128,
    levelEleven.lookup (93312 + i.val) ≤ levelElevenRoots.lookup (93312 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_93440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 93440 128 =
      79674800927006398066617461642271 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_93440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93440 128 =
      1590667581863114063666327 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_93440 : ∀ i : Fin 128,
    levelEleven.lookup (93440 + i.val) ≤ levelElevenRoots.lookup (93440 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_93568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 93568 128 =
      41204924556353632801430634657577 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_93568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93568 128 =
      1083800496047413687323662 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_93568 : ∀ i : Fin 128,
    levelEleven.lookup (93568 + i.val) ≤ levelElevenRoots.lookup (93568 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_182 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 93184 512 =
      278568212022963003402848574509856 := by
  have h0 := levelEleven_energy_93184
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 93184 256 =
      157688486539602972534800478210008 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 93184 128 128
      91742180182058901997142059334841 65946306357544070537658418875167 h0 levelEleven_energy_93312
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 93184 384 =
      237363287466609370601417939852279 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 93184 256 128
      157688486539602972534800478210008 79674800927006398066617461642271 h1 levelEleven_energy_93440
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 93184 512 =
      278568212022963003402848574509856 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 93184 384 128
      237363287466609370601417939852279 41204924556353632801430634657577 h2 levelEleven_energy_93568
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_182 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93184 512 =
      5577239667816594289397659 := by
  have h0 := levelEleven_fractional_93184
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93184 256 =
      2902771589906066538407670 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93184 128 128
      1725055743282366167189916 1177715846623700371217754 h0 levelEleven_fractional_93312
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93184 384 =
      4493439171769180602073997 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93184 256 128
      2902771589906066538407670 1590667581863114063666327 h1 levelEleven_fractional_93440
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93184 512 =
      5577239667816594289397659 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 93184 384 128
      4493439171769180602073997 1083800496047413687323662 h2 levelEleven_fractional_93568
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_182 : ∀ i : Fin 512,
    levelEleven.lookup (93184 + i.val) ≤ levelElevenRoots.lookup (93184 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_93184
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 93184 128 128
    h0 levelEleven_squares_93312
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 93184 256 128
    h1 levelEleven_squares_93440
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 93184 384 128
    h2 levelEleven_squares_93568
  exact h3

end WordCertDensity.Certificates
