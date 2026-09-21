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
theorem levelEleven_energy_34816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 34816 128 =
      107888953026178275677293037899864 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_34816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34816 128 =
      1845699995600156912564636 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_34816 : ∀ i : Fin 128,
    levelEleven.lookup (34816 + i.val) ≤ levelElevenRoots.lookup (34816 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_34944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 34944 128 =
      113065231225400199441598213111799 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_34944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34944 128 =
      1597302134316643672177737 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_34944 : ∀ i : Fin 128,
    levelEleven.lookup (34944 + i.val) ≤ levelElevenRoots.lookup (34944 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_35072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 35072 128 =
      36510161406688487899805796811367 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_35072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35072 128 =
      1050946206198463510161467 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_35072 : ∀ i : Fin 128,
    levelEleven.lookup (35072 + i.val) ≤ levelElevenRoots.lookup (35072 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_35200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 35200 128 =
      31593041467134787238066039361384 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_35200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35200 128 =
      926576052418611278646242 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_35200 : ∀ i : Fin 128,
    levelEleven.lookup (35200 + i.val) ≤ levelElevenRoots.lookup (35200 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_68 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 34816 512 =
      289057387125401750256763087184414 := by
  have h0 := levelEleven_energy_34816
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 34816 256 =
      220954184251578475118891251011663 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 34816 128 128
      107888953026178275677293037899864 113065231225400199441598213111799 h0 levelEleven_energy_34944
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 34816 384 =
      257464345658266963018697047823030 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 34816 256 128
      220954184251578475118891251011663 36510161406688487899805796811367 h1 levelEleven_energy_35072
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 34816 512 =
      289057387125401750256763087184414 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 34816 384 128
      257464345658266963018697047823030 31593041467134787238066039361384 h2 levelEleven_energy_35200
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_68 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34816 512 =
      5420524388533875373550082 := by
  have h0 := levelEleven_fractional_34816
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34816 256 =
      3443002129916800584742373 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34816 128 128
      1845699995600156912564636 1597302134316643672177737 h0 levelEleven_fractional_34944
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34816 384 =
      4493948336115264094903840 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34816 256 128
      3443002129916800584742373 1050946206198463510161467 h1 levelEleven_fractional_35072
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34816 512 =
      5420524388533875373550082 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34816 384 128
      4493948336115264094903840 926576052418611278646242 h2 levelEleven_fractional_35200
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_68 : ∀ i : Fin 512,
    levelEleven.lookup (34816 + i.val) ≤ levelElevenRoots.lookup (34816 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_34816
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 34816 128 128
    h0 levelEleven_squares_34944
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 34816 256 128
    h1 levelEleven_squares_35072
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 34816 384 128
    h2 levelEleven_squares_35200
  exact h3

end WordCertDensity.Certificates
