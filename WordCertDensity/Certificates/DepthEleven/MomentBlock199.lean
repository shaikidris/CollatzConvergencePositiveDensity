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
theorem levelEleven_energy_101888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 101888 128 =
      67369956649294055193212667156761 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_101888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101888 128 =
      1429855836093688314895096 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_101888 : ∀ i : Fin 128,
    levelEleven.lookup (101888 + i.val) ≤ levelElevenRoots.lookup (101888 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_102016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 102016 128 =
      50033664092990610502747878803824 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_102016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102016 128 =
      1090642941147319121378311 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_102016 : ∀ i : Fin 128,
    levelEleven.lookup (102016 + i.val) ≤ levelElevenRoots.lookup (102016 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_102144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 102144 128 =
      86870978377957138412807559141230 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_102144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102144 128 =
      1557774791103312095210215 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_102144 : ∀ i : Fin 128,
    levelEleven.lookup (102144 + i.val) ≤ levelElevenRoots.lookup (102144 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_102272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 102272 128 =
      53314611506314057635429187092242 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_102272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102272 128 =
      1160239676564513699259674 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_102272 : ∀ i : Fin 128,
    levelEleven.lookup (102272 + i.val) ≤ levelElevenRoots.lookup (102272 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_199 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 101888 512 =
      257589210626555861744197292194057 := by
  have h0 := levelEleven_energy_101888
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 101888 256 =
      117403620742284665695960545960585 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 101888 128 128
      67369956649294055193212667156761 50033664092990610502747878803824 h0 levelEleven_energy_102016
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 101888 384 =
      204274599120241804108768105101815 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 101888 256 128
      117403620742284665695960545960585 86870978377957138412807559141230 h1 levelEleven_energy_102144
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 101888 512 =
      257589210626555861744197292194057 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 101888 384 128
      204274599120241804108768105101815 53314611506314057635429187092242 h2 levelEleven_energy_102272
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_199 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101888 512 =
      5238513244908833230743296 := by
  have h0 := levelEleven_fractional_101888
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101888 256 =
      2520498777241007436273407 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101888 128 128
      1429855836093688314895096 1090642941147319121378311 h0 levelEleven_fractional_102016
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101888 384 =
      4078273568344319531483622 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101888 256 128
      2520498777241007436273407 1557774791103312095210215 h1 levelEleven_fractional_102144
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101888 512 =
      5238513244908833230743296 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101888 384 128
      4078273568344319531483622 1160239676564513699259674 h2 levelEleven_fractional_102272
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_199 : ∀ i : Fin 512,
    levelEleven.lookup (101888 + i.val) ≤ levelElevenRoots.lookup (101888 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_101888
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 101888 128 128
    h0 levelEleven_squares_102016
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 101888 256 128
    h1 levelEleven_squares_102144
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 101888 384 128
    h2 levelEleven_squares_102272
  exact h3

end WordCertDensity.Certificates
