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
theorem levelEleven_energy_5632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 5632 128 =
      51847195195998160988647913216067 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_5632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5632 128 =
      1185358779538908858751193 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_5632 : ∀ i : Fin 128,
    levelEleven.lookup (5632 + i.val) ≤ levelElevenRoots.lookup (5632 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_5760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 5760 128 =
      35307758354004800147450999172274 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_5760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5760 128 =
      967695241511731444713726 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_5760 : ∀ i : Fin 128,
    levelEleven.lookup (5760 + i.val) ≤ levelElevenRoots.lookup (5760 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_5888 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 5888 128 =
      35821906898456893943599858445940 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_5888 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5888 128 =
      972766669846704034278954 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_5888 : ∀ i : Fin 128,
    levelEleven.lookup (5888 + i.val) ≤ levelElevenRoots.lookup (5888 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_6016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 6016 128 =
      54663709396082108586201134196730 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_6016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6016 128 =
      1251382604416563249180813 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_6016 : ∀ i : Fin 128,
    levelEleven.lookup (6016 + i.val) ≤ levelElevenRoots.lookup (6016 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_11 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 5632 512 =
      177640569844541963665899905031011 := by
  have h0 := levelEleven_energy_5632
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 5632 256 =
      87154953550002961136098912388341 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 5632 128 128
      51847195195998160988647913216067 35307758354004800147450999172274 h0 levelEleven_energy_5760
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 5632 384 =
      122976860448459855079698770834281 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 5632 256 128
      87154953550002961136098912388341 35821906898456893943599858445940 h1 levelEleven_energy_5888
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 5632 512 =
      177640569844541963665899905031011 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 5632 384 128
      122976860448459855079698770834281 54663709396082108586201134196730 h2 levelEleven_energy_6016
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_11 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5632 512 =
      4377203295313907586924686 := by
  have h0 := levelEleven_fractional_5632
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5632 256 =
      2153054021050640303464919 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5632 128 128
      1185358779538908858751193 967695241511731444713726 h0 levelEleven_fractional_5760
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5632 384 =
      3125820690897344337743873 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5632 256 128
      2153054021050640303464919 972766669846704034278954 h1 levelEleven_fractional_5888
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5632 512 =
      4377203295313907586924686 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5632 384 128
      3125820690897344337743873 1251382604416563249180813 h2 levelEleven_fractional_6016
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_11 : ∀ i : Fin 512,
    levelEleven.lookup (5632 + i.val) ≤ levelElevenRoots.lookup (5632 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_5632
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 5632 128 128
    h0 levelEleven_squares_5760
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 5632 256 128
    h1 levelEleven_squares_5888
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 5632 384 128
    h2 levelEleven_squares_6016
  exact h3

end WordCertDensity.Certificates
