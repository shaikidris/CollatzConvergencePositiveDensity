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
theorem levelEleven_energy_33792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 33792 128 =
      44119393468846651484250710614287 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_33792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33792 128 =
      1065301980774336247706883 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_33792 : ∀ i : Fin 128,
    levelEleven.lookup (33792 + i.val) ≤ levelElevenRoots.lookup (33792 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_33920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 33920 128 =
      24429840642283189588020414588451 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_33920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33920 128 =
      841471845437440984536259 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_33920 : ∀ i : Fin 128,
    levelEleven.lookup (33920 + i.val) ≤ levelElevenRoots.lookup (33920 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_34048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 34048 128 =
      66879962935583134999266691249998 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_34048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34048 128 =
      1342333266102458593506451 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_34048 : ∀ i : Fin 128,
    levelEleven.lookup (34048 + i.val) ≤ levelElevenRoots.lookup (34048 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_34176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 34176 128 =
      224616301386059816668524493995318 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_34176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 34176 128 =
      2543594509778202362456717 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_34176 : ∀ i : Fin 128,
    levelEleven.lookup (34176 + i.val) ≤ levelElevenRoots.lookup (34176 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_66 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 33792 512 =
      360045498432772792740062310448054 := by
  have h0 := levelEleven_energy_33792
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 33792 256 =
      68549234111129841072271125202738 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 33792 128 128
      44119393468846651484250710614287 24429840642283189588020414588451 h0 levelEleven_energy_33920
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 33792 384 =
      135429197046712976071537816452736 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 33792 256 128
      68549234111129841072271125202738 66879962935583134999266691249998 h1 levelEleven_energy_34048
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 33792 512 =
      360045498432772792740062310448054 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 33792 384 128
      135429197046712976071537816452736 224616301386059816668524493995318 h2 levelEleven_energy_34176
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_66 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33792 512 =
      5792701602092438188206310 := by
  have h0 := levelEleven_fractional_33792
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33792 256 =
      1906773826211777232243142 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33792 128 128
      1065301980774336247706883 841471845437440984536259 h0 levelEleven_fractional_33920
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33792 384 =
      3249107092314235825749593 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33792 256 128
      1906773826211777232243142 1342333266102458593506451 h1 levelEleven_fractional_34048
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33792 512 =
      5792701602092438188206310 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33792 384 128
      3249107092314235825749593 2543594509778202362456717 h2 levelEleven_fractional_34176
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_66 : ∀ i : Fin 512,
    levelEleven.lookup (33792 + i.val) ≤ levelElevenRoots.lookup (33792 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_33792
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 33792 128 128
    h0 levelEleven_squares_33920
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 33792 256 128
    h1 levelEleven_squares_34048
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 33792 384 128
    h2 levelEleven_squares_34176
  exact h3

end WordCertDensity.Certificates
