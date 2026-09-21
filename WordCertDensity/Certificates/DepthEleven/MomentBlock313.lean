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
theorem levelEleven_energy_160256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 160256 128 =
      85361270337459399809908345678866 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_160256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160256 128 =
      1588408226227931147569286 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_160256 : ∀ i : Fin 128,
    levelEleven.lookup (160256 + i.val) ≤ levelElevenRoots.lookup (160256 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_160384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 160384 128 =
      21215473392984366215274679723235 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_160384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160384 128 =
      707493913329219115199161 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_160384 : ∀ i : Fin 128,
    levelEleven.lookup (160384 + i.val) ≤ levelElevenRoots.lookup (160384 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_160512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 160512 128 =
      748422792090076015536751272324773 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_160512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160512 128 =
      5343230844050630567663458 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_160512 : ∀ i : Fin 128,
    levelEleven.lookup (160512 + i.val) ≤ levelElevenRoots.lookup (160512 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_160640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 160640 128 =
      49928649437683681719162470864853 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_160640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160640 128 =
      1175211492391737477308851 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_160640 : ∀ i : Fin 128,
    levelEleven.lookup (160640 + i.val) ≤ levelElevenRoots.lookup (160640 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_313 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 160256 512 =
      904928185258203463281096768591727 := by
  have h0 := levelEleven_energy_160256
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 160256 256 =
      106576743730443766025183025402101 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 160256 128 128
      85361270337459399809908345678866 21215473392984366215274679723235 h0 levelEleven_energy_160384
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 160256 384 =
      854999535820519781561934297726874 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 160256 256 128
      106576743730443766025183025402101 748422792090076015536751272324773 h1 levelEleven_energy_160512
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 160256 512 =
      904928185258203463281096768591727 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 160256 384 128
      854999535820519781561934297726874 49928649437683681719162470864853 h2 levelEleven_energy_160640
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_313 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160256 512 =
      8814344475999518307740756 := by
  have h0 := levelEleven_fractional_160256
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160256 256 =
      2295902139557150262768447 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160256 128 128
      1588408226227931147569286 707493913329219115199161 h0 levelEleven_fractional_160384
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160256 384 =
      7639132983607780830431905 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160256 256 128
      2295902139557150262768447 5343230844050630567663458 h1 levelEleven_fractional_160512
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160256 512 =
      8814344475999518307740756 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160256 384 128
      7639132983607780830431905 1175211492391737477308851 h2 levelEleven_fractional_160640
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_313 : ∀ i : Fin 512,
    levelEleven.lookup (160256 + i.val) ≤ levelElevenRoots.lookup (160256 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_160256
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 160256 128 128
    h0 levelEleven_squares_160384
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 160256 256 128
    h1 levelEleven_squares_160512
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 160256 384 128
    h2 levelEleven_squares_160640
  exact h3

end WordCertDensity.Certificates
