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
theorem levelEleven_energy_61440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 61440 128 =
      63249150564083011319396864497056 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_61440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61440 128 =
      1334352474260600417676440 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_61440 : ∀ i : Fin 128,
    levelEleven.lookup (61440 + i.val) ≤ levelElevenRoots.lookup (61440 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_61568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 61568 128 =
      29181385311436220771252098186999 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_61568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61568 128 =
      924090235312418327951205 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_61568 : ∀ i : Fin 128,
    levelEleven.lookup (61568 + i.val) ≤ levelElevenRoots.lookup (61568 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_61696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 61696 128 =
      55363017724214628236586888879943 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_61696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61696 128 =
      1296849729996962108650875 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_61696 : ∀ i : Fin 128,
    levelEleven.lookup (61696 + i.val) ≤ levelElevenRoots.lookup (61696 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_61824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 61824 128 =
      31536638498911855624776606094453 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_61824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61824 128 =
      938584753024809373464178 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_61824 : ∀ i : Fin 128,
    levelEleven.lookup (61824 + i.val) ≤ levelElevenRoots.lookup (61824 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 61440 512 =
      179330192098645715952012457658451 := by
  have h0 := levelEleven_energy_61440
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 61440 256 =
      92430535875519232090648962684055 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 61440 128 128
      63249150564083011319396864497056 29181385311436220771252098186999 h0 levelEleven_energy_61568
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 61440 384 =
      147793553599733860327235851563998 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 61440 256 128
      92430535875519232090648962684055 55363017724214628236586888879943 h1 levelEleven_energy_61696
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 61440 512 =
      179330192098645715952012457658451 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 61440 384 128
      147793553599733860327235851563998 31536638498911855624776606094453 h2 levelEleven_energy_61824
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61440 512 =
      4493877192594790227742698 := by
  have h0 := levelEleven_fractional_61440
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61440 256 =
      2258442709573018745627645 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61440 128 128
      1334352474260600417676440 924090235312418327951205 h0 levelEleven_fractional_61568
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61440 384 =
      3555292439569980854278520 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61440 256 128
      2258442709573018745627645 1296849729996962108650875 h1 levelEleven_fractional_61696
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61440 512 =
      4493877192594790227742698 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 61440 384 128
      3555292439569980854278520 938584753024809373464178 h2 levelEleven_fractional_61824
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_120 : ∀ i : Fin 512,
    levelEleven.lookup (61440 + i.val) ≤ levelElevenRoots.lookup (61440 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_61440
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 61440 128 128
    h0 levelEleven_squares_61568
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 61440 256 128
    h1 levelEleven_squares_61696
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 61440 384 128
    h2 levelEleven_squares_61824
  exact h3

end WordCertDensity.Certificates
