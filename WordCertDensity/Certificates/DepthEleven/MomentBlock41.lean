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
theorem levelEleven_energy_20992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 20992 128 =
      41493707944948981038377362165200 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_20992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20992 128 =
      1069812699335807766668943 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_20992 : ∀ i : Fin 128,
    levelEleven.lookup (20992 + i.val) ≤ levelElevenRoots.lookup (20992 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_21120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 21120 128 =
      26938422525161752768935122070771 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_21120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21120 128 =
      780364431935645767074156 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_21120 : ∀ i : Fin 128,
    levelEleven.lookup (21120 + i.val) ≤ levelElevenRoots.lookup (21120 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_21248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 21248 128 =
      82048993748104973304443920556538 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_21248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21248 128 =
      1648669266834192350739428 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_21248 : ∀ i : Fin 128,
    levelEleven.lookup (21248 + i.val) ≤ levelElevenRoots.lookup (21248 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_21376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 21376 128 =
      28235043373733721426219217210171 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_21376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 21376 128 =
      893805717775013636060196 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_21376 : ∀ i : Fin 128,
    levelEleven.lookup (21376 + i.val) ≤ levelElevenRoots.lookup (21376 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_41 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 20992 512 =
      178716167591949428537975622002680 := by
  have h0 := levelEleven_energy_20992
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 20992 256 =
      68432130470110733807312484235971 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 20992 128 128
      41493707944948981038377362165200 26938422525161752768935122070771 h0 levelEleven_energy_21120
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 20992 384 =
      150481124218215707111756404792509 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 20992 256 128
      68432130470110733807312484235971 82048993748104973304443920556538 h1 levelEleven_energy_21248
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 20992 512 =
      178716167591949428537975622002680 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 20992 384 128
      150481124218215707111756404792509 28235043373733721426219217210171 h2 levelEleven_energy_21376
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_41 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20992 512 =
      4392652115880659520542723 := by
  have h0 := levelEleven_fractional_20992
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20992 256 =
      1850177131271453533743099 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20992 128 128
      1069812699335807766668943 780364431935645767074156 h0 levelEleven_fractional_21120
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20992 384 =
      3498846398105645884482527 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20992 256 128
      1850177131271453533743099 1648669266834192350739428 h1 levelEleven_fractional_21248
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20992 512 =
      4392652115880659520542723 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20992 384 128
      3498846398105645884482527 893805717775013636060196 h2 levelEleven_fractional_21376
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_41 : ∀ i : Fin 512,
    levelEleven.lookup (20992 + i.val) ≤ levelElevenRoots.lookup (20992 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_20992
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 20992 128 128
    h0 levelEleven_squares_21120
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 20992 256 128
    h1 levelEleven_squares_21248
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 20992 384 128
    h2 levelEleven_squares_21376
  exact h3

end WordCertDensity.Certificates
