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
theorem levelEleven_energy_74240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 74240 128 =
      151505262204279132703172110480235 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_74240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74240 128 =
      2299143238424586873329975 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_74240 : ∀ i : Fin 128,
    levelEleven.lookup (74240 + i.val) ≤ levelElevenRoots.lookup (74240 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_74368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 74368 128 =
      65882433667429223730323590847951 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_74368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74368 128 =
      1217612275913385753461011 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_74368 : ∀ i : Fin 128,
    levelEleven.lookup (74368 + i.val) ≤ levelElevenRoots.lookup (74368 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_74496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 74496 128 =
      104527321599753386568293016695462 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_74496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74496 128 =
      1816174411591308651616025 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_74496 : ∀ i : Fin 128,
    levelEleven.lookup (74496 + i.val) ≤ levelElevenRoots.lookup (74496 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_74624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 74624 128 =
      65939547373040775957592244052823 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_74624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74624 128 =
      1239490182087017809485139 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_74624 : ∀ i : Fin 128,
    levelEleven.lookup (74624 + i.val) ≤ levelElevenRoots.lookup (74624 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_145 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 74240 512 =
      387854564844502518959380962076471 := by
  have h0 := levelEleven_energy_74240
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 74240 256 =
      217387695871708356433495701328186 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 74240 128 128
      151505262204279132703172110480235 65882433667429223730323590847951 h0 levelEleven_energy_74368
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 74240 384 =
      321915017471461743001788718023648 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 74240 256 128
      217387695871708356433495701328186 104527321599753386568293016695462 h1 levelEleven_energy_74496
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 74240 512 =
      387854564844502518959380962076471 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 74240 384 128
      321915017471461743001788718023648 65939547373040775957592244052823 h2 levelEleven_energy_74624
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_145 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74240 512 =
      6572420108016299087892150 := by
  have h0 := levelEleven_fractional_74240
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74240 256 =
      3516755514337972626790986 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74240 128 128
      2299143238424586873329975 1217612275913385753461011 h0 levelEleven_fractional_74368
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74240 384 =
      5332929925929281278407011 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74240 256 128
      3516755514337972626790986 1816174411591308651616025 h1 levelEleven_fractional_74496
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74240 512 =
      6572420108016299087892150 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 74240 384 128
      5332929925929281278407011 1239490182087017809485139 h2 levelEleven_fractional_74624
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_145 : ∀ i : Fin 512,
    levelEleven.lookup (74240 + i.val) ≤ levelElevenRoots.lookup (74240 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_74240
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 74240 128 128
    h0 levelEleven_squares_74368
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 74240 256 128
    h1 levelEleven_squares_74496
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 74240 384 128
    h2 levelEleven_squares_74624
  exact h3

end WordCertDensity.Certificates
