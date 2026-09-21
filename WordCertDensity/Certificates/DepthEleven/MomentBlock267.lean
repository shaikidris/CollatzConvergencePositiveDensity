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
theorem levelEleven_energy_136704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 136704 128 =
      24501247014658576476215532845333 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_136704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136704 128 =
      810147822380786373220944 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_136704 : ∀ i : Fin 128,
    levelEleven.lookup (136704 + i.val) ≤ levelElevenRoots.lookup (136704 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_136832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 136832 128 =
      40907493520508297429678333836451 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_136832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136832 128 =
      993150811257759264195407 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_136832 : ∀ i : Fin 128,
    levelEleven.lookup (136832 + i.val) ≤ levelElevenRoots.lookup (136832 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_136960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 136960 128 =
      118873893575370240107232306155234 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_136960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136960 128 =
      1887679797792423711100642 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_136960 : ∀ i : Fin 128,
    levelEleven.lookup (136960 + i.val) ≤ levelElevenRoots.lookup (136960 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_137088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 137088 128 =
      31638246518824198857355955937505 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_137088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 137088 128 =
      898666433138196956328079 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_137088 : ∀ i : Fin 128,
    levelEleven.lookup (137088 + i.val) ≤ levelElevenRoots.lookup (137088 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_267 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 136704 512 =
      215920880629361312870482128774523 := by
  have h0 := levelEleven_energy_136704
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 136704 256 =
      65408740535166873905893866681784 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 136704 128 128
      24501247014658576476215532845333 40907493520508297429678333836451 h0 levelEleven_energy_136832
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 136704 384 =
      184282634110537114013126172837018 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 136704 256 128
      65408740535166873905893866681784 118873893575370240107232306155234 h1 levelEleven_energy_136960
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 136704 512 =
      215920880629361312870482128774523 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 136704 384 128
      184282634110537114013126172837018 31638246518824198857355955937505 h2 levelEleven_energy_137088
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_267 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136704 512 =
      4589644864569166304845072 := by
  have h0 := levelEleven_fractional_136704
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136704 256 =
      1803298633638545637416351 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136704 128 128
      810147822380786373220944 993150811257759264195407 h0 levelEleven_fractional_136832
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136704 384 =
      3690978431430969348516993 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136704 256 128
      1803298633638545637416351 1887679797792423711100642 h1 levelEleven_fractional_136960
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136704 512 =
      4589644864569166304845072 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 136704 384 128
      3690978431430969348516993 898666433138196956328079 h2 levelEleven_fractional_137088
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_267 : ∀ i : Fin 512,
    levelEleven.lookup (136704 + i.val) ≤ levelElevenRoots.lookup (136704 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_136704
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 136704 128 128
    h0 levelEleven_squares_136832
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 136704 256 128
    h1 levelEleven_squares_136960
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 136704 384 128
    h2 levelEleven_squares_137088
  exact h3

end WordCertDensity.Certificates
