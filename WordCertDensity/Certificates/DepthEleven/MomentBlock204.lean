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
theorem levelEleven_energy_104448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 104448 128 =
      37852041458267352319265954679305 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_104448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104448 128 =
      1052104945900467206455135 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_104448 : ∀ i : Fin 128,
    levelEleven.lookup (104448 + i.val) ≤ levelElevenRoots.lookup (104448 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_104576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 104576 128 =
      24728126479906574203842290243678 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_104576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104576 128 =
      847362050675598218886735 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_104576 : ∀ i : Fin 128,
    levelEleven.lookup (104576 + i.val) ≤ levelElevenRoots.lookup (104576 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_104704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 104704 128 =
      23407273162074091548548629017591 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_104704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104704 128 =
      761858138431827558687803 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_104704 : ∀ i : Fin 128,
    levelEleven.lookup (104704 + i.val) ≤ levelElevenRoots.lookup (104704 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_104832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 104832 128 =
      256874334342409280522370490301913 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_104832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104832 128 =
      3082544631459416171095350 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_104832 : ∀ i : Fin 128,
    levelEleven.lookup (104832 + i.val) ≤ levelElevenRoots.lookup (104832 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_204 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 104448 512 =
      342861775442657298594027364242487 := by
  have h0 := levelEleven_energy_104448
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 104448 256 =
      62580167938173926523108244922983 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 104448 128 128
      37852041458267352319265954679305 24728126479906574203842290243678 h0 levelEleven_energy_104576
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 104448 384 =
      85987441100248018071656873940574 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 104448 256 128
      62580167938173926523108244922983 23407273162074091548548629017591 h1 levelEleven_energy_104704
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 104448 512 =
      342861775442657298594027364242487 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 104448 384 128
      85987441100248018071656873940574 256874334342409280522370490301913 h2 levelEleven_energy_104832
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_204 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104448 512 =
      5743869766467309155125023 := by
  have h0 := levelEleven_fractional_104448
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104448 256 =
      1899466996576065425341870 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104448 128 128
      1052104945900467206455135 847362050675598218886735 h0 levelEleven_fractional_104576
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104448 384 =
      2661325135007892984029673 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104448 256 128
      1899466996576065425341870 761858138431827558687803 h1 levelEleven_fractional_104704
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104448 512 =
      5743869766467309155125023 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104448 384 128
      2661325135007892984029673 3082544631459416171095350 h2 levelEleven_fractional_104832
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_204 : ∀ i : Fin 512,
    levelEleven.lookup (104448 + i.val) ≤ levelElevenRoots.lookup (104448 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_104448
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 104448 128 128
    h0 levelEleven_squares_104576
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 104448 256 128
    h1 levelEleven_squares_104704
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 104448 384 128
    h2 levelEleven_squares_104832
  exact h3

end WordCertDensity.Certificates
