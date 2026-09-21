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
theorem levelEleven_energy_46592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 46592 128 =
      57681908942918006369019189478355 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_46592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46592 128 =
      1185485103535634029152729 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_46592 : ∀ i : Fin 128,
    levelEleven.lookup (46592 + i.val) ≤ levelElevenRoots.lookup (46592 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_46720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 46720 128 =
      35697033664786691013311902128512 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_46720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46720 128 =
      1014581178264543519252194 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_46720 : ∀ i : Fin 128,
    levelEleven.lookup (46720 + i.val) ≤ levelElevenRoots.lookup (46720 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_46848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 46848 128 =
      38346898483136713831146677953252 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_46848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46848 128 =
      962437036461168549212221 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_46848 : ∀ i : Fin 128,
    levelEleven.lookup (46848 + i.val) ≤ levelElevenRoots.lookup (46848 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_46976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 46976 128 =
      82886612700796958462174381967604 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_46976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46976 128 =
      1475601127603385547786570 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_46976 : ∀ i : Fin 128,
    levelEleven.lookup (46976 + i.val) ≤ levelElevenRoots.lookup (46976 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_91 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 46592 512 =
      214612453791638369675652151527723 := by
  have h0 := levelEleven_energy_46592
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 46592 256 =
      93378942607704697382331091606867 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 46592 128 128
      57681908942918006369019189478355 35697033664786691013311902128512 h0 levelEleven_energy_46720
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 46592 384 =
      131725841090841411213477769560119 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 46592 256 128
      93378942607704697382331091606867 38346898483136713831146677953252 h1 levelEleven_energy_46848
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 46592 512 =
      214612453791638369675652151527723 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 46592 384 128
      131725841090841411213477769560119 82886612700796958462174381967604 h2 levelEleven_energy_46976
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_91 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46592 512 =
      4638104445864731645403714 := by
  have h0 := levelEleven_fractional_46592
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46592 256 =
      2200066281800177548404923 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46592 128 128
      1185485103535634029152729 1014581178264543519252194 h0 levelEleven_fractional_46720
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46592 384 =
      3162503318261346097617144 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46592 256 128
      2200066281800177548404923 962437036461168549212221 h1 levelEleven_fractional_46848
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46592 512 =
      4638104445864731645403714 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 46592 384 128
      3162503318261346097617144 1475601127603385547786570 h2 levelEleven_fractional_46976
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_91 : ∀ i : Fin 512,
    levelEleven.lookup (46592 + i.val) ≤ levelElevenRoots.lookup (46592 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_46592
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 46592 128 128
    h0 levelEleven_squares_46720
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 46592 256 128
    h1 levelEleven_squares_46848
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 46592 384 128
    h2 levelEleven_squares_46976
  exact h3

end WordCertDensity.Certificates
