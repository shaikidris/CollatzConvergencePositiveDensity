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
theorem levelEleven_energy_77824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 77824 128 =
      86583265421833915609227944827371 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_77824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77824 128 =
      1631289373227780530967570 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_77824 : ∀ i : Fin 128,
    levelEleven.lookup (77824 + i.val) ≤ levelElevenRoots.lookup (77824 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_77952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 77952 128 =
      25466669641429525741192829980754 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_77952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77952 128 =
      780515888930860358191156 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_77952 : ∀ i : Fin 128,
    levelEleven.lookup (77952 + i.val) ≤ levelElevenRoots.lookup (77952 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_78080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 78080 128 =
      42189262976291102608518858993813 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_78080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78080 128 =
      1081242496286383841658604 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_78080 : ∀ i : Fin 128,
    levelEleven.lookup (78080 + i.val) ≤ levelElevenRoots.lookup (78080 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_78208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 78208 128 =
      29275479593184288370568080907056 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_78208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 78208 128 =
      879750874724038535659712 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_78208 : ∀ i : Fin 128,
    levelEleven.lookup (78208 + i.val) ≤ levelElevenRoots.lookup (78208 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 77824 512 =
      183514677632738832329507714708994 := by
  have h0 := levelEleven_energy_77824
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 77824 256 =
      112049935063263441350420774808125 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 77824 128 128
      86583265421833915609227944827371 25466669641429525741192829980754 h0 levelEleven_energy_77952
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 77824 384 =
      154239198039554543958939633801938 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 77824 256 128
      112049935063263441350420774808125 42189262976291102608518858993813 h1 levelEleven_energy_78080
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 77824 512 =
      183514677632738832329507714708994 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 77824 384 128
      154239198039554543958939633801938 29275479593184288370568080907056 h2 levelEleven_energy_78208
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77824 512 =
      4372798633169063266477042 := by
  have h0 := levelEleven_fractional_77824
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77824 256 =
      2411805262158640889158726 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77824 128 128
      1631289373227780530967570 780515888930860358191156 h0 levelEleven_fractional_77952
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77824 384 =
      3493047758445024730817330 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77824 256 128
      2411805262158640889158726 1081242496286383841658604 h1 levelEleven_fractional_78080
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77824 512 =
      4372798633169063266477042 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77824 384 128
      3493047758445024730817330 879750874724038535659712 h2 levelEleven_fractional_78208
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_152 : ∀ i : Fin 512,
    levelEleven.lookup (77824 + i.val) ≤ levelElevenRoots.lookup (77824 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_77824
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 77824 128 128
    h0 levelEleven_squares_77952
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 77824 256 128
    h1 levelEleven_squares_78080
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 77824 384 128
    h2 levelEleven_squares_78208
  exact h3

end WordCertDensity.Certificates
