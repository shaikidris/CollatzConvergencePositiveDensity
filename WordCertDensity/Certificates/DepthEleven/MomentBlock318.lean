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
theorem levelEleven_energy_162816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 162816 128 =
      30688040339022073107958376924640 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_162816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162816 128 =
      920479907538794192751562 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_162816 : ∀ i : Fin 128,
    levelEleven.lookup (162816 + i.val) ≤ levelElevenRoots.lookup (162816 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_162944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 162944 128 =
      27206966201477558367495642826869 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_162944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162944 128 =
      841658277598133390354780 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_162944 : ∀ i : Fin 128,
    levelEleven.lookup (162944 + i.val) ≤ levelElevenRoots.lookup (162944 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_163072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 163072 128 =
      35515843912719735327808606169925 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_163072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163072 128 =
      961068825937580345218342 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_163072 : ∀ i : Fin 128,
    levelEleven.lookup (163072 + i.val) ≤ levelElevenRoots.lookup (163072 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_163200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 163200 128 =
      74941706731310371735922028409466 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_163200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163200 128 =
      1489987053123710924162904 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_163200 : ∀ i : Fin 128,
    levelEleven.lookup (163200 + i.val) ≤ levelElevenRoots.lookup (163200 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_318 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 162816 512 =
      168352557184529738539184654330900 := by
  have h0 := levelEleven_energy_162816
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 162816 256 =
      57895006540499631475454019751509 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 162816 128 128
      30688040339022073107958376924640 27206966201477558367495642826869 h0 levelEleven_energy_162944
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 162816 384 =
      93410850453219366803262625921434 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 162816 256 128
      57895006540499631475454019751509 35515843912719735327808606169925 h1 levelEleven_energy_163072
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 162816 512 =
      168352557184529738539184654330900 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 162816 384 128
      93410850453219366803262625921434 74941706731310371735922028409466 h2 levelEleven_energy_163200
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_318 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162816 512 =
      4213194064198218852487588 := by
  have h0 := levelEleven_fractional_162816
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162816 256 =
      1762138185136927583106342 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162816 128 128
      920479907538794192751562 841658277598133390354780 h0 levelEleven_fractional_162944
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162816 384 =
      2723207011074507928324684 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162816 256 128
      1762138185136927583106342 961068825937580345218342 h1 levelEleven_fractional_163072
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162816 512 =
      4213194064198218852487588 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 162816 384 128
      2723207011074507928324684 1489987053123710924162904 h2 levelEleven_fractional_163200
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_318 : ∀ i : Fin 512,
    levelEleven.lookup (162816 + i.val) ≤ levelElevenRoots.lookup (162816 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_162816
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 162816 128 128
    h0 levelEleven_squares_162944
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 162816 256 128
    h1 levelEleven_squares_163072
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 162816 384 128
    h2 levelEleven_squares_163200
  exact h3

end WordCertDensity.Certificates
