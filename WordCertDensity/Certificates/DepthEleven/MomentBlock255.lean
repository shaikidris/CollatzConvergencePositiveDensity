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
theorem levelEleven_energy_130560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 130560 128 =
      57818108475133988970650314550315 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_130560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130560 128 =
      1231375915823956935361404 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_130560 : ∀ i : Fin 128,
    levelEleven.lookup (130560 + i.val) ≤ levelElevenRoots.lookup (130560 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_130688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 130688 128 =
      36322573831296043613013103514169 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_130688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130688 128 =
      1006986207223971543575078 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_130688 : ∀ i : Fin 128,
    levelEleven.lookup (130688 + i.val) ≤ levelElevenRoots.lookup (130688 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_130816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 130816 128 =
      44317952505890224387289656596384 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_130816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130816 128 =
      1139178724714189760158786 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_130816 : ∀ i : Fin 128,
    levelEleven.lookup (130816 + i.val) ≤ levelElevenRoots.lookup (130816 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_130944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 130944 128 =
      35105960277578492936084679828867 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_130944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130944 128 =
      951448698596273274274373 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_130944 : ∀ i : Fin 128,
    levelEleven.lookup (130944 + i.val) ≤ levelElevenRoots.lookup (130944 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_255 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 130560 512 =
      173564595089898749907037754489735 := by
  have h0 := levelEleven_energy_130560
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 130560 256 =
      94140682306430032583663418064484 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 130560 128 128
      57818108475133988970650314550315 36322573831296043613013103514169 h0 levelEleven_energy_130688
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 130560 384 =
      138458634812320256970953074660868 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 130560 256 128
      94140682306430032583663418064484 44317952505890224387289656596384 h1 levelEleven_energy_130816
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 130560 512 =
      173564595089898749907037754489735 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 130560 384 128
      138458634812320256970953074660868 35105960277578492936084679828867 h2 levelEleven_energy_130944
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_255 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130560 512 =
      4328989546358391513369641 := by
  have h0 := levelEleven_fractional_130560
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130560 256 =
      2238362123047928478936482 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130560 128 128
      1231375915823956935361404 1006986207223971543575078 h0 levelEleven_fractional_130688
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130560 384 =
      3377540847762118239095268 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130560 256 128
      2238362123047928478936482 1139178724714189760158786 h1 levelEleven_fractional_130816
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130560 512 =
      4328989546358391513369641 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 130560 384 128
      3377540847762118239095268 951448698596273274274373 h2 levelEleven_fractional_130944
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_255 : ∀ i : Fin 512,
    levelEleven.lookup (130560 + i.val) ≤ levelElevenRoots.lookup (130560 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_130560
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 130560 128 128
    h0 levelEleven_squares_130688
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 130560 256 128
    h1 levelEleven_squares_130816
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 130560 384 128
    h2 levelEleven_squares_130944
  exact h3

end WordCertDensity.Certificates
