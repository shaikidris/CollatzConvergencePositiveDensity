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
theorem levelEleven_energy_62976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 62976 128 =
      33116505291702851596619354595713 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_62976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62976 128 =
      934448570459763126586167 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_62976 : ∀ i : Fin 128,
    levelEleven.lookup (62976 + i.val) ≤ levelElevenRoots.lookup (62976 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_63104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 63104 128 =
      26282521652594614639876842303178 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_63104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63104 128 =
      877167639544962937259351 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_63104 : ∀ i : Fin 128,
    levelEleven.lookup (63104 + i.val) ≤ levelElevenRoots.lookup (63104 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_63232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 63232 128 =
      65984297929748589460116687125552 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_63232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63232 128 =
      1449069283935824811677876 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_63232 : ∀ i : Fin 128,
    levelEleven.lookup (63232 + i.val) ≤ levelElevenRoots.lookup (63232 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_63360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 63360 128 =
      30836676553753801500850858316557 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_63360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 63360 128 =
      890380338597962006005215 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_63360 : ∀ i : Fin 128,
    levelEleven.lookup (63360 + i.val) ≤ levelElevenRoots.lookup (63360 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_123 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 62976 512 =
      156220001427799857197463742341000 := by
  have h0 := levelEleven_energy_62976
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 62976 256 =
      59399026944297466236496196898891 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 62976 128 128
      33116505291702851596619354595713 26282521652594614639876842303178 h0 levelEleven_energy_63104
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 62976 384 =
      125383324874046055696612884024443 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 62976 256 128
      59399026944297466236496196898891 65984297929748589460116687125552 h1 levelEleven_energy_63232
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 62976 512 =
      156220001427799857197463742341000 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 62976 384 128
      125383324874046055696612884024443 30836676553753801500850858316557 h2 levelEleven_energy_63360
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_123 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62976 512 =
      4151065832538512881528609 := by
  have h0 := levelEleven_fractional_62976
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62976 256 =
      1811616210004726063845518 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62976 128 128
      934448570459763126586167 877167639544962937259351 h0 levelEleven_fractional_63104
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62976 384 =
      3260685493940550875523394 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62976 256 128
      1811616210004726063845518 1449069283935824811677876 h1 levelEleven_fractional_63232
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62976 512 =
      4151065832538512881528609 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62976 384 128
      3260685493940550875523394 890380338597962006005215 h2 levelEleven_fractional_63360
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_123 : ∀ i : Fin 512,
    levelEleven.lookup (62976 + i.val) ≤ levelElevenRoots.lookup (62976 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_62976
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 62976 128 128
    h0 levelEleven_squares_63104
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 62976 256 128
    h1 levelEleven_squares_63232
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 62976 384 128
    h2 levelEleven_squares_63360
  exact h3

end WordCertDensity.Certificates
