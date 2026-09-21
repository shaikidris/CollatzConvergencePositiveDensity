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
theorem levelEleven_energy_13824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 13824 128 =
      202420810480431137816344381691073 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_13824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13824 128 =
      2257792633083947995048554 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_13824 : ∀ i : Fin 128,
    levelEleven.lookup (13824 + i.val) ≤ levelElevenRoots.lookup (13824 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_13952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 13952 128 =
      48634749976253566175175184367976 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_13952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13952 128 =
      1250148147617652929735651 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_13952 : ∀ i : Fin 128,
    levelEleven.lookup (13952 + i.val) ≤ levelElevenRoots.lookup (13952 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_14080 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 14080 128 =
      39668471059985459747181763920808 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_14080 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14080 128 =
      1073349427768028096483814 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_14080 : ∀ i : Fin 128,
    levelEleven.lookup (14080 + i.val) ≤ levelElevenRoots.lookup (14080 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_14208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 14208 128 =
      34568118365429587154741176267717 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_14208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14208 128 =
      1010427610038138571265058 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_14208 : ∀ i : Fin 128,
    levelEleven.lookup (14208 + i.val) ≤ levelElevenRoots.lookup (14208 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_27 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 13824 512 =
      325292149882099750893442506247574 := by
  have h0 := levelEleven_energy_13824
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 13824 256 =
      251055560456684703991519566059049 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 13824 128 128
      202420810480431137816344381691073 48634749976253566175175184367976 h0 levelEleven_energy_13952
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 13824 384 =
      290724031516670163738701329979857 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 13824 256 128
      251055560456684703991519566059049 39668471059985459747181763920808 h1 levelEleven_energy_14080
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 13824 512 =
      325292149882099750893442506247574 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 13824 384 128
      290724031516670163738701329979857 34568118365429587154741176267717 h2 levelEleven_energy_14208
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_27 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13824 512 =
      5591717818507767592533077 := by
  have h0 := levelEleven_fractional_13824
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13824 256 =
      3507940780701600924784205 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13824 128 128
      2257792633083947995048554 1250148147617652929735651 h0 levelEleven_fractional_13952
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13824 384 =
      4581290208469629021268019 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13824 256 128
      3507940780701600924784205 1073349427768028096483814 h1 levelEleven_fractional_14080
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13824 512 =
      5591717818507767592533077 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13824 384 128
      4581290208469629021268019 1010427610038138571265058 h2 levelEleven_fractional_14208
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_27 : ∀ i : Fin 512,
    levelEleven.lookup (13824 + i.val) ≤ levelElevenRoots.lookup (13824 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_13824
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 13824 128 128
    h0 levelEleven_squares_13952
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 13824 256 128
    h1 levelEleven_squares_14080
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 13824 384 128
    h2 levelEleven_squares_14208
  exact h3

end WordCertDensity.Certificates
