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
theorem levelEleven_energy_53248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 53248 128 =
      25035188121023572785081390669906 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_53248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53248 128 =
      780121579985367404208885 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_53248 : ∀ i : Fin 128,
    levelEleven.lookup (53248 + i.val) ≤ levelElevenRoots.lookup (53248 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_53376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 53376 128 =
      96477797753562839740386931577758 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_53376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53376 128 =
      1659572462574109558290141 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_53376 : ∀ i : Fin 128,
    levelEleven.lookup (53376 + i.val) ≤ levelElevenRoots.lookup (53376 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_53504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 53504 128 =
      25483867342726029679747564803848 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_53504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53504 128 =
      809320404876514343215657 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_53504 : ∀ i : Fin 128,
    levelEleven.lookup (53504 + i.val) ≤ levelElevenRoots.lookup (53504 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_53632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 53632 128 =
      23042180537198871735768600092952 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_53632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53632 128 =
      810401215631131902506146 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_53632 : ∀ i : Fin 128,
    levelEleven.lookup (53632 + i.val) ≤ levelElevenRoots.lookup (53632 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 53248 512 =
      170039033754511313940984487144464 := by
  have h0 := levelEleven_energy_53248
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 53248 256 =
      121512985874586412525468322247664 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 53248 128 128
      25035188121023572785081390669906 96477797753562839740386931577758 h0 levelEleven_energy_53376
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 53248 384 =
      146996853217312442205215887051512 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 53248 256 128
      121512985874586412525468322247664 25483867342726029679747564803848 h1 levelEleven_energy_53504
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 53248 512 =
      170039033754511313940984487144464 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 53248 384 128
      146996853217312442205215887051512 23042180537198871735768600092952 h2 levelEleven_energy_53632
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53248 512 =
      4059415663067123208220829 := by
  have h0 := levelEleven_fractional_53248
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53248 256 =
      2439694042559476962499026 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53248 128 128
      780121579985367404208885 1659572462574109558290141 h0 levelEleven_fractional_53376
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53248 384 =
      3249014447435991305714683 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53248 256 128
      2439694042559476962499026 809320404876514343215657 h1 levelEleven_fractional_53504
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53248 512 =
      4059415663067123208220829 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53248 384 128
      3249014447435991305714683 810401215631131902506146 h2 levelEleven_fractional_53632
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_104 : ∀ i : Fin 512,
    levelEleven.lookup (53248 + i.val) ≤ levelElevenRoots.lookup (53248 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_53248
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 53248 128 128
    h0 levelEleven_squares_53376
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 53248 256 128
    h1 levelEleven_squares_53504
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 53248 384 128
    h2 levelEleven_squares_53632
  exact h3

end WordCertDensity.Certificates
