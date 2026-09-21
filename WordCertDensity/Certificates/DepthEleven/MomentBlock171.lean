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
theorem levelEleven_energy_87552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 87552 128 =
      46598436055882237653108458492043 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_87552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87552 128 =
      1220273518450851518976702 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_87552 : ∀ i : Fin 128,
    levelEleven.lookup (87552 + i.val) ≤ levelElevenRoots.lookup (87552 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_87680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 87680 128 =
      25084330161483299613692941829195 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_87680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87680 128 =
      817767957503440193939809 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_87680 : ∀ i : Fin 128,
    levelEleven.lookup (87680 + i.val) ≤ levelElevenRoots.lookup (87680 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_87808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 87808 128 =
      74507604988818189607879054433569 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_87808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87808 128 =
      1401630893233115959766422 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_87808 : ∀ i : Fin 128,
    levelEleven.lookup (87808 + i.val) ≤ levelElevenRoots.lookup (87808 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_87936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 87936 128 =
      26929467931806178048074276244181 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_87936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87936 128 =
      788827136505060915303424 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_87936 : ∀ i : Fin 128,
    levelEleven.lookup (87936 + i.val) ≤ levelElevenRoots.lookup (87936 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_171 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 87552 512 =
      173119839137989904922754730998988 := by
  have h0 := levelEleven_energy_87552
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 87552 256 =
      71682766217365537266801400321238 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 87552 128 128
      46598436055882237653108458492043 25084330161483299613692941829195 h0 levelEleven_energy_87680
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 87552 384 =
      146190371206183726874680454754807 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 87552 256 128
      71682766217365537266801400321238 74507604988818189607879054433569 h1 levelEleven_energy_87808
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 87552 512 =
      173119839137989904922754730998988 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 87552 384 128
      146190371206183726874680454754807 26929467931806178048074276244181 h2 levelEleven_energy_87936
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_171 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87552 512 =
      4228499505692468587986357 := by
  have h0 := levelEleven_fractional_87552
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87552 256 =
      2038041475954291712916511 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87552 128 128
      1220273518450851518976702 817767957503440193939809 h0 levelEleven_fractional_87680
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87552 384 =
      3439672369187407672682933 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87552 256 128
      2038041475954291712916511 1401630893233115959766422 h1 levelEleven_fractional_87808
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87552 512 =
      4228499505692468587986357 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87552 384 128
      3439672369187407672682933 788827136505060915303424 h2 levelEleven_fractional_87936
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_171 : ∀ i : Fin 512,
    levelEleven.lookup (87552 + i.val) ≤ levelElevenRoots.lookup (87552 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_87552
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 87552 128 128
    h0 levelEleven_squares_87680
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 87552 256 128
    h1 levelEleven_squares_87808
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 87552 384 128
    h2 levelEleven_squares_87936
  exact h3

end WordCertDensity.Certificates
