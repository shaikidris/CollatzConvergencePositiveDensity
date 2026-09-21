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
theorem levelEleven_energy_153600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 153600 128 =
      34469360811318050316476081672262 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_153600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153600 128 =
      847653571025104821768214 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_153600 : ∀ i : Fin 128,
    levelEleven.lookup (153600 + i.val) ≤ levelElevenRoots.lookup (153600 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_153728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 153728 128 =
      38488774498204589916668129747747 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_153728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153728 128 =
      1102501004481816145540824 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_153728 : ∀ i : Fin 128,
    levelEleven.lookup (153728 + i.val) ≤ levelElevenRoots.lookup (153728 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_153856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 153856 128 =
      49064022199243943733410703665884 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_153856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153856 128 =
      1163756676492633772037540 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_153856 : ∀ i : Fin 128,
    levelEleven.lookup (153856 + i.val) ≤ levelElevenRoots.lookup (153856 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_153984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 153984 128 =
      140195720454817436982317133240793 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_153984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153984 128 =
      2073238665174260284800896 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_153984 : ∀ i : Fin 128,
    levelEleven.lookup (153984 + i.val) ≤ levelElevenRoots.lookup (153984 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_300 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 153600 512 =
      262217877963584020948872048326686 := by
  have h0 := levelEleven_energy_153600
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 153600 256 =
      72958135309522640233144211420009 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 153600 128 128
      34469360811318050316476081672262 38488774498204589916668129747747 h0 levelEleven_energy_153728
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 153600 384 =
      122022157508766583966554915085893 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 153600 256 128
      72958135309522640233144211420009 49064022199243943733410703665884 h1 levelEleven_energy_153856
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 153600 512 =
      262217877963584020948872048326686 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 153600 384 128
      122022157508766583966554915085893 140195720454817436982317133240793 h2 levelEleven_energy_153984
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_300 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153600 512 =
      5187149917173815024147474 := by
  have h0 := levelEleven_fractional_153600
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153600 256 =
      1950154575506920967309038 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153600 128 128
      847653571025104821768214 1102501004481816145540824 h0 levelEleven_fractional_153728
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153600 384 =
      3113911251999554739346578 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153600 256 128
      1950154575506920967309038 1163756676492633772037540 h1 levelEleven_fractional_153856
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153600 512 =
      5187149917173815024147474 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153600 384 128
      3113911251999554739346578 2073238665174260284800896 h2 levelEleven_fractional_153984
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_300 : ∀ i : Fin 512,
    levelEleven.lookup (153600 + i.val) ≤ levelElevenRoots.lookup (153600 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_153600
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 153600 128 128
    h0 levelEleven_squares_153728
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 153600 256 128
    h1 levelEleven_squares_153856
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 153600 384 128
    h2 levelEleven_squares_153984
  exact h3

end WordCertDensity.Certificates
