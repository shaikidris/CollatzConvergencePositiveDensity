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
theorem levelEleven_energy_156672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 156672 128 =
      34373999933063072361861837788129 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_156672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156672 128 =
      889837491447189717109129 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_156672 : ∀ i : Fin 128,
    levelEleven.lookup (156672 + i.val) ≤ levelElevenRoots.lookup (156672 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_156800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 156800 128 =
      34538837672309556616968229767351 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_156800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156800 128 =
      1027501061088244850472105 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_156800 : ∀ i : Fin 128,
    levelEleven.lookup (156800 + i.val) ≤ levelElevenRoots.lookup (156800 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_156928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 156928 128 =
      53110519077676077872254259266824 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_156928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156928 128 =
      1275741703865615483278694 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_156928 : ∀ i : Fin 128,
    levelEleven.lookup (156928 + i.val) ≤ levelElevenRoots.lookup (156928 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_157056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 157056 128 =
      27827786120940615158804228033754 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_157056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 157056 128 =
      862785135077422080205925 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_157056 : ∀ i : Fin 128,
    levelEleven.lookup (157056 + i.val) ≤ levelElevenRoots.lookup (157056 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_306 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 156672 512 =
      149851142803989322009888554856058 := by
  have h0 := levelEleven_energy_156672
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 156672 256 =
      68912837605372628978830067555480 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 156672 128 128
      34373999933063072361861837788129 34538837672309556616968229767351 h0 levelEleven_energy_156800
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 156672 384 =
      122023356683048706851084326822304 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 156672 256 128
      68912837605372628978830067555480 53110519077676077872254259266824 h1 levelEleven_energy_156928
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 156672 512 =
      149851142803989322009888554856058 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 156672 384 128
      122023356683048706851084326822304 27827786120940615158804228033754 h2 levelEleven_energy_157056
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_306 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156672 512 =
      4055865391478472131065853 := by
  have h0 := levelEleven_fractional_156672
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156672 256 =
      1917338552535434567581234 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156672 128 128
      889837491447189717109129 1027501061088244850472105 h0 levelEleven_fractional_156800
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156672 384 =
      3193080256401050050859928 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156672 256 128
      1917338552535434567581234 1275741703865615483278694 h1 levelEleven_fractional_156928
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156672 512 =
      4055865391478472131065853 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 156672 384 128
      3193080256401050050859928 862785135077422080205925 h2 levelEleven_fractional_157056
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_306 : ∀ i : Fin 512,
    levelEleven.lookup (156672 + i.val) ≤ levelElevenRoots.lookup (156672 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_156672
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 156672 128 128
    h0 levelEleven_squares_156800
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 156672 256 128
    h1 levelEleven_squares_156928
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 156672 384 128
    h2 levelEleven_squares_157056
  exact h3

end WordCertDensity.Certificates
