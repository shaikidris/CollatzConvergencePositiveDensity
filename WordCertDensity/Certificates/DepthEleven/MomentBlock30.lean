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
theorem levelEleven_energy_15360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 15360 128 =
      34089292599547424309846915769979 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_15360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15360 128 =
      973261643534688496772613 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_15360 : ∀ i : Fin 128,
    levelEleven.lookup (15360 + i.val) ≤ levelElevenRoots.lookup (15360 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_15488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 15488 128 =
      98697370910615462962055053801585 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_15488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15488 128 =
      1696046614841962399860543 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_15488 : ∀ i : Fin 128,
    levelEleven.lookup (15488 + i.val) ≤ levelElevenRoots.lookup (15488 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_15616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 15616 128 =
      34295911146280528485003742114485 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_15616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15616 128 =
      1001428990555749634629362 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_15616 : ∀ i : Fin 128,
    levelEleven.lookup (15616 + i.val) ≤ levelElevenRoots.lookup (15616 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_15744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 15744 128 =
      33646048800869839501916474516805 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_15744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15744 128 =
      869415964010831839360566 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_15744 : ∀ i : Fin 128,
    levelEleven.lookup (15744 + i.val) ≤ levelElevenRoots.lookup (15744 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_30 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 15360 512 =
      200728623457313255258822186202854 := by
  have h0 := levelEleven_energy_15360
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 15360 256 =
      132786663510162887271901969571564 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 15360 128 128
      34089292599547424309846915769979 98697370910615462962055053801585 h0 levelEleven_energy_15488
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 15360 384 =
      167082574656443415756905711686049 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 15360 256 128
      132786663510162887271901969571564 34295911146280528485003742114485 h1 levelEleven_energy_15616
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 15360 512 =
      200728623457313255258822186202854 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 15360 384 128
      167082574656443415756905711686049 33646048800869839501916474516805 h2 levelEleven_energy_15744
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_30 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15360 512 =
      4540153212943232370623084 := by
  have h0 := levelEleven_fractional_15360
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15360 256 =
      2669308258376650896633156 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15360 128 128
      973261643534688496772613 1696046614841962399860543 h0 levelEleven_fractional_15488
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15360 384 =
      3670737248932400531262518 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15360 256 128
      2669308258376650896633156 1001428990555749634629362 h1 levelEleven_fractional_15616
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15360 512 =
      4540153212943232370623084 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15360 384 128
      3670737248932400531262518 869415964010831839360566 h2 levelEleven_fractional_15744
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_30 : ∀ i : Fin 512,
    levelEleven.lookup (15360 + i.val) ≤ levelElevenRoots.lookup (15360 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_15360
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 15360 128 128
    h0 levelEleven_squares_15488
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 15360 256 128
    h1 levelEleven_squares_15616
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 15360 384 128
    h2 levelEleven_squares_15744
  exact h3

end WordCertDensity.Certificates
