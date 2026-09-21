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
theorem levelEleven_energy_67584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 67584 128 =
      65564342592219089584043986220350 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_67584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67584 128 =
      1203905281216871157574479 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_67584 : ∀ i : Fin 128,
    levelEleven.lookup (67584 + i.val) ≤ levelElevenRoots.lookup (67584 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_67712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 67712 128 =
      87474002827775336213097063926801 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_67712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67712 128 =
      1719286276427429843295491 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_67712 : ∀ i : Fin 128,
    levelEleven.lookup (67712 + i.val) ≤ levelElevenRoots.lookup (67712 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_67840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 67840 128 =
      31496242624904142956823065872097 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_67840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67840 128 =
      966538528016904786241133 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_67840 : ∀ i : Fin 128,
    levelEleven.lookup (67840 + i.val) ≤ levelElevenRoots.lookup (67840 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_67968 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 67968 128 =
      51908755575261605292306504328239 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_67968 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67968 128 =
      1227172219081411565776531 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_67968 : ∀ i : Fin 128,
    levelEleven.lookup (67968 + i.val) ≤ levelElevenRoots.lookup (67968 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_132 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 67584 512 =
      236443343620160174046270620347487 := by
  have h0 := levelEleven_energy_67584
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 67584 256 =
      153038345419994425797141050147151 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 67584 128 128
      65564342592219089584043986220350 87474002827775336213097063926801 h0 levelEleven_energy_67712
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 67584 384 =
      184534588044898568753964116019248 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 67584 256 128
      153038345419994425797141050147151 31496242624904142956823065872097 h1 levelEleven_energy_67840
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 67584 512 =
      236443343620160174046270620347487 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 67584 384 128
      184534588044898568753964116019248 51908755575261605292306504328239 h2 levelEleven_energy_67968
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_132 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67584 512 =
      5116902304742617352887634 := by
  have h0 := levelEleven_fractional_67584
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67584 256 =
      2923191557644301000869970 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67584 128 128
      1203905281216871157574479 1719286276427429843295491 h0 levelEleven_fractional_67712
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67584 384 =
      3889730085661205787111103 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67584 256 128
      2923191557644301000869970 966538528016904786241133 h1 levelEleven_fractional_67840
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67584 512 =
      5116902304742617352887634 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 67584 384 128
      3889730085661205787111103 1227172219081411565776531 h2 levelEleven_fractional_67968
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_132 : ∀ i : Fin 512,
    levelEleven.lookup (67584 + i.val) ≤ levelElevenRoots.lookup (67584 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_67584
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 67584 128 128
    h0 levelEleven_squares_67712
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 67584 256 128
    h1 levelEleven_squares_67840
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 67584 384 128
    h2 levelEleven_squares_67968
  exact h3

end WordCertDensity.Certificates
