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
theorem levelEleven_energy_110592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 110592 128 =
      741085398592909511135399834011750 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_110592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110592 128 =
      5247794058166296602069648 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_110592 : ∀ i : Fin 128,
    levelEleven.lookup (110592 + i.val) ≤ levelElevenRoots.lookup (110592 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_110720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 110720 128 =
      30715776010126859769921160072940 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_110720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110720 128 =
      939416357214293563924419 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_110720 : ∀ i : Fin 128,
    levelEleven.lookup (110720 + i.val) ≤ levelElevenRoots.lookup (110720 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_110848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 110848 128 =
      25931593837771227451157943560040 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_110848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110848 128 =
      821442183896452724069098 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_110848 : ∀ i : Fin 128,
    levelEleven.lookup (110848 + i.val) ≤ levelElevenRoots.lookup (110848 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_110976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 110976 128 =
      47518198657896579535031431020311 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_110976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110976 128 =
      1152905592214061757461619 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_110976 : ∀ i : Fin 128,
    levelEleven.lookup (110976 + i.val) ≤ levelElevenRoots.lookup (110976 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 110592 512 =
      845250967098704177891510368665041 := by
  have h0 := levelEleven_energy_110592
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 110592 256 =
      771801174603036370905320994084690 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 110592 128 128
      741085398592909511135399834011750 30715776010126859769921160072940 h0 levelEleven_energy_110720
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 110592 384 =
      797732768440807598356478937644730 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 110592 256 128
      771801174603036370905320994084690 25931593837771227451157943560040 h1 levelEleven_energy_110848
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 110592 512 =
      845250967098704177891510368665041 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 110592 384 128
      797732768440807598356478937644730 47518198657896579535031431020311 h2 levelEleven_energy_110976
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110592 512 =
      8161558191491104647524784 := by
  have h0 := levelEleven_fractional_110592
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110592 256 =
      6187210415380590165994067 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110592 128 128
      5247794058166296602069648 939416357214293563924419 h0 levelEleven_fractional_110720
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110592 384 =
      7008652599277042890063165 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110592 256 128
      6187210415380590165994067 821442183896452724069098 h1 levelEleven_fractional_110848
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110592 512 =
      8161558191491104647524784 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 110592 384 128
      7008652599277042890063165 1152905592214061757461619 h2 levelEleven_fractional_110976
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_216 : ∀ i : Fin 512,
    levelEleven.lookup (110592 + i.val) ≤ levelElevenRoots.lookup (110592 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_110592
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 110592 128 128
    h0 levelEleven_squares_110720
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 110592 256 128
    h1 levelEleven_squares_110848
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 110592 384 128
    h2 levelEleven_squares_110976
  exact h3

end WordCertDensity.Certificates
