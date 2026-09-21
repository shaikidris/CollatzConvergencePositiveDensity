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
theorem levelEleven_energy_82432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 82432 128 =
      26294213122805377958653219918731 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_82432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82432 128 =
      845580328543894229629444 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_82432 : ∀ i : Fin 128,
    levelEleven.lookup (82432 + i.val) ≤ levelElevenRoots.lookup (82432 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_82560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 82560 128 =
      31462523469454778938658207219017 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_82560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82560 128 =
      894235860384386981840201 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_82560 : ∀ i : Fin 128,
    levelEleven.lookup (82560 + i.val) ≤ levelElevenRoots.lookup (82560 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_82688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 82688 128 =
      49181099864104173354914872842991 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_82688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82688 128 =
      1232903868372777973355294 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_82688 : ∀ i : Fin 128,
    levelEleven.lookup (82688 + i.val) ≤ levelElevenRoots.lookup (82688 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_82816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 82816 128 =
      17277204752016719815495064674292 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_82816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82816 128 =
      659284708001524534043081 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_82816 : ∀ i : Fin 128,
    levelEleven.lookup (82816 + i.val) ≤ levelElevenRoots.lookup (82816 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_161 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 82432 512 =
      124215041208381050067721364655031 := by
  have h0 := levelEleven_energy_82432
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 82432 256 =
      57756736592260156897311427137748 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 82432 128 128
      26294213122805377958653219918731 31462523469454778938658207219017 h0 levelEleven_energy_82560
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 82432 384 =
      106937836456364330252226299980739 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 82432 256 128
      57756736592260156897311427137748 49181099864104173354914872842991 h1 levelEleven_energy_82688
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 82432 512 =
      124215041208381050067721364655031 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 82432 384 128
      106937836456364330252226299980739 17277204752016719815495064674292 h2 levelEleven_energy_82816
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_161 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82432 512 =
      3632004765302583718868020 := by
  have h0 := levelEleven_fractional_82432
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82432 256 =
      1739816188928281211469645 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82432 128 128
      845580328543894229629444 894235860384386981840201 h0 levelEleven_fractional_82560
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82432 384 =
      2972720057301059184824939 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82432 256 128
      1739816188928281211469645 1232903868372777973355294 h1 levelEleven_fractional_82688
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82432 512 =
      3632004765302583718868020 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82432 384 128
      2972720057301059184824939 659284708001524534043081 h2 levelEleven_fractional_82816
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_161 : ∀ i : Fin 512,
    levelEleven.lookup (82432 + i.val) ≤ levelElevenRoots.lookup (82432 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_82432
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 82432 128 128
    h0 levelEleven_squares_82560
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 82432 256 128
    h1 levelEleven_squares_82688
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 82432 384 128
    h2 levelEleven_squares_82816
  exact h3

end WordCertDensity.Certificates
