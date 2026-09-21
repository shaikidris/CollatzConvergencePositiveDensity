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
theorem levelEleven_energy_163328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 163328 128 =
      18603738936267902871705872199488 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_163328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163328 128 =
      669478707599865809495236 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_163328 : ∀ i : Fin 128,
    levelEleven.lookup (163328 + i.val) ≤ levelElevenRoots.lookup (163328 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_163456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 163456 128 =
      59661125886786721908330199380480 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_163456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163456 128 =
      1413720892747318074840579 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_163456 : ∀ i : Fin 128,
    levelEleven.lookup (163456 + i.val) ≤ levelElevenRoots.lookup (163456 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_163584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 163584 128 =
      72465130278098124240455913964774 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_163584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163584 128 =
      1280043513949503328467063 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_163584 : ∀ i : Fin 128,
    levelEleven.lookup (163584 + i.val) ≤ levelElevenRoots.lookup (163584 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_163712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 163712 128 =
      23535390699401568011978319253419 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_163712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163712 128 =
      815185709111974666125444 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_163712 : ∀ i : Fin 128,
    levelEleven.lookup (163712 + i.val) ≤ levelElevenRoots.lookup (163712 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_319 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 163328 512 =
      174265385800554317032470304798161 := by
  have h0 := levelEleven_energy_163328
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 163328 256 =
      78264864823054624780036071579968 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 163328 128 128
      18603738936267902871705872199488 59661125886786721908330199380480 h0 levelEleven_energy_163456
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 163328 384 =
      150729995101152749020491985544742 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 163328 256 128
      78264864823054624780036071579968 72465130278098124240455913964774 h1 levelEleven_energy_163584
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 163328 512 =
      174265385800554317032470304798161 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 163328 384 128
      150729995101152749020491985544742 23535390699401568011978319253419 h2 levelEleven_energy_163712
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_319 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163328 512 =
      4178428823408661878928322 := by
  have h0 := levelEleven_fractional_163328
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163328 256 =
      2083199600347183884335815 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163328 128 128
      669478707599865809495236 1413720892747318074840579 h0 levelEleven_fractional_163456
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163328 384 =
      3363243114296687212802878 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163328 256 128
      2083199600347183884335815 1280043513949503328467063 h1 levelEleven_fractional_163584
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163328 512 =
      4178428823408661878928322 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 163328 384 128
      3363243114296687212802878 815185709111974666125444 h2 levelEleven_fractional_163712
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_319 : ∀ i : Fin 512,
    levelEleven.lookup (163328 + i.val) ≤ levelElevenRoots.lookup (163328 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_163328
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 163328 128 128
    h0 levelEleven_squares_163456
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 163328 256 128
    h1 levelEleven_squares_163584
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 163328 384 128
    h2 levelEleven_squares_163712
  exact h3

end WordCertDensity.Certificates
