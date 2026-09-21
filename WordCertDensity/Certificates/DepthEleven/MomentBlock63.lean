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
theorem levelEleven_energy_32256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 32256 128 =
      34078191416305055787977346435733 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_32256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32256 128 =
      917756634054979555226281 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_32256 : ∀ i : Fin 128,
    levelEleven.lookup (32256 + i.val) ≤ levelElevenRoots.lookup (32256 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_32384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 32384 128 =
      50888590608216482504344268778210 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_32384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32384 128 =
      1193728610535005350127253 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_32384 : ∀ i : Fin 128,
    levelEleven.lookup (32384 + i.val) ≤ levelElevenRoots.lookup (32384 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_32512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 32512 128 =
      71965843851039904009788455650393 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_32512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32512 128 =
      1364141050354005462932440 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_32512 : ∀ i : Fin 128,
    levelEleven.lookup (32512 + i.val) ≤ levelElevenRoots.lookup (32512 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_32640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 32640 128 =
      53045507063558349755872274618143 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_32640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32640 128 =
      1283417404504923957930341 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_32640 : ∀ i : Fin 128,
    levelEleven.lookup (32640 + i.val) ≤ levelElevenRoots.lookup (32640 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_63 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 32256 512 =
      209978132939119792057982345482479 := by
  have h0 := levelEleven_energy_32256
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 32256 256 =
      84966782024521538292321615213943 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 32256 128 128
      34078191416305055787977346435733 50888590608216482504344268778210 h0 levelEleven_energy_32384
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 32256 384 =
      156932625875561442302110070864336 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 32256 256 128
      84966782024521538292321615213943 71965843851039904009788455650393 h1 levelEleven_energy_32512
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 32256 512 =
      209978132939119792057982345482479 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 32256 384 128
      156932625875561442302110070864336 53045507063558349755872274618143 h2 levelEleven_energy_32640
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_63 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32256 512 =
      4759043699448914326216315 := by
  have h0 := levelEleven_fractional_32256
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32256 256 =
      2111485244589984905353534 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32256 128 128
      917756634054979555226281 1193728610535005350127253 h0 levelEleven_fractional_32384
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32256 384 =
      3475626294943990368285974 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32256 256 128
      2111485244589984905353534 1364141050354005462932440 h1 levelEleven_fractional_32512
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32256 512 =
      4759043699448914326216315 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 32256 384 128
      3475626294943990368285974 1283417404504923957930341 h2 levelEleven_fractional_32640
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_63 : ∀ i : Fin 512,
    levelEleven.lookup (32256 + i.val) ≤ levelElevenRoots.lookup (32256 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_32256
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 32256 128 128
    h0 levelEleven_squares_32384
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 32256 256 128
    h1 levelEleven_squares_32512
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 32256 384 128
    h2 levelEleven_squares_32640
  exact h3

end WordCertDensity.Certificates
