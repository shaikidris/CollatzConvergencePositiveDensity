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
theorem levelEleven_energy_128000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128000 128 =
      29911886937330355697896265017326 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_128000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128000 128 =
      868916344552013576364218 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_128000 : ∀ i : Fin 128,
    levelEleven.lookup (128000 + i.val) ≤ levelElevenRoots.lookup (128000 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_128128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128128 128 =
      103388005684189554857516417794905 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_128128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128128 128 =
      1894259644338968598624447 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_128128 : ∀ i : Fin 128,
    levelEleven.lookup (128128 + i.val) ≤ levelElevenRoots.lookup (128128 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_128256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128256 128 =
      26247383197056406835318946288205 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_128256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128256 128 =
      752585349950106117591273 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_128256 : ∀ i : Fin 128,
    levelEleven.lookup (128256 + i.val) ≤ levelElevenRoots.lookup (128256 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_128384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128384 128 =
      51238761402923671922610908655046 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_128384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128384 128 =
      1269929653559208600855564 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_128384 : ∀ i : Fin 128,
    levelEleven.lookup (128384 + i.val) ≤ levelElevenRoots.lookup (128384 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_250 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128000 512 =
      210786037221499989313342537755482 := by
  have h0 := levelEleven_energy_128000
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 128000 256 =
      133299892621519910555412682812231 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 128000 128 128
      29911886937330355697896265017326 103388005684189554857516417794905 h0 levelEleven_energy_128128
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 128000 384 =
      159547275818576317390731629100436 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 128000 256 128
      133299892621519910555412682812231 26247383197056406835318946288205 h1 levelEleven_energy_128256
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 128000 512 =
      210786037221499989313342537755482 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 128000 384 128
      159547275818576317390731629100436 51238761402923671922610908655046 h2 levelEleven_energy_128384
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_250 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128000 512 =
      4785690992400296893435502 := by
  have h0 := levelEleven_fractional_128000
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128000 256 =
      2763175988890982174988665 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128000 128 128
      868916344552013576364218 1894259644338968598624447 h0 levelEleven_fractional_128128
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128000 384 =
      3515761338841088292579938 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128000 256 128
      2763175988890982174988665 752585349950106117591273 h1 levelEleven_fractional_128256
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128000 512 =
      4785690992400296893435502 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128000 384 128
      3515761338841088292579938 1269929653559208600855564 h2 levelEleven_fractional_128384
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_250 : ∀ i : Fin 512,
    levelEleven.lookup (128000 + i.val) ≤ levelElevenRoots.lookup (128000 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_128000
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 128000 128 128
    h0 levelEleven_squares_128128
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 128000 256 128
    h1 levelEleven_squares_128256
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 128000 384 128
    h2 levelEleven_squares_128384
  exact h3

end WordCertDensity.Certificates
