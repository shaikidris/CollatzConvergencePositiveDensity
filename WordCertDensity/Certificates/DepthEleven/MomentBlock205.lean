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
theorem levelEleven_energy_104960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 104960 128 =
      46308860386913047229033906797625 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_104960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104960 128 =
      1096320209762435889612298 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_104960 : ∀ i : Fin 128,
    levelEleven.lookup (104960 + i.val) ≤ levelElevenRoots.lookup (104960 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_105088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 105088 128 =
      256553929652209700657030752129399 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_105088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105088 128 =
      3165646235493914020258823 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_105088 : ∀ i : Fin 128,
    levelEleven.lookup (105088 + i.val) ≤ levelElevenRoots.lookup (105088 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_105216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 105216 128 =
      38883389085569565703228098968245 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_105216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105216 128 =
      1081244816507401455363697 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_105216 : ∀ i : Fin 128,
    levelEleven.lookup (105216 + i.val) ≤ levelElevenRoots.lookup (105216 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_105344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 105344 128 =
      48570225312376061544694892641563 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_105344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105344 128 =
      1256986842902320587395968 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_105344 : ∀ i : Fin 128,
    levelEleven.lookup (105344 + i.val) ≤ levelElevenRoots.lookup (105344 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_205 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 104960 512 =
      390316404437068375133987650536832 := by
  have h0 := levelEleven_energy_104960
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 104960 256 =
      302862790039122747886064658927024 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 104960 128 128
      46308860386913047229033906797625 256553929652209700657030752129399 h0 levelEleven_energy_105088
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 104960 384 =
      341746179124692313589292757895269 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 104960 256 128
      302862790039122747886064658927024 38883389085569565703228098968245 h1 levelEleven_energy_105216
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 104960 512 =
      390316404437068375133987650536832 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 104960 384 128
      341746179124692313589292757895269 48570225312376061544694892641563 h2 levelEleven_energy_105344
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_205 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104960 512 =
      6600198104666071952630786 := by
  have h0 := levelEleven_fractional_104960
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104960 256 =
      4261966445256349909871121 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104960 128 128
      1096320209762435889612298 3165646235493914020258823 h0 levelEleven_fractional_105088
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104960 384 =
      5343211261763751365234818 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104960 256 128
      4261966445256349909871121 1081244816507401455363697 h1 levelEleven_fractional_105216
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104960 512 =
      6600198104666071952630786 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104960 384 128
      5343211261763751365234818 1256986842902320587395968 h2 levelEleven_fractional_105344
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_205 : ∀ i : Fin 512,
    levelEleven.lookup (104960 + i.val) ≤ levelElevenRoots.lookup (104960 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_104960
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 104960 128 128
    h0 levelEleven_squares_105088
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 104960 256 128
    h1 levelEleven_squares_105216
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 104960 384 128
    h2 levelEleven_squares_105344
  exact h3

end WordCertDensity.Certificates
