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
theorem levelEleven_energy_4096 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 4096 128 =
      15825355715964938233132643943132 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_4096 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4096 128 =
      616301212820852598236748 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_4096 : ∀ i : Fin 128,
    levelEleven.lookup (4096 + i.val) ≤ levelElevenRoots.lookup (4096 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_4224 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 4224 128 =
      69582489707223700041938560694586 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_4224 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4224 128 =
      1574545313510423188504399 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_4224 : ∀ i : Fin 128,
    levelEleven.lookup (4224 + i.val) ≤ levelElevenRoots.lookup (4224 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_4352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 4352 128 =
      17678307987538637131875548136420 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_4352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4352 128 =
      638240335239404102453081 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_4352 : ∀ i : Fin 128,
    levelEleven.lookup (4352 + i.val) ≤ levelElevenRoots.lookup (4352 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_4480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 4480 128 =
      52136340311445856208704015973994 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_4480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4480 128 =
      1341458502649233227449676 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_4480 : ∀ i : Fin 128,
    levelEleven.lookup (4480 + i.val) ≤ levelElevenRoots.lookup (4480 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_8 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 4096 512 =
      155222493722173131615650768748132 := by
  have h0 := levelEleven_energy_4096
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 4096 256 =
      85407845423188638275071204637718 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 4096 128 128
      15825355715964938233132643943132 69582489707223700041938560694586 h0 levelEleven_energy_4224
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 4096 384 =
      103086153410727275406946752774138 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 4096 256 128
      85407845423188638275071204637718 17678307987538637131875548136420 h1 levelEleven_energy_4352
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 4096 512 =
      155222493722173131615650768748132 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 4096 384 128
      103086153410727275406946752774138 52136340311445856208704015973994 h2 levelEleven_energy_4480
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_8 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4096 512 =
      4170545364219913116643904 := by
  have h0 := levelEleven_fractional_4096
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4096 256 =
      2190846526331275786741147 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4096 128 128
      616301212820852598236748 1574545313510423188504399 h0 levelEleven_fractional_4224
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4096 384 =
      2829086861570679889194228 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4096 256 128
      2190846526331275786741147 638240335239404102453081 h1 levelEleven_fractional_4352
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4096 512 =
      4170545364219913116643904 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4096 384 128
      2829086861570679889194228 1341458502649233227449676 h2 levelEleven_fractional_4480
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_8 : ∀ i : Fin 512,
    levelEleven.lookup (4096 + i.val) ≤ levelElevenRoots.lookup (4096 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_4096
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 4096 128 128
    h0 levelEleven_squares_4224
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 4096 256 128
    h1 levelEleven_squares_4352
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 4096 384 128
    h2 levelEleven_squares_4480
  exact h3

end WordCertDensity.Certificates
