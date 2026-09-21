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
theorem levelEleven_energy_141312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 141312 128 =
      69889452579145793590178896768018 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_141312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141312 128 =
      1485754038491743626406795 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_141312 : ∀ i : Fin 128,
    levelEleven.lookup (141312 + i.val) ≤ levelElevenRoots.lookup (141312 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_141440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 141440 128 =
      12696201037231080352238600652890 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_141440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141440 128 =
      532874604790154420955596 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_141440 : ∀ i : Fin 128,
    levelEleven.lookup (141440 + i.val) ≤ levelElevenRoots.lookup (141440 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_141568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 141568 128 =
      55668946675333666793596875381344 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_141568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141568 128 =
      1278401291193050359994591 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_141568 : ∀ i : Fin 128,
    levelEleven.lookup (141568 + i.val) ≤ levelElevenRoots.lookup (141568 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_141696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 141696 128 =
      31193321659251046386231931515321 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_141696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141696 128 =
      901045489754981178516125 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_141696 : ∀ i : Fin 128,
    levelEleven.lookup (141696 + i.val) ≤ levelElevenRoots.lookup (141696 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_276 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 141312 512 =
      169447921950961587122246304317573 := by
  have h0 := levelEleven_energy_141312
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 141312 256 =
      82585653616376873942417497420908 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 141312 128 128
      69889452579145793590178896768018 12696201037231080352238600652890 h0 levelEleven_energy_141440
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 141312 384 =
      138254600291710540736014372802252 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 141312 256 128
      82585653616376873942417497420908 55668946675333666793596875381344 h1 levelEleven_energy_141568
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 141312 512 =
      169447921950961587122246304317573 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 141312 384 128
      138254600291710540736014372802252 31193321659251046386231931515321 h2 levelEleven_energy_141696
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_276 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141312 512 =
      4198075424229929585873107 := by
  have h0 := levelEleven_fractional_141312
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141312 256 =
      2018628643281898047362391 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141312 128 128
      1485754038491743626406795 532874604790154420955596 h0 levelEleven_fractional_141440
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141312 384 =
      3297029934474948407356982 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141312 256 128
      2018628643281898047362391 1278401291193050359994591 h1 levelEleven_fractional_141568
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141312 512 =
      4198075424229929585873107 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 141312 384 128
      3297029934474948407356982 901045489754981178516125 h2 levelEleven_fractional_141696
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_276 : ∀ i : Fin 512,
    levelEleven.lookup (141312 + i.val) ≤ levelElevenRoots.lookup (141312 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_141312
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 141312 128 128
    h0 levelEleven_squares_141440
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 141312 256 128
    h1 levelEleven_squares_141568
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 141312 384 128
    h2 levelEleven_squares_141696
  exact h3

end WordCertDensity.Certificates
