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
theorem levelEleven_energy_16384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 16384 128 =
      86297132260778771819736072484144 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_16384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16384 128 =
      1500811795143407893757674 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_16384 : ∀ i : Fin 128,
    levelEleven.lookup (16384 + i.val) ≤ levelElevenRoots.lookup (16384 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_16512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 16512 128 =
      24830821030853671848742626887831 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_16512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16512 128 =
      845207580172481012298939 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_16512 : ∀ i : Fin 128,
    levelEleven.lookup (16512 + i.val) ≤ levelElevenRoots.lookup (16512 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_16640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 16640 128 =
      86120491528740601575740065411140 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_16640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16640 128 =
      1681604864736594831212962 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_16640 : ∀ i : Fin 128,
    levelEleven.lookup (16640 + i.val) ≤ levelElevenRoots.lookup (16640 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_16768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 16768 128 =
      20651459659756067812383437591733 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_16768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16768 128 =
      697265353442616219003686 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_16768 : ∀ i : Fin 128,
    levelEleven.lookup (16768 + i.val) ≤ levelElevenRoots.lookup (16768 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_32 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 16384 512 =
      217899904480129113056602202374848 := by
  have h0 := levelEleven_energy_16384
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 16384 256 =
      111127953291632443668478699371975 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 16384 128 128
      86297132260778771819736072484144 24830821030853671848742626887831 h0 levelEleven_energy_16512
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 16384 384 =
      197248444820373045244218764783115 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 16384 256 128
      111127953291632443668478699371975 86120491528740601575740065411140 h1 levelEleven_energy_16640
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 16384 512 =
      217899904480129113056602202374848 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 16384 384 128
      197248444820373045244218764783115 20651459659756067812383437591733 h2 levelEleven_energy_16768
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_32 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16384 512 =
      4724889593495099956273261 := by
  have h0 := levelEleven_fractional_16384
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16384 256 =
      2346019375315888906056613 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16384 128 128
      1500811795143407893757674 845207580172481012298939 h0 levelEleven_fractional_16512
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16384 384 =
      4027624240052483737269575 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16384 256 128
      2346019375315888906056613 1681604864736594831212962 h1 levelEleven_fractional_16640
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16384 512 =
      4724889593495099956273261 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 16384 384 128
      4027624240052483737269575 697265353442616219003686 h2 levelEleven_fractional_16768
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_32 : ∀ i : Fin 512,
    levelEleven.lookup (16384 + i.val) ≤ levelElevenRoots.lookup (16384 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_16384
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 16384 128 128
    h0 levelEleven_squares_16512
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 16384 256 128
    h1 levelEleven_squares_16640
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 16384 384 128
    h2 levelEleven_squares_16768
  exact h3

end WordCertDensity.Certificates
