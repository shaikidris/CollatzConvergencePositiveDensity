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
theorem levelEleven_energy_152576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 152576 128 =
      46618967799956447305902636564252 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_152576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152576 128 =
      1214095526177942011820450 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_152576 : ∀ i : Fin 128,
    levelEleven.lookup (152576 + i.val) ≤ levelElevenRoots.lookup (152576 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_152704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 152704 128 =
      33233037851646426325766168656356 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_152704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152704 128 =
      984731611068663249589151 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_152704 : ∀ i : Fin 128,
    levelEleven.lookup (152704 + i.val) ≤ levelElevenRoots.lookup (152704 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_152832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 152832 128 =
      83431734494805943930885783718981 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_152832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152832 128 =
      1559283062694063015983736 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_152832 : ∀ i : Fin 128,
    levelEleven.lookup (152832 + i.val) ≤ levelElevenRoots.lookup (152832 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_152960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 152960 128 =
      48117016817628675614213957257674 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_152960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152960 128 =
      1180717821810992149962261 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_152960 : ∀ i : Fin 128,
    levelEleven.lookup (152960 + i.val) ≤ levelElevenRoots.lookup (152960 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_298 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 152576 512 =
      211400756964037493176768546197263 := by
  have h0 := levelEleven_energy_152576
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 152576 256 =
      79852005651602873631668805220608 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 152576 128 128
      46618967799956447305902636564252 33233037851646426325766168656356 h0 levelEleven_energy_152704
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 152576 384 =
      163283740146408817562554588939589 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 152576 256 128
      79852005651602873631668805220608 83431734494805943930885783718981 h1 levelEleven_energy_152832
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 152576 512 =
      211400756964037493176768546197263 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 152576 384 128
      163283740146408817562554588939589 48117016817628675614213957257674 h2 levelEleven_energy_152960
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_298 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152576 512 =
      4938828021751660427355598 := by
  have h0 := levelEleven_fractional_152576
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152576 256 =
      2198827137246605261409601 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152576 128 128
      1214095526177942011820450 984731611068663249589151 h0 levelEleven_fractional_152704
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152576 384 =
      3758110199940668277393337 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152576 256 128
      2198827137246605261409601 1559283062694063015983736 h1 levelEleven_fractional_152832
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152576 512 =
      4938828021751660427355598 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 152576 384 128
      3758110199940668277393337 1180717821810992149962261 h2 levelEleven_fractional_152960
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_298 : ∀ i : Fin 512,
    levelEleven.lookup (152576 + i.val) ≤ levelElevenRoots.lookup (152576 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_152576
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 152576 128 128
    h0 levelEleven_squares_152704
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 152576 256 128
    h1 levelEleven_squares_152832
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 152576 384 128
    h2 levelEleven_squares_152960
  exact h3

end WordCertDensity.Certificates
