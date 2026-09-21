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
theorem levelEleven_energy_26112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 26112 128 =
      63979218381685967788315450597934 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_26112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26112 128 =
      1455526323021703562482860 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_26112 : ∀ i : Fin 128,
    levelEleven.lookup (26112 + i.val) ≤ levelElevenRoots.lookup (26112 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_26240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 26240 128 =
      21617729520585421794511891028886 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_26240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26240 128 =
      707555264156670951993880 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_26240 : ∀ i : Fin 128,
    levelEleven.lookup (26240 + i.val) ≤ levelElevenRoots.lookup (26240 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_26368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 26368 128 =
      61736763807912292009521670371884 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_26368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26368 128 =
      1428257454894194228096149 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_26368 : ∀ i : Fin 128,
    levelEleven.lookup (26368 + i.val) ≤ levelElevenRoots.lookup (26368 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_26496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 26496 128 =
      26543915306546673583812534090664 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_26496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26496 128 =
      826347195929558004697698 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_26496 : ∀ i : Fin 128,
    levelEleven.lookup (26496 + i.val) ≤ levelElevenRoots.lookup (26496 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_51 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 26112 512 =
      173877627016730355176161546089368 := by
  have h0 := levelEleven_energy_26112
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 26112 256 =
      85596947902271389582827341626820 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 26112 128 128
      63979218381685967788315450597934 21617729520585421794511891028886 h0 levelEleven_energy_26240
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 26112 384 =
      147333711710183681592349011998704 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 26112 256 128
      85596947902271389582827341626820 61736763807912292009521670371884 h1 levelEleven_energy_26368
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 26112 512 =
      173877627016730355176161546089368 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 26112 384 128
      147333711710183681592349011998704 26543915306546673583812534090664 h2 levelEleven_energy_26496
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_51 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26112 512 =
      4417686238002126747270587 := by
  have h0 := levelEleven_fractional_26112
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26112 256 =
      2163081587178374514476740 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26112 128 128
      1455526323021703562482860 707555264156670951993880 h0 levelEleven_fractional_26240
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26112 384 =
      3591339042072568742572889 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26112 256 128
      2163081587178374514476740 1428257454894194228096149 h1 levelEleven_fractional_26368
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26112 512 =
      4417686238002126747270587 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 26112 384 128
      3591339042072568742572889 826347195929558004697698 h2 levelEleven_fractional_26496
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_51 : ∀ i : Fin 512,
    levelEleven.lookup (26112 + i.val) ≤ levelElevenRoots.lookup (26112 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_26112
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 26112 128 128
    h0 levelEleven_squares_26240
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 26112 256 128
    h1 levelEleven_squares_26368
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 26112 384 128
    h2 levelEleven_squares_26496
  exact h3

end WordCertDensity.Certificates
