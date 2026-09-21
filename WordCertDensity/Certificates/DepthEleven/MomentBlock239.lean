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
theorem levelEleven_energy_122368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 122368 128 =
      84690836818057086228968247256689 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_122368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122368 128 =
      1695445763968159881847468 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_122368 : ∀ i : Fin 128,
    levelEleven.lookup (122368 + i.val) ≤ levelElevenRoots.lookup (122368 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_122496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 122496 128 =
      22634975339046074725697518860975 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_122496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122496 128 =
      718111404026503474386600 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_122496 : ∀ i : Fin 128,
    levelEleven.lookup (122496 + i.val) ≤ levelElevenRoots.lookup (122496 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_122624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 122624 128 =
      277550511352285482553143241741510 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_122624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122624 128 =
      2959671075766270610700427 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_122624 : ∀ i : Fin 128,
    levelEleven.lookup (122624 + i.val) ≤ levelElevenRoots.lookup (122624 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_122752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 122752 128 =
      34161380373370642093163912129470 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_122752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122752 128 =
      921545646300642658857791 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_122752 : ∀ i : Fin 128,
    levelEleven.lookup (122752 + i.val) ≤ levelElevenRoots.lookup (122752 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_239 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 122368 512 =
      419037703882759285600972919988644 := by
  have h0 := levelEleven_energy_122368
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 122368 256 =
      107325812157103160954665766117664 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 122368 128 128
      84690836818057086228968247256689 22634975339046074725697518860975 h0 levelEleven_energy_122496
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 122368 384 =
      384876323509388643507809007859174 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 122368 256 128
      107325812157103160954665766117664 277550511352285482553143241741510 h1 levelEleven_energy_122624
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 122368 512 =
      419037703882759285600972919988644 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 122368 384 128
      384876323509388643507809007859174 34161380373370642093163912129470 h2 levelEleven_energy_122752
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_239 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122368 512 =
      6294773890061576625792286 := by
  have h0 := levelEleven_fractional_122368
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122368 256 =
      2413557167994663356234068 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122368 128 128
      1695445763968159881847468 718111404026503474386600 h0 levelEleven_fractional_122496
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122368 384 =
      5373228243760933966934495 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122368 256 128
      2413557167994663356234068 2959671075766270610700427 h1 levelEleven_fractional_122624
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122368 512 =
      6294773890061576625792286 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122368 384 128
      5373228243760933966934495 921545646300642658857791 h2 levelEleven_fractional_122752
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_239 : ∀ i : Fin 512,
    levelEleven.lookup (122368 + i.val) ≤ levelElevenRoots.lookup (122368 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_122368
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 122368 128 128
    h0 levelEleven_squares_122496
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 122368 256 128
    h1 levelEleven_squares_122624
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 122368 384 128
    h2 levelEleven_squares_122752
  exact h3

end WordCertDensity.Certificates
