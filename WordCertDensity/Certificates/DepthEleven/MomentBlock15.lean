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
theorem levelEleven_energy_7680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 7680 128 =
      35934466961487347058562078162524 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_7680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7680 128 =
      1015002499870976368749387 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_7680 : ∀ i : Fin 128,
    levelEleven.lookup (7680 + i.val) ≤ levelElevenRoots.lookup (7680 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_7808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 7808 128 =
      34534504928045871214493082288543 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_7808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7808 128 =
      934387106028554863205706 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_7808 : ∀ i : Fin 128,
    levelEleven.lookup (7808 + i.val) ≤ levelElevenRoots.lookup (7808 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_7936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 7936 128 =
      31941427854865892212496430423371 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_7936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7936 128 =
      955967947989042212200316 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_7936 : ∀ i : Fin 128,
    levelEleven.lookup (7936 + i.val) ≤ levelElevenRoots.lookup (7936 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_8064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 8064 128 =
      48462155965924947390014803948426 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_8064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8064 128 =
      1132574089410075506047111 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_8064 : ∀ i : Fin 128,
    levelEleven.lookup (8064 + i.val) ≤ levelElevenRoots.lookup (8064 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_15 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 7680 512 =
      150872555710324057875566394822864 := by
  have h0 := levelEleven_energy_7680
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 7680 256 =
      70468971889533218273055160451067 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 7680 128 128
      35934466961487347058562078162524 34534504928045871214493082288543 h0 levelEleven_energy_7808
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 7680 384 =
      102410399744399110485551590874438 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 7680 256 128
      70468971889533218273055160451067 31941427854865892212496430423371 h1 levelEleven_energy_7936
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 7680 512 =
      150872555710324057875566394822864 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 7680 384 128
      102410399744399110485551590874438 48462155965924947390014803948426 h2 levelEleven_energy_8064
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_15 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7680 512 =
      4037931643298648950202520 := by
  have h0 := levelEleven_fractional_7680
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7680 256 =
      1949389605899531231955093 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7680 128 128
      1015002499870976368749387 934387106028554863205706 h0 levelEleven_fractional_7808
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7680 384 =
      2905357553888573444155409 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7680 256 128
      1949389605899531231955093 955967947989042212200316 h1 levelEleven_fractional_7936
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7680 512 =
      4037931643298648950202520 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 7680 384 128
      2905357553888573444155409 1132574089410075506047111 h2 levelEleven_fractional_8064
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_15 : ∀ i : Fin 512,
    levelEleven.lookup (7680 + i.val) ≤ levelElevenRoots.lookup (7680 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_7680
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 7680 128 128
    h0 levelEleven_squares_7808
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 7680 256 128
    h1 levelEleven_squares_7936
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 7680 384 128
    h2 levelEleven_squares_8064
  exact h3

end WordCertDensity.Certificates
