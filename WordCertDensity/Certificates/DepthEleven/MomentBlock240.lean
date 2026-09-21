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
theorem levelEleven_energy_122880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 122880 128 =
      77934959822281790735394268310505 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_122880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122880 128 =
      1464673751208262556488563 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_122880 : ∀ i : Fin 128,
    levelEleven.lookup (122880 + i.val) ≤ levelElevenRoots.lookup (122880 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_123008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 123008 128 =
      35631635060927073578580161608851 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_123008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123008 128 =
      969715812172161547023024 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_123008 : ∀ i : Fin 128,
    levelEleven.lookup (123008 + i.val) ≤ levelElevenRoots.lookup (123008 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_123136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 123136 128 =
      21950573962408500915391305302834 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_123136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123136 128 =
      724499973956087664173556 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_123136 : ∀ i : Fin 128,
    levelEleven.lookup (123136 + i.val) ≤ levelElevenRoots.lookup (123136 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_123264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 123264 128 =
      35981073237227233694004127972374 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_123264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123264 128 =
      1074179917712433579920412 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_123264 : ∀ i : Fin 128,
    levelEleven.lookup (123264 + i.val) ≤ levelElevenRoots.lookup (123264 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 122880 512 =
      171498242082844598923369863194564 := by
  have h0 := levelEleven_energy_122880
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 122880 256 =
      113566594883208864313974429919356 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 122880 128 128
      77934959822281790735394268310505 35631635060927073578580161608851 h0 levelEleven_energy_123008
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 122880 384 =
      135517168845617365229365735222190 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 122880 256 128
      113566594883208864313974429919356 21950573962408500915391305302834 h1 levelEleven_energy_123136
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 122880 512 =
      171498242082844598923369863194564 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 122880 384 128
      135517168845617365229365735222190 35981073237227233694004127972374 h2 levelEleven_energy_123264
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122880 512 =
      4233069455048945347605555 := by
  have h0 := levelEleven_fractional_122880
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122880 256 =
      2434389563380424103511587 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122880 128 128
      1464673751208262556488563 969715812172161547023024 h0 levelEleven_fractional_123008
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122880 384 =
      3158889537336511767685143 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122880 256 128
      2434389563380424103511587 724499973956087664173556 h1 levelEleven_fractional_123136
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122880 512 =
      4233069455048945347605555 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 122880 384 128
      3158889537336511767685143 1074179917712433579920412 h2 levelEleven_fractional_123264
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_240 : ∀ i : Fin 512,
    levelEleven.lookup (122880 + i.val) ≤ levelElevenRoots.lookup (122880 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_122880
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 122880 128 128
    h0 levelEleven_squares_123008
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 122880 256 128
    h1 levelEleven_squares_123136
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 122880 384 128
    h2 levelEleven_squares_123264
  exact h3

end WordCertDensity.Certificates
