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
theorem levelEleven_energy_170496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 170496 128 =
      802603490758776040944017086868240 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_170496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170496 128 =
      6003137090606110315688096 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_170496 : ∀ i : Fin 128,
    levelEleven.lookup (170496 + i.val) ≤ levelElevenRoots.lookup (170496 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_170624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 170624 128 =
      34968811029067436466303231813226 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_170624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170624 128 =
      969937575723995250425916 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_170624 : ∀ i : Fin 128,
    levelEleven.lookup (170624 + i.val) ≤ levelElevenRoots.lookup (170624 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_170752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 170752 128 =
      73244672522342156473967396091402 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_170752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170752 128 =
      1467354016009212182948046 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_170752 : ∀ i : Fin 128,
    levelEleven.lookup (170752 + i.val) ≤ levelElevenRoots.lookup (170752 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_170880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 170880 128 =
      92192778068395626442678357861103 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_170880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170880 128 =
      1684719895964103372362826 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_170880 : ∀ i : Fin 128,
    levelEleven.lookup (170880 + i.val) ≤ levelElevenRoots.lookup (170880 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_333 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 170496 512 =
      1003009752378581260326966072633971 := by
  have h0 := levelEleven_energy_170496
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 170496 256 =
      837572301787843477410320318681466 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 170496 128 128
      802603490758776040944017086868240 34968811029067436466303231813226 h0 levelEleven_energy_170624
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 170496 384 =
      910816974310185633884287714772868 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 170496 256 128
      837572301787843477410320318681466 73244672522342156473967396091402 h1 levelEleven_energy_170752
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 170496 512 =
      1003009752378581260326966072633971 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 170496 384 128
      910816974310185633884287714772868 92192778068395626442678357861103 h2 levelEleven_energy_170880
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_333 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170496 512 =
      10125148578303421121424884 := by
  have h0 := levelEleven_fractional_170496
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170496 256 =
      6973074666330105566114012 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170496 128 128
      6003137090606110315688096 969937575723995250425916 h0 levelEleven_fractional_170624
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170496 384 =
      8440428682339317749062058 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170496 256 128
      6973074666330105566114012 1467354016009212182948046 h1 levelEleven_fractional_170752
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170496 512 =
      10125148578303421121424884 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170496 384 128
      8440428682339317749062058 1684719895964103372362826 h2 levelEleven_fractional_170880
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_333 : ∀ i : Fin 512,
    levelEleven.lookup (170496 + i.val) ≤ levelElevenRoots.lookup (170496 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_170496
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 170496 128 128
    h0 levelEleven_squares_170624
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 170496 256 128
    h1 levelEleven_squares_170752
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 170496 384 128
    h2 levelEleven_squares_170880
  exact h3

end WordCertDensity.Certificates
