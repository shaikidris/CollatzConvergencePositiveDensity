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
theorem levelEleven_energy_44544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 44544 128 =
      46420000459520892746122689538774 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_44544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44544 128 =
      1214048963179315817907200 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_44544 : ∀ i : Fin 128,
    levelEleven.lookup (44544 + i.val) ≤ levelElevenRoots.lookup (44544 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_44672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 44672 128 =
      44894805485475957077292824066649 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_44672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44672 128 =
      1102995676791746419363465 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_44672 : ∀ i : Fin 128,
    levelEleven.lookup (44672 + i.val) ≤ levelElevenRoots.lookup (44672 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_44800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 44800 128 =
      47575302601877625479239975596417 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_44800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44800 128 =
      1211586916695247653215936 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_44800 : ∀ i : Fin 128,
    levelEleven.lookup (44800 + i.val) ≤ levelElevenRoots.lookup (44800 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_44928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 44928 128 =
      28850244344703548022092986578522 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_44928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44928 128 =
      813192192003153829682157 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_44928 : ∀ i : Fin 128,
    levelEleven.lookup (44928 + i.val) ≤ levelElevenRoots.lookup (44928 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_87 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 44544 512 =
      167740352891578023324748475780362 := by
  have h0 := levelEleven_energy_44544
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 44544 256 =
      91314805944996849823415513605423 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 44544 128 128
      46420000459520892746122689538774 44894805485475957077292824066649 h0 levelEleven_energy_44672
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 44544 384 =
      138890108546874475302655489201840 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 44544 256 128
      91314805944996849823415513605423 47575302601877625479239975596417 h1 levelEleven_energy_44800
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 44544 512 =
      167740352891578023324748475780362 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 44544 384 128
      138890108546874475302655489201840 28850244344703548022092986578522 h2 levelEleven_energy_44928
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_87 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44544 512 =
      4341823748669463720168758 := by
  have h0 := levelEleven_fractional_44544
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44544 256 =
      2317044639971062237270665 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44544 128 128
      1214048963179315817907200 1102995676791746419363465 h0 levelEleven_fractional_44672
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44544 384 =
      3528631556666309890486601 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44544 256 128
      2317044639971062237270665 1211586916695247653215936 h1 levelEleven_fractional_44800
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44544 512 =
      4341823748669463720168758 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 44544 384 128
      3528631556666309890486601 813192192003153829682157 h2 levelEleven_fractional_44928
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_87 : ∀ i : Fin 512,
    levelEleven.lookup (44544 + i.val) ≤ levelElevenRoots.lookup (44544 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_44544
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 44544 128 128
    h0 levelEleven_squares_44672
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 44544 256 128
    h1 levelEleven_squares_44800
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 44544 384 128
    h2 levelEleven_squares_44928
  exact h3

end WordCertDensity.Certificates
