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
theorem levelEleven_energy_111616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 111616 128 =
      127334938852886164848352322666324 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_111616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111616 128 =
      2164387931400549339748169 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_111616 : ∀ i : Fin 128,
    levelEleven.lookup (111616 + i.val) ≤ levelElevenRoots.lookup (111616 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_111744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 111744 128 =
      36503710406148649811431727556530 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_111744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111744 128 =
      1027028395189440718358516 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_111744 : ∀ i : Fin 128,
    levelEleven.lookup (111744 + i.val) ≤ levelElevenRoots.lookup (111744 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_111872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 111872 128 =
      76324615979366121436822471451736 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_111872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111872 128 =
      1431343081596225321470575 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_111872 : ∀ i : Fin 128,
    levelEleven.lookup (111872 + i.val) ≤ levelElevenRoots.lookup (111872 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_112000 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 112000 128 =
      74948899599915145866378723880630 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_112000 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112000 128 =
      1366437575852542374061438 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_112000 : ∀ i : Fin 128,
    levelEleven.lookup (112000 + i.val) ≤ levelElevenRoots.lookup (112000 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_218 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 111616 512 =
      315112164838316081962985245555220 := by
  have h0 := levelEleven_energy_111616
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 111616 256 =
      163838649259034814659784050222854 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 111616 128 128
      127334938852886164848352322666324 36503710406148649811431727556530 h0 levelEleven_energy_111744
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 111616 384 =
      240163265238400936096606521674590 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 111616 256 128
      163838649259034814659784050222854 76324615979366121436822471451736 h1 levelEleven_energy_111872
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 111616 512 =
      315112164838316081962985245555220 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 111616 384 128
      240163265238400936096606521674590 74948899599915145866378723880630 h2 levelEleven_energy_112000
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_218 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111616 512 =
      5989196984038757753638698 := by
  have h0 := levelEleven_fractional_111616
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111616 256 =
      3191416326589990058106685 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111616 128 128
      2164387931400549339748169 1027028395189440718358516 h0 levelEleven_fractional_111744
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111616 384 =
      4622759408186215379577260 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111616 256 128
      3191416326589990058106685 1431343081596225321470575 h1 levelEleven_fractional_111872
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111616 512 =
      5989196984038757753638698 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 111616 384 128
      4622759408186215379577260 1366437575852542374061438 h2 levelEleven_fractional_112000
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_218 : ∀ i : Fin 512,
    levelEleven.lookup (111616 + i.val) ≤ levelElevenRoots.lookup (111616 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_111616
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 111616 128 128
    h0 levelEleven_squares_111744
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 111616 256 128
    h1 levelEleven_squares_111872
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 111616 384 128
    h2 levelEleven_squares_112000
  exact h3

end WordCertDensity.Certificates
