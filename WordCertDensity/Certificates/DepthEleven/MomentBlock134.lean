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
theorem levelEleven_energy_68608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 68608 128 =
      241005859538564706811049089264561 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_68608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68608 128 =
      2710851019609481229212220 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_68608 : ∀ i : Fin 128,
    levelEleven.lookup (68608 + i.val) ≤ levelElevenRoots.lookup (68608 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_68736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 68736 128 =
      49202836432328404196812887061532 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_68736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68736 128 =
      1219621583772899719238310 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_68736 : ∀ i : Fin 128,
    levelEleven.lookup (68736 + i.val) ≤ levelElevenRoots.lookup (68736 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_68864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 68864 128 =
      88955611559198434890943646406920 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_68864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68864 128 =
      1543535483449388113964006 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_68864 : ∀ i : Fin 128,
    levelEleven.lookup (68864 + i.val) ≤ levelElevenRoots.lookup (68864 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_68992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 68992 128 =
      38270529437706934500455632256042 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_68992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68992 128 =
      985612663179875474501873 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_68992 : ∀ i : Fin 128,
    levelEleven.lookup (68992 + i.val) ≤ levelElevenRoots.lookup (68992 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_134 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 68608 512 =
      417434836967798480399261254989055 := by
  have h0 := levelEleven_energy_68608
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 68608 256 =
      290208695970893111007861976326093 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 68608 128 128
      241005859538564706811049089264561 49202836432328404196812887061532 h0 levelEleven_energy_68736
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 68608 384 =
      379164307530091545898805622733013 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 68608 256 128
      290208695970893111007861976326093 88955611559198434890943646406920 h1 levelEleven_energy_68864
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 68608 512 =
      417434836967798480399261254989055 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 68608 384 128
      379164307530091545898805622733013 38270529437706934500455632256042 h2 levelEleven_energy_68992
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_134 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68608 512 =
      6459620750011644536916409 := by
  have h0 := levelEleven_fractional_68608
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68608 256 =
      3930472603382380948450530 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68608 128 128
      2710851019609481229212220 1219621583772899719238310 h0 levelEleven_fractional_68736
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68608 384 =
      5474008086831769062414536 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68608 256 128
      3930472603382380948450530 1543535483449388113964006 h1 levelEleven_fractional_68864
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68608 512 =
      6459620750011644536916409 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 68608 384 128
      5474008086831769062414536 985612663179875474501873 h2 levelEleven_fractional_68992
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_134 : ∀ i : Fin 512,
    levelEleven.lookup (68608 + i.val) ≤ levelElevenRoots.lookup (68608 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_68608
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 68608 128 128
    h0 levelEleven_squares_68736
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 68608 256 128
    h1 levelEleven_squares_68864
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 68608 384 128
    h2 levelEleven_squares_68992
  exact h3

end WordCertDensity.Certificates
