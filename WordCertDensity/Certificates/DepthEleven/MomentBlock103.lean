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
theorem levelEleven_energy_52736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 52736 128 =
      35816569373233779185653084605875 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_52736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52736 128 =
      977411856840919630475579 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_52736 : ∀ i : Fin 128,
    levelEleven.lookup (52736 + i.val) ≤ levelElevenRoots.lookup (52736 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_52864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 52864 128 =
      45673608188766147500356096733809 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_52864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52864 128 =
      1198520071681604092325284 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_52864 : ∀ i : Fin 128,
    levelEleven.lookup (52864 + i.val) ≤ levelElevenRoots.lookup (52864 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_52992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 52992 128 =
      27891966489333682789741737196906 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_52992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52992 128 =
      804103618138197461699196 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_52992 : ∀ i : Fin 128,
    levelEleven.lookup (52992 + i.val) ≤ levelElevenRoots.lookup (52992 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_53120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 53120 128 =
      55977860425895287625603115716914 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_53120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 53120 128 =
      1295322249336350126991780 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_53120 : ∀ i : Fin 128,
    levelEleven.lookup (53120 + i.val) ≤ levelElevenRoots.lookup (53120 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_103 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 52736 512 =
      165360004477228897101354034253504 := by
  have h0 := levelEleven_energy_52736
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 52736 256 =
      81490177561999926686009181339684 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 52736 128 128
      35816569373233779185653084605875 45673608188766147500356096733809 h0 levelEleven_energy_52864
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 52736 384 =
      109382144051333609475750918536590 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 52736 256 128
      81490177561999926686009181339684 27891966489333682789741737196906 h1 levelEleven_energy_52992
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 52736 512 =
      165360004477228897101354034253504 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 52736 384 128
      109382144051333609475750918536590 55977860425895287625603115716914 h2 levelEleven_energy_53120
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_103 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52736 512 =
      4275357795997071311491839 := by
  have h0 := levelEleven_fractional_52736
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52736 256 =
      2175931928522523722800863 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52736 128 128
      977411856840919630475579 1198520071681604092325284 h0 levelEleven_fractional_52864
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52736 384 =
      2980035546660721184500059 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52736 256 128
      2175931928522523722800863 804103618138197461699196 h1 levelEleven_fractional_52992
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52736 512 =
      4275357795997071311491839 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 52736 384 128
      2980035546660721184500059 1295322249336350126991780 h2 levelEleven_fractional_53120
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_103 : ∀ i : Fin 512,
    levelEleven.lookup (52736 + i.val) ≤ levelElevenRoots.lookup (52736 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_52736
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 52736 128 128
    h0 levelEleven_squares_52864
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 52736 256 128
    h1 levelEleven_squares_52992
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 52736 384 128
    h2 levelEleven_squares_53120
  exact h3

end WordCertDensity.Certificates
