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
theorem levelEleven_energy_47104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 47104 128 =
      18329648491373975577621472561799 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_47104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47104 128 =
      701035359289775535588124 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_47104 : ∀ i : Fin 128,
    levelEleven.lookup (47104 + i.val) ≤ levelElevenRoots.lookup (47104 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_47232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 47232 128 =
      48928652070097693132519386398651 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_47232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47232 128 =
      1217976546729894644938617 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_47232 : ∀ i : Fin 128,
    levelEleven.lookup (47232 + i.val) ≤ levelElevenRoots.lookup (47232 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_47360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 47360 128 =
      45717203409287760077362590285296 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_47360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47360 128 =
      1045980992264966223203192 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_47360 : ∀ i : Fin 128,
    levelEleven.lookup (47360 + i.val) ≤ levelElevenRoots.lookup (47360 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_47488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 47488 128 =
      55301186531767266508961499291961 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_47488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47488 128 =
      1347825734452324812912343 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_47488 : ∀ i : Fin 128,
    levelEleven.lookup (47488 + i.val) ≤ levelElevenRoots.lookup (47488 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_92 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 47104 512 =
      168276690502526695296464948537707 := by
  have h0 := levelEleven_energy_47104
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 47104 256 =
      67258300561471668710140858960450 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 47104 128 128
      18329648491373975577621472561799 48928652070097693132519386398651 h0 levelEleven_energy_47232
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 47104 384 =
      112975503970759428787503449245746 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 47104 256 128
      67258300561471668710140858960450 45717203409287760077362590285296 h1 levelEleven_energy_47360
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 47104 512 =
      168276690502526695296464948537707 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 47104 384 128
      112975503970759428787503449245746 55301186531767266508961499291961 h2 levelEleven_energy_47488
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_92 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47104 512 =
      4312818632736961216642276 := by
  have h0 := levelEleven_fractional_47104
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47104 256 =
      1919011906019670180526741 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47104 128 128
      701035359289775535588124 1217976546729894644938617 h0 levelEleven_fractional_47232
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47104 384 =
      2964992898284636403729933 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47104 256 128
      1919011906019670180526741 1045980992264966223203192 h1 levelEleven_fractional_47360
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47104 512 =
      4312818632736961216642276 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 47104 384 128
      2964992898284636403729933 1347825734452324812912343 h2 levelEleven_fractional_47488
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_92 : ∀ i : Fin 512,
    levelEleven.lookup (47104 + i.val) ≤ levelElevenRoots.lookup (47104 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_47104
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 47104 128 128
    h0 levelEleven_squares_47232
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 47104 256 128
    h1 levelEleven_squares_47360
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 47104 384 128
    h2 levelEleven_squares_47488
  exact h3

end WordCertDensity.Certificates
