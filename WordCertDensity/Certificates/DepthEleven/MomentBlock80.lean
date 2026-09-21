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
theorem levelEleven_energy_40960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 40960 128 =
      252378523154180625235951661449014 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_40960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40960 128 =
      2899405279962096915628567 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_40960 : ∀ i : Fin 128,
    levelEleven.lookup (40960 + i.val) ≤ levelElevenRoots.lookup (40960 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_41088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 41088 128 =
      36223407589399116318093062282366 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_41088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41088 128 =
      970959484915345238849879 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_41088 : ∀ i : Fin 128,
    levelEleven.lookup (41088 + i.val) ≤ levelElevenRoots.lookup (41088 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_41216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 41216 128 =
      26949140673833020713071795864378 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_41216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41216 128 =
      863648255497087434286582 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_41216 : ∀ i : Fin 128,
    levelEleven.lookup (41216 + i.val) ≤ levelElevenRoots.lookup (41216 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_41344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 41344 128 =
      71036069214938402901911748332109 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_41344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41344 128 =
      1407443654198538664672760 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_41344 : ∀ i : Fin 128,
    levelEleven.lookup (41344 + i.val) ≤ levelElevenRoots.lookup (41344 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_80 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 40960 512 =
      386587140632351165169028267927867 := by
  have h0 := levelEleven_energy_40960
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 40960 256 =
      288601930743579741554044723731380 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 40960 128 128
      252378523154180625235951661449014 36223407589399116318093062282366 h0 levelEleven_energy_41088
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 40960 384 =
      315551071417412762267116519595758 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 40960 256 128
      288601930743579741554044723731380 26949140673833020713071795864378 h1 levelEleven_energy_41216
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 40960 512 =
      386587140632351165169028267927867 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 40960 384 128
      315551071417412762267116519595758 71036069214938402901911748332109 h2 levelEleven_energy_41344
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_80 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40960 512 =
      6141456674573068253437788 := by
  have h0 := levelEleven_fractional_40960
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40960 256 =
      3870364764877442154478446 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40960 128 128
      2899405279962096915628567 970959484915345238849879 h0 levelEleven_fractional_41088
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40960 384 =
      4734013020374529588765028 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40960 256 128
      3870364764877442154478446 863648255497087434286582 h1 levelEleven_fractional_41216
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40960 512 =
      6141456674573068253437788 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 40960 384 128
      4734013020374529588765028 1407443654198538664672760 h2 levelEleven_fractional_41344
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_80 : ∀ i : Fin 512,
    levelEleven.lookup (40960 + i.val) ≤ levelElevenRoots.lookup (40960 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_40960
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 40960 128 128
    h0 levelEleven_squares_41088
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 40960 256 128
    h1 levelEleven_squares_41216
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 40960 384 128
    h2 levelEleven_squares_41344
  exact h3

end WordCertDensity.Certificates
