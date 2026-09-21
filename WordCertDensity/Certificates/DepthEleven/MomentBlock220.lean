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
theorem levelEleven_energy_112640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 112640 128 =
      19145195369303474488731010522746 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_112640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112640 128 =
      715768709345911121427364 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_112640 : ∀ i : Fin 128,
    levelEleven.lookup (112640 + i.val) ≤ levelElevenRoots.lookup (112640 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_112768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 112768 128 =
      23003382454819361002060411231514 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_112768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112768 128 =
      745203753378400615384292 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_112768 : ∀ i : Fin 128,
    levelEleven.lookup (112768 + i.val) ≤ levelElevenRoots.lookup (112768 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_112896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 112896 128 =
      74139854287690086997716276710272 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_112896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112896 128 =
      1506874134693642616932482 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_112896 : ∀ i : Fin 128,
    levelEleven.lookup (112896 + i.val) ≤ levelElevenRoots.lookup (112896 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_113024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 113024 128 =
      24724893415245118325231550418986 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_113024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 113024 128 =
      770770178509039366826009 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_113024 : ∀ i : Fin 128,
    levelEleven.lookup (113024 + i.val) ≤ levelElevenRoots.lookup (113024 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_220 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 112640 512 =
      141013325527058040813739248883518 := by
  have h0 := levelEleven_energy_112640
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 112640 256 =
      42148577824122835490791421754260 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 112640 128 128
      19145195369303474488731010522746 23003382454819361002060411231514 h0 levelEleven_energy_112768
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 112640 384 =
      116288432111812922488507698464532 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 112640 256 128
      42148577824122835490791421754260 74139854287690086997716276710272 h1 levelEleven_energy_112896
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 112640 512 =
      141013325527058040813739248883518 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 112640 384 128
      116288432111812922488507698464532 24724893415245118325231550418986 h2 levelEleven_energy_113024
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_220 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112640 512 =
      3738616775926993720570147 := by
  have h0 := levelEleven_fractional_112640
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112640 256 =
      1460972462724311736811656 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112640 128 128
      715768709345911121427364 745203753378400615384292 h0 levelEleven_fractional_112768
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112640 384 =
      2967846597417954353744138 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112640 256 128
      1460972462724311736811656 1506874134693642616932482 h1 levelEleven_fractional_112896
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112640 512 =
      3738616775926993720570147 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 112640 384 128
      2967846597417954353744138 770770178509039366826009 h2 levelEleven_fractional_113024
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_220 : ∀ i : Fin 512,
    levelEleven.lookup (112640 + i.val) ≤ levelElevenRoots.lookup (112640 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_112640
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 112640 128 128
    h0 levelEleven_squares_112768
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 112640 256 128
    h1 levelEleven_squares_112896
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 112640 384 128
    h2 levelEleven_squares_113024
  exact h3

end WordCertDensity.Certificates
