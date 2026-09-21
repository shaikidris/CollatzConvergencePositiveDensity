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
theorem levelEleven_energy_80896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 80896 128 =
      107979191489719088841544858266239 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_80896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80896 128 =
      1667333276482842708680289 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_80896 : ∀ i : Fin 128,
    levelEleven.lookup (80896 + i.val) ≤ levelElevenRoots.lookup (80896 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_81024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 81024 128 =
      52032737101104099007468610097502 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_81024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81024 128 =
      1266493039142920121754581 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_81024 : ∀ i : Fin 128,
    levelEleven.lookup (81024 + i.val) ≤ levelElevenRoots.lookup (81024 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_81152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 81152 128 =
      72631969520200417166824371547679 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_81152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81152 128 =
      1492864559177158843115128 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_81152 : ∀ i : Fin 128,
    levelEleven.lookup (81152 + i.val) ≤ levelElevenRoots.lookup (81152 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_81280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 81280 128 =
      83536640466260232135743876064699 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_81280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 81280 128 =
      1590345884814974118541376 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_81280 : ∀ i : Fin 128,
    levelEleven.lookup (81280 + i.val) ≤ levelElevenRoots.lookup (81280 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_158 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 80896 512 =
      316180538577283837151581715976119 := by
  have h0 := levelEleven_energy_80896
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 80896 256 =
      160011928590823187849013468363741 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 80896 128 128
      107979191489719088841544858266239 52032737101104099007468610097502 h0 levelEleven_energy_81024
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 80896 384 =
      232643898111023605015837839911420 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 80896 256 128
      160011928590823187849013468363741 72631969520200417166824371547679 h1 levelEleven_energy_81152
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 80896 512 =
      316180538577283837151581715976119 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 80896 384 128
      232643898111023605015837839911420 83536640466260232135743876064699 h2 levelEleven_energy_81280
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_158 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80896 512 =
      6017036759617895792091374 := by
  have h0 := levelEleven_fractional_80896
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80896 256 =
      2933826315625762830434870 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80896 128 128
      1667333276482842708680289 1266493039142920121754581 h0 levelEleven_fractional_81024
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80896 384 =
      4426690874802921673549998 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80896 256 128
      2933826315625762830434870 1492864559177158843115128 h1 levelEleven_fractional_81152
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80896 512 =
      6017036759617895792091374 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 80896 384 128
      4426690874802921673549998 1590345884814974118541376 h2 levelEleven_fractional_81280
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_158 : ∀ i : Fin 512,
    levelEleven.lookup (80896 + i.val) ≤ levelElevenRoots.lookup (80896 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_80896
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 80896 128 128
    h0 levelEleven_squares_81024
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 80896 256 128
    h1 levelEleven_squares_81152
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 80896 384 128
    h2 levelEleven_squares_81280
  exact h3

end WordCertDensity.Certificates
