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
theorem levelEleven_energy_24064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 24064 128 =
      19645200240984231606689703334010 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_24064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24064 128 =
      652458968357006153853828 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_24064 : ∀ i : Fin 128,
    levelEleven.lookup (24064 + i.val) ≤ levelElevenRoots.lookup (24064 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_24192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 24192 128 =
      93331322073926093525650743627136 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_24192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24192 128 =
      1716364496674141249198311 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_24192 : ∀ i : Fin 128,
    levelEleven.lookup (24192 + i.val) ≤ levelElevenRoots.lookup (24192 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_24320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 24320 128 =
      29267604819065247849107137275571 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_24320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24320 128 =
      850479786680752993695858 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_24320 : ∀ i : Fin 128,
    levelEleven.lookup (24320 + i.val) ≤ levelElevenRoots.lookup (24320 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_24448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 24448 128 =
      61877309543766012246470119830522 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_24448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24448 128 =
      1339748144626375716568349 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_24448 : ∀ i : Fin 128,
    levelEleven.lookup (24448 + i.val) ≤ levelElevenRoots.lookup (24448 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_47 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 24064 512 =
      204121436677741585227917704067239 := by
  have h0 := levelEleven_energy_24064
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 24064 256 =
      112976522314910325132340446961146 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 24064 128 128
      19645200240984231606689703334010 93331322073926093525650743627136 h0 levelEleven_energy_24192
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 24064 384 =
      142244127133975572981447584236717 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 24064 256 128
      112976522314910325132340446961146 29267604819065247849107137275571 h1 levelEleven_energy_24320
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 24064 512 =
      204121436677741585227917704067239 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 24064 384 128
      142244127133975572981447584236717 61877309543766012246470119830522 h2 levelEleven_energy_24448
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_47 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24064 512 =
      4559051396338276113316346 := by
  have h0 := levelEleven_fractional_24064
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24064 256 =
      2368823465031147403052139 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24064 128 128
      652458968357006153853828 1716364496674141249198311 h0 levelEleven_fractional_24192
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24064 384 =
      3219303251711900396747997 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24064 256 128
      2368823465031147403052139 850479786680752993695858 h1 levelEleven_fractional_24320
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24064 512 =
      4559051396338276113316346 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24064 384 128
      3219303251711900396747997 1339748144626375716568349 h2 levelEleven_fractional_24448
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_47 : ∀ i : Fin 512,
    levelEleven.lookup (24064 + i.val) ≤ levelElevenRoots.lookup (24064 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_24064
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 24064 128 128
    h0 levelEleven_squares_24192
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 24064 256 128
    h1 levelEleven_squares_24320
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 24064 384 128
    h2 levelEleven_squares_24448
  exact h3

end WordCertDensity.Certificates
