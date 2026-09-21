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
theorem levelEleven_energy_30208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 30208 128 =
      50389690026831390752691220068205 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_30208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30208 128 =
      1277380356343831429232773 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_30208 : ∀ i : Fin 128,
    levelEleven.lookup (30208 + i.val) ≤ levelElevenRoots.lookup (30208 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_30336 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 30336 128 =
      23855183065823919128637473690097 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_30336 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30336 128 =
      757101090179771914839940 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_30336 : ∀ i : Fin 128,
    levelEleven.lookup (30336 + i.val) ≤ levelElevenRoots.lookup (30336 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_30464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 30464 128 =
      49602448718813703602571656415321 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_30464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30464 128 =
      1215670133833861940084059 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_30464 : ∀ i : Fin 128,
    levelEleven.lookup (30464 + i.val) ≤ levelElevenRoots.lookup (30464 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_30592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 30592 128 =
      34774632217176879744512994212385 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_30592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30592 128 =
      897156602043307713016085 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_30592 : ∀ i : Fin 128,
    levelEleven.lookup (30592 + i.val) ≤ levelElevenRoots.lookup (30592 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_59 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 30208 512 =
      158621954028645893228413344386008 := by
  have h0 := levelEleven_energy_30208
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 30208 256 =
      74244873092655309881328693758302 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 30208 128 128
      50389690026831390752691220068205 23855183065823919128637473690097 h0 levelEleven_energy_30336
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 30208 384 =
      123847321811469013483900350173623 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 30208 256 128
      74244873092655309881328693758302 49602448718813703602571656415321 h1 levelEleven_energy_30464
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 30208 512 =
      158621954028645893228413344386008 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 30208 384 128
      123847321811469013483900350173623 34774632217176879744512994212385 h2 levelEleven_energy_30592
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_59 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30208 512 =
      4147308182400772997172857 := by
  have h0 := levelEleven_fractional_30208
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30208 256 =
      2034481446523603344072713 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30208 128 128
      1277380356343831429232773 757101090179771914839940 h0 levelEleven_fractional_30336
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30208 384 =
      3250151580357465284156772 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30208 256 128
      2034481446523603344072713 1215670133833861940084059 h1 levelEleven_fractional_30464
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30208 512 =
      4147308182400772997172857 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30208 384 128
      3250151580357465284156772 897156602043307713016085 h2 levelEleven_fractional_30592
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_59 : ∀ i : Fin 512,
    levelEleven.lookup (30208 + i.val) ≤ levelElevenRoots.lookup (30208 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_30208
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 30208 128 128
    h0 levelEleven_squares_30336
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 30208 256 128
    h1 levelEleven_squares_30464
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 30208 384 128
    h2 levelEleven_squares_30592
  exact h3

end WordCertDensity.Certificates
