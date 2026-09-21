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
theorem levelEleven_energy_9216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 9216 128 =
      53602724122896803797785941129630 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_9216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9216 128 =
      1170292698078520402289112 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_9216 : ∀ i : Fin 128,
    levelEleven.lookup (9216 + i.val) ≤ levelElevenRoots.lookup (9216 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_9344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 9344 128 =
      33782879170238867648665908454141 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_9344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9344 128 =
      979353099891287947179130 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_9344 : ∀ i : Fin 128,
    levelEleven.lookup (9344 + i.val) ≤ levelElevenRoots.lookup (9344 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_9472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 9472 128 =
      21357585793042130231365631942483 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_9472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9472 128 =
      742181475679965698296861 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_9472 : ∀ i : Fin 128,
    levelEleven.lookup (9472 + i.val) ≤ levelElevenRoots.lookup (9472 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_9600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 9600 128 =
      124125149939310500026828855709374 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_9600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9600 128 =
      2015550543572082660040747 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_9600 : ∀ i : Fin 128,
    levelEleven.lookup (9600 + i.val) ≤ levelElevenRoots.lookup (9600 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_18 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 9216 512 =
      232868339025488301704646337235628 := by
  have h0 := levelEleven_energy_9216
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 9216 256 =
      87385603293135671446451849583771 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 9216 128 128
      53602724122896803797785941129630 33782879170238867648665908454141 h0 levelEleven_energy_9344
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 9216 384 =
      108743189086177801677817481526254 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 9216 256 128
      87385603293135671446451849583771 21357585793042130231365631942483 h1 levelEleven_energy_9472
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 9216 512 =
      232868339025488301704646337235628 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 9216 384 128
      108743189086177801677817481526254 124125149939310500026828855709374 h2 levelEleven_energy_9600
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_18 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9216 512 =
      4907377817221856707805850 := by
  have h0 := levelEleven_fractional_9216
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9216 256 =
      2149645797969808349468242 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9216 128 128
      1170292698078520402289112 979353099891287947179130 h0 levelEleven_fractional_9344
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9216 384 =
      2891827273649774047765103 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9216 256 128
      2149645797969808349468242 742181475679965698296861 h1 levelEleven_fractional_9472
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9216 512 =
      4907377817221856707805850 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9216 384 128
      2891827273649774047765103 2015550543572082660040747 h2 levelEleven_fractional_9600
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_18 : ∀ i : Fin 512,
    levelEleven.lookup (9216 + i.val) ≤ levelElevenRoots.lookup (9216 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_9216
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 9216 128 128
    h0 levelEleven_squares_9344
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 9216 256 128
    h1 levelEleven_squares_9472
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 9216 384 128
    h2 levelEleven_squares_9600
  exact h3

end WordCertDensity.Certificates
