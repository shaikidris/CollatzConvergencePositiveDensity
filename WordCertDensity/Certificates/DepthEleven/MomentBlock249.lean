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
theorem levelEleven_energy_127488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 127488 128 =
      28628380348039798259241916811362 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_127488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127488 128 =
      902264527320061385089839 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_127488 : ∀ i : Fin 128,
    levelEleven.lookup (127488 + i.val) ≤ levelElevenRoots.lookup (127488 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_127616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 127616 128 =
      66284651306292443673000068499368 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_127616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127616 128 =
      1243880964843643472557325 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_127616 : ∀ i : Fin 128,
    levelEleven.lookup (127616 + i.val) ≤ levelElevenRoots.lookup (127616 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_127744 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 127744 128 =
      36971274123841797929614164989063 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_127744 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127744 128 =
      1026155694142954013418546 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_127744 : ∀ i : Fin 128,
    levelEleven.lookup (127744 + i.val) ≤ levelElevenRoots.lookup (127744 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_127872 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 127872 128 =
      218076144500298716199647634736853 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_127872 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127872 128 =
      2561486637399481620707946 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_127872 : ∀ i : Fin 128,
    levelEleven.lookup (127872 + i.val) ≤ levelElevenRoots.lookup (127872 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_249 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 127488 512 =
      349960450278472756061503785036646 := by
  have h0 := levelEleven_energy_127488
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 127488 256 =
      94913031654332241932241985310730 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 127488 128 128
      28628380348039798259241916811362 66284651306292443673000068499368 h0 levelEleven_energy_127616
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 127488 384 =
      131884305778174039861856150299793 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 127488 256 128
      94913031654332241932241985310730 36971274123841797929614164989063 h1 levelEleven_energy_127744
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 127488 512 =
      349960450278472756061503785036646 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 127488 384 128
      131884305778174039861856150299793 218076144500298716199647634736853 h2 levelEleven_energy_127872
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_249 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127488 512 =
      5733787823706140491773656 := by
  have h0 := levelEleven_fractional_127488
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127488 256 =
      2146145492163704857647164 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127488 128 128
      902264527320061385089839 1243880964843643472557325 h0 levelEleven_fractional_127616
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127488 384 =
      3172301186306658871065710 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127488 256 128
      2146145492163704857647164 1026155694142954013418546 h1 levelEleven_fractional_127744
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127488 512 =
      5733787823706140491773656 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 127488 384 128
      3172301186306658871065710 2561486637399481620707946 h2 levelEleven_fractional_127872
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_249 : ∀ i : Fin 512,
    levelEleven.lookup (127488 + i.val) ≤ levelElevenRoots.lookup (127488 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_127488
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 127488 128 128
    h0 levelEleven_squares_127616
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 127488 256 128
    h1 levelEleven_squares_127744
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 127488 384 128
    h2 levelEleven_squares_127872
  exact h3

end WordCertDensity.Certificates
