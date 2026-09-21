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
theorem levelEleven_energy_54784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 54784 128 =
      34931364698097896817755552844448 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_54784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54784 128 =
      1040609633395170323502857 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_54784 : ∀ i : Fin 128,
    levelEleven.lookup (54784 + i.val) ≤ levelElevenRoots.lookup (54784 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_54912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 54912 128 =
      48389903723224429471968109810508 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_54912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54912 128 =
      1120133080794293449994739 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_54912 : ∀ i : Fin 128,
    levelEleven.lookup (54912 + i.val) ≤ levelElevenRoots.lookup (54912 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_55040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 55040 128 =
      33904007669748924510771492479389 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_55040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55040 128 =
      990806533080247281231845 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_55040 : ∀ i : Fin 128,
    levelEleven.lookup (55040 + i.val) ≤ levelElevenRoots.lookup (55040 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_55168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 55168 128 =
      28074650524114795873550567111701 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_55168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55168 128 =
      826280539650756622618557 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_55168 : ∀ i : Fin 128,
    levelEleven.lookup (55168 + i.val) ≤ levelElevenRoots.lookup (55168 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_107 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 54784 512 =
      145299926615186046674045722246046 := by
  have h0 := levelEleven_energy_54784
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 54784 256 =
      83321268421322326289723662654956 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 54784 128 128
      34931364698097896817755552844448 48389903723224429471968109810508 h0 levelEleven_energy_54912
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 54784 384 =
      117225276091071250800495155134345 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 54784 256 128
      83321268421322326289723662654956 33904007669748924510771492479389 h1 levelEleven_energy_55040
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 54784 512 =
      145299926615186046674045722246046 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 54784 384 128
      117225276091071250800495155134345 28074650524114795873550567111701 h2 levelEleven_energy_55168
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_107 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54784 512 =
      3977829786920467677347998 := by
  have h0 := levelEleven_fractional_54784
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54784 256 =
      2160742714189463773497596 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54784 128 128
      1040609633395170323502857 1120133080794293449994739 h0 levelEleven_fractional_54912
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54784 384 =
      3151549247269711054729441 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54784 256 128
      2160742714189463773497596 990806533080247281231845 h1 levelEleven_fractional_55040
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54784 512 =
      3977829786920467677347998 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 54784 384 128
      3151549247269711054729441 826280539650756622618557 h2 levelEleven_fractional_55168
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_107 : ∀ i : Fin 512,
    levelEleven.lookup (54784 + i.val) ≤ levelElevenRoots.lookup (54784 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_54784
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 54784 128 128
    h0 levelEleven_squares_54912
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 54784 256 128
    h1 levelEleven_squares_55040
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 54784 384 128
    h2 levelEleven_squares_55168
  exact h3

end WordCertDensity.Certificates
