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
theorem levelEleven_energy_38400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 38400 128 =
      16826213387951491394648293388729 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_38400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38400 128 =
      636886767508894863299488 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_38400 : ∀ i : Fin 128,
    levelEleven.lookup (38400 + i.val) ≤ levelElevenRoots.lookup (38400 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_38528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 38528 128 =
      148328025086386317156734566830938 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_38528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38528 128 =
      2133631601186504297264113 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_38528 : ∀ i : Fin 128,
    levelEleven.lookup (38528 + i.val) ≤ levelElevenRoots.lookup (38528 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_38656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 38656 128 =
      23234959011259389981499183572297 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_38656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38656 128 =
      772416223115792282000139 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_38656 : ∀ i : Fin 128,
    levelEleven.lookup (38656 + i.val) ≤ levelElevenRoots.lookup (38656 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_38784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 38784 128 =
      45693579513925455041474982085413 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_38784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38784 128 =
      1199279148233898806312373 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_38784 : ∀ i : Fin 128,
    levelEleven.lookup (38784 + i.val) ≤ levelElevenRoots.lookup (38784 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_75 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 38400 512 =
      234082776999522653574357025877377 := by
  have h0 := levelEleven_energy_38400
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 38400 256 =
      165154238474337808551382860219667 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 38400 128 128
      16826213387951491394648293388729 148328025086386317156734566830938 h0 levelEleven_energy_38528
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 38400 384 =
      188389197485597198532882043791964 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 38400 256 128
      165154238474337808551382860219667 23234959011259389981499183572297 h1 levelEleven_energy_38656
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 38400 512 =
      234082776999522653574357025877377 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 38400 384 128
      188389197485597198532882043791964 45693579513925455041474982085413 h2 levelEleven_energy_38784
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_75 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38400 512 =
      4742213740045090248876113 := by
  have h0 := levelEleven_fractional_38400
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38400 256 =
      2770518368695399160563601 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38400 128 128
      636886767508894863299488 2133631601186504297264113 h0 levelEleven_fractional_38528
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38400 384 =
      3542934591811191442563740 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38400 256 128
      2770518368695399160563601 772416223115792282000139 h1 levelEleven_fractional_38656
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38400 512 =
      4742213740045090248876113 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38400 384 128
      3542934591811191442563740 1199279148233898806312373 h2 levelEleven_fractional_38784
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_75 : ∀ i : Fin 512,
    levelEleven.lookup (38400 + i.val) ≤ levelElevenRoots.lookup (38400 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_38400
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 38400 128 128
    h0 levelEleven_squares_38528
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 38400 256 128
    h1 levelEleven_squares_38656
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 38400 384 128
    h2 levelEleven_squares_38784
  exact h3

end WordCertDensity.Certificates
