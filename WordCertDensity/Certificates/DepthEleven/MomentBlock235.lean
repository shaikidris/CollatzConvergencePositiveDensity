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
theorem levelEleven_energy_120320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 120320 128 =
      197547998799683228740543059528718 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_120320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120320 128 =
      2214839557168180311160447 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_120320 : ∀ i : Fin 128,
    levelEleven.lookup (120320 + i.val) ≤ levelElevenRoots.lookup (120320 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_120448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 120448 128 =
      124402815461009108090327444246855 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_120448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120448 128 =
      2000605509674084145669660 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_120448 : ∀ i : Fin 128,
    levelEleven.lookup (120448 + i.val) ≤ levelElevenRoots.lookup (120448 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_120576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 120576 128 =
      27214699621578776845680688554279 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_120576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120576 128 =
      861119099173647953047176 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_120576 : ∀ i : Fin 128,
    levelEleven.lookup (120576 + i.val) ≤ levelElevenRoots.lookup (120576 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_120704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 120704 128 =
      43358776983327450801299999234301 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_120704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120704 128 =
      1138422433822272926898259 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_120704 : ∀ i : Fin 128,
    levelEleven.lookup (120704 + i.val) ≤ levelElevenRoots.lookup (120704 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_235 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 120320 512 =
      392524290865598564477851191564153 := by
  have h0 := levelEleven_energy_120320
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 120320 256 =
      321950814260692336830870503775573 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 120320 128 128
      197547998799683228740543059528718 124402815461009108090327444246855 h0 levelEleven_energy_120448
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 120320 384 =
      349165513882271113676551192329852 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 120320 256 128
      321950814260692336830870503775573 27214699621578776845680688554279 h1 levelEleven_energy_120576
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 120320 512 =
      392524290865598564477851191564153 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 120320 384 128
      349165513882271113676551192329852 43358776983327450801299999234301 h2 levelEleven_energy_120704
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_235 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120320 512 =
      6214986599838185336775542 := by
  have h0 := levelEleven_fractional_120320
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120320 256 =
      4215445066842264456830107 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120320 128 128
      2214839557168180311160447 2000605509674084145669660 h0 levelEleven_fractional_120448
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120320 384 =
      5076564166015912409877283 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120320 256 128
      4215445066842264456830107 861119099173647953047176 h1 levelEleven_fractional_120576
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120320 512 =
      6214986599838185336775542 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 120320 384 128
      5076564166015912409877283 1138422433822272926898259 h2 levelEleven_fractional_120704
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_235 : ∀ i : Fin 512,
    levelEleven.lookup (120320 + i.val) ≤ levelElevenRoots.lookup (120320 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_120320
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 120320 128 128
    h0 levelEleven_squares_120448
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 120320 256 128
    h1 levelEleven_squares_120576
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 120320 384 128
    h2 levelEleven_squares_120704
  exact h3

end WordCertDensity.Certificates
