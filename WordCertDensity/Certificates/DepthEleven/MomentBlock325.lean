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
theorem levelEleven_energy_166400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 166400 128 =
      31137335098674134895444881461701 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_166400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166400 128 =
      919009070097476410767487 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_166400 : ∀ i : Fin 128,
    levelEleven.lookup (166400 + i.val) ≤ levelElevenRoots.lookup (166400 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_166528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 166528 128 =
      31262687575283716854387077138621 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_166528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166528 128 =
      950167125806416687448222 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_166528 : ∀ i : Fin 128,
    levelEleven.lookup (166528 + i.val) ≤ levelElevenRoots.lookup (166528 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_166656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 166656 128 =
      47552922624811776322684157311580 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_166656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166656 128 =
      1135711006736301313846259 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_166656 : ∀ i : Fin 128,
    levelEleven.lookup (166656 + i.val) ≤ levelElevenRoots.lookup (166656 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_166784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 166784 128 =
      41172626064006241351366666913387 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_166784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166784 128 =
      1094151682349283923092766 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_166784 : ∀ i : Fin 128,
    levelEleven.lookup (166784 + i.val) ≤ levelElevenRoots.lookup (166784 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_325 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 166400 512 =
      151125571362775869423882782825289 := by
  have h0 := levelEleven_energy_166400
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 166400 256 =
      62400022673957851749831958600322 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 166400 128 128
      31137335098674134895444881461701 31262687575283716854387077138621 h0 levelEleven_energy_166528
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 166400 384 =
      109952945298769628072516115911902 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 166400 256 128
      62400022673957851749831958600322 47552922624811776322684157311580 h1 levelEleven_energy_166656
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 166400 512 =
      151125571362775869423882782825289 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 166400 384 128
      109952945298769628072516115911902 41172626064006241351366666913387 h2 levelEleven_energy_166784
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_325 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166400 512 =
      4099038884989478335154734 := by
  have h0 := levelEleven_fractional_166400
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166400 256 =
      1869176195903893098215709 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166400 128 128
      919009070097476410767487 950167125806416687448222 h0 levelEleven_fractional_166528
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166400 384 =
      3004887202640194412061968 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166400 256 128
      1869176195903893098215709 1135711006736301313846259 h1 levelEleven_fractional_166656
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166400 512 =
      4099038884989478335154734 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 166400 384 128
      3004887202640194412061968 1094151682349283923092766 h2 levelEleven_fractional_166784
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_325 : ∀ i : Fin 512,
    levelEleven.lookup (166400 + i.val) ≤ levelElevenRoots.lookup (166400 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_166400
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 166400 128 128
    h0 levelEleven_squares_166528
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 166400 256 128
    h1 levelEleven_squares_166656
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 166400 384 128
    h2 levelEleven_squares_166784
  exact h3

end WordCertDensity.Certificates
