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
theorem levelEleven_energy_12800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 12800 128 =
      37971229893147161609801436779161 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_12800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12800 128 =
      1101098348669208805004684 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_12800 : ∀ i : Fin 128,
    levelEleven.lookup (12800 + i.val) ≤ levelElevenRoots.lookup (12800 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_12928 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 12928 128 =
      38102247388593787977479600277290 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_12928 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12928 128 =
      1060303938194014569231256 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_12928 : ∀ i : Fin 128,
    levelEleven.lookup (12928 + i.val) ≤ levelElevenRoots.lookup (12928 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_13056 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 13056 128 =
      97454828884155505320344014272922 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_13056 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13056 128 =
      1592911137136216178034667 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_13056 : ∀ i : Fin 128,
    levelEleven.lookup (13056 + i.val) ≤ levelElevenRoots.lookup (13056 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_13184 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 13184 128 =
      57827680320555461472834935251935 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_13184 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 13184 128 =
      1347530782862177957618438 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_13184 : ∀ i : Fin 128,
    levelEleven.lookup (13184 + i.val) ≤ levelElevenRoots.lookup (13184 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_25 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 12800 512 =
      231355986486451916380459986581308 := by
  have h0 := levelEleven_energy_12800
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 12800 256 =
      76073477281740949587281037056451 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 12800 128 128
      37971229893147161609801436779161 38102247388593787977479600277290 h0 levelEleven_energy_12928
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 12800 384 =
      173528306165896454907625051329373 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 12800 256 128
      76073477281740949587281037056451 97454828884155505320344014272922 h1 levelEleven_energy_13056
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 12800 512 =
      231355986486451916380459986581308 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 12800 384 128
      173528306165896454907625051329373 57827680320555461472834935251935 h2 levelEleven_energy_13184
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_25 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12800 512 =
      5101844206861617509889045 := by
  have h0 := levelEleven_fractional_12800
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12800 256 =
      2161402286863223374235940 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12800 128 128
      1101098348669208805004684 1060303938194014569231256 h0 levelEleven_fractional_12928
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12800 384 =
      3754313423999439552270607 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12800 256 128
      2161402286863223374235940 1592911137136216178034667 h1 levelEleven_fractional_13056
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12800 512 =
      5101844206861617509889045 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12800 384 128
      3754313423999439552270607 1347530782862177957618438 h2 levelEleven_fractional_13184
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_25 : ∀ i : Fin 512,
    levelEleven.lookup (12800 + i.val) ≤ levelElevenRoots.lookup (12800 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_12800
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 12800 128 128
    h0 levelEleven_squares_12928
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 12800 256 128
    h1 levelEleven_squares_13056
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 12800 384 128
    h2 levelEleven_squares_13184
  exact h3

end WordCertDensity.Certificates
