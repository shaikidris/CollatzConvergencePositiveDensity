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
theorem levelEleven_energy_147456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 147456 128 =
      35511623374445179226576971326950 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_147456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147456 128 =
      1003444248449338301083175 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_147456 : ∀ i : Fin 128,
    levelEleven.lookup (147456 + i.val) ≤ levelElevenRoots.lookup (147456 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_147584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 147584 128 =
      205950288940162093274842499003266 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_147584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147584 128 =
      2493509586221116553960408 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_147584 : ∀ i : Fin 128,
    levelEleven.lookup (147584 + i.val) ≤ levelElevenRoots.lookup (147584 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_147712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 147712 128 =
      29194447965492124207820059016241 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_147712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147712 128 =
      862208868844691455663853 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_147712 : ∀ i : Fin 128,
    levelEleven.lookup (147712 + i.val) ≤ levelElevenRoots.lookup (147712 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_147840 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 147840 128 =
      83765174469979149237193381708599 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_147840 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147840 128 =
      1644788450099117395985943 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_147840 : ∀ i : Fin 128,
    levelEleven.lookup (147840 + i.val) ≤ levelElevenRoots.lookup (147840 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 147456 512 =
      354421534750078545946432911055056 := by
  have h0 := levelEleven_energy_147456
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 147456 256 =
      241461912314607272501419470330216 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 147456 128 128
      35511623374445179226576971326950 205950288940162093274842499003266 h0 levelEleven_energy_147584
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 147456 384 =
      270656360280099396709239529346457 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 147456 256 128
      241461912314607272501419470330216 29194447965492124207820059016241 h1 levelEleven_energy_147712
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 147456 512 =
      354421534750078545946432911055056 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 147456 384 128
      270656360280099396709239529346457 83765174469979149237193381708599 h2 levelEleven_energy_147840
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147456 512 =
      6003951153614263706693379 := by
  have h0 := levelEleven_fractional_147456
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147456 256 =
      3496953834670454855043583 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147456 128 128
      1003444248449338301083175 2493509586221116553960408 h0 levelEleven_fractional_147584
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147456 384 =
      4359162703515146310707436 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147456 256 128
      3496953834670454855043583 862208868844691455663853 h1 levelEleven_fractional_147712
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147456 512 =
      6003951153614263706693379 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 147456 384 128
      4359162703515146310707436 1644788450099117395985943 h2 levelEleven_fractional_147840
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_288 : ∀ i : Fin 512,
    levelEleven.lookup (147456 + i.val) ≤ levelElevenRoots.lookup (147456 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_147456
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 147456 128 128
    h0 levelEleven_squares_147584
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 147456 256 128
    h1 levelEleven_squares_147712
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 147456 384 128
    h2 levelEleven_squares_147840
  exact h3

end WordCertDensity.Certificates
