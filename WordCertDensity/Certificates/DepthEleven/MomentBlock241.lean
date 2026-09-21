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
theorem levelEleven_energy_123392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 123392 128 =
      30707260377331182606100731524465 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_123392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123392 128 =
      884354885190302036464533 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_123392 : ∀ i : Fin 128,
    levelEleven.lookup (123392 + i.val) ≤ levelElevenRoots.lookup (123392 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_123520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 123520 128 =
      84406995860328350608535696283653 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_123520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123520 128 =
      1603270368014106989005639 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_123520 : ∀ i : Fin 128,
    levelEleven.lookup (123520 + i.val) ≤ levelElevenRoots.lookup (123520 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_123648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 123648 128 =
      15795543761080591939231579630489 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_123648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123648 128 =
      613688897832833341441277 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_123648 : ∀ i : Fin 128,
    levelEleven.lookup (123648 + i.val) ≤ levelElevenRoots.lookup (123648 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_123776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 123776 128 =
      56713226302292727087760394245229 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_123776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123776 128 =
      1248371581147056294037538 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_123776 : ∀ i : Fin 128,
    levelEleven.lookup (123776 + i.val) ≤ levelElevenRoots.lookup (123776 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_241 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 123392 512 =
      187623026301032852241628401683836 := by
  have h0 := levelEleven_energy_123392
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 123392 256 =
      115114256237659533214636427808118 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 123392 128 128
      30707260377331182606100731524465 84406995860328350608535696283653 h0 levelEleven_energy_123520
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 123392 384 =
      130909799998740125153868007438607 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 123392 256 128
      115114256237659533214636427808118 15795543761080591939231579630489 h1 levelEleven_energy_123648
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 123392 512 =
      187623026301032852241628401683836 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 123392 384 128
      130909799998740125153868007438607 56713226302292727087760394245229 h2 levelEleven_energy_123776
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_241 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123392 512 =
      4349685732184298660948987 := by
  have h0 := levelEleven_fractional_123392
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123392 256 =
      2487625253204409025470172 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123392 128 128
      884354885190302036464533 1603270368014106989005639 h0 levelEleven_fractional_123520
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123392 384 =
      3101314151037242366911449 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123392 256 128
      2487625253204409025470172 613688897832833341441277 h1 levelEleven_fractional_123648
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123392 512 =
      4349685732184298660948987 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123392 384 128
      3101314151037242366911449 1248371581147056294037538 h2 levelEleven_fractional_123776
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_241 : ∀ i : Fin 512,
    levelEleven.lookup (123392 + i.val) ≤ levelElevenRoots.lookup (123392 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_123392
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 123392 128 128
    h0 levelEleven_squares_123520
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 123392 256 128
    h1 levelEleven_squares_123648
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 123392 384 128
    h2 levelEleven_squares_123776
  exact h3

end WordCertDensity.Certificates
