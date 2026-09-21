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
theorem levelEleven_energy_5120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 5120 128 =
      15720318992891610684365581655062 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_5120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5120 128 =
      612623036641659008555568 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_5120 : ∀ i : Fin 128,
    levelEleven.lookup (5120 + i.val) ≤ levelElevenRoots.lookup (5120 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_5248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 5248 128 =
      81932339141612423406194441910365 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_5248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5248 128 =
      1571346479261748691937397 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_5248 : ∀ i : Fin 128,
    levelEleven.lookup (5248 + i.val) ≤ levelElevenRoots.lookup (5248 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_5376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 5376 128 =
      50635146428279651346623192375533 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_5376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5376 128 =
      1136133247723617891485879 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_5376 : ∀ i : Fin 128,
    levelEleven.lookup (5376 + i.val) ≤ levelElevenRoots.lookup (5376 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_5504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 5504 128 =
      71209755110567790002612593897571 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_5504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5504 128 =
      1386668197741355359617646 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_5504 : ∀ i : Fin 128,
    levelEleven.lookup (5504 + i.val) ≤ levelElevenRoots.lookup (5504 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_10 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 5120 512 =
      219497559673351475439795809838531 := by
  have h0 := levelEleven_energy_5120
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 5120 256 =
      97652658134504034090560023565427 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 5120 128 128
      15720318992891610684365581655062 81932339141612423406194441910365 h0 levelEleven_energy_5248
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 5120 384 =
      148287804562783685437183215940960 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 5120 256 128
      97652658134504034090560023565427 50635146428279651346623192375533 h1 levelEleven_energy_5376
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 5120 512 =
      219497559673351475439795809838531 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 5120 384 128
      148287804562783685437183215940960 71209755110567790002612593897571 h2 levelEleven_energy_5504
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_10 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5120 512 =
      4706770961368380951596490 := by
  have h0 := levelEleven_fractional_5120
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5120 256 =
      2183969515903407700492965 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5120 128 128
      612623036641659008555568 1571346479261748691937397 h0 levelEleven_fractional_5248
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5120 384 =
      3320102763627025591978844 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5120 256 128
      2183969515903407700492965 1136133247723617891485879 h1 levelEleven_fractional_5376
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5120 512 =
      4706770961368380951596490 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 5120 384 128
      3320102763627025591978844 1386668197741355359617646 h2 levelEleven_fractional_5504
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_10 : ∀ i : Fin 512,
    levelEleven.lookup (5120 + i.val) ≤ levelElevenRoots.lookup (5120 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_5120
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 5120 128 128
    h0 levelEleven_squares_5248
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 5120 256 128
    h1 levelEleven_squares_5376
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 5120 384 128
    h2 levelEleven_squares_5504
  exact h3

end WordCertDensity.Certificates
