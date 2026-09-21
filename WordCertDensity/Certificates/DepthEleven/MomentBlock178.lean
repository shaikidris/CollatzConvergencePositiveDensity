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
theorem levelEleven_energy_91136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 91136 128 =
      14504054213239646715566400941927 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_91136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91136 128 =
      579037241297196033415731 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_91136 : ∀ i : Fin 128,
    levelEleven.lookup (91136 + i.val) ≤ levelElevenRoots.lookup (91136 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_91264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 91264 128 =
      92649812657548547844808749380840 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_91264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91264 128 =
      1600543499979745543634962 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_91264 : ∀ i : Fin 128,
    levelEleven.lookup (91264 + i.val) ≤ levelElevenRoots.lookup (91264 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_91392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 91392 128 =
      25268680264492459164519270409384 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_91392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91392 128 =
      802160655013583893177761 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_91392 : ∀ i : Fin 128,
    levelEleven.lookup (91392 + i.val) ≤ levelElevenRoots.lookup (91392 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_91520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 91520 128 =
      51777306969818712114132151709796 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_91520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91520 128 =
      1235506205107182938504687 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_91520 : ∀ i : Fin 128,
    levelEleven.lookup (91520 + i.val) ≤ levelElevenRoots.lookup (91520 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_178 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 91136 512 =
      184199854105099365839026572441947 := by
  have h0 := levelEleven_energy_91136
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 91136 256 =
      107153866870788194560375150322767 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 91136 128 128
      14504054213239646715566400941927 92649812657548547844808749380840 h0 levelEleven_energy_91264
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 91136 384 =
      132422547135280653724894420732151 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 91136 256 128
      107153866870788194560375150322767 25268680264492459164519270409384 h1 levelEleven_energy_91392
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 91136 512 =
      184199854105099365839026572441947 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 91136 384 128
      132422547135280653724894420732151 51777306969818712114132151709796 h2 levelEleven_energy_91520
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_178 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91136 512 =
      4217247601397708408733141 := by
  have h0 := levelEleven_fractional_91136
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91136 256 =
      2179580741276941577050693 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91136 128 128
      579037241297196033415731 1600543499979745543634962 h0 levelEleven_fractional_91264
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91136 384 =
      2981741396290525470228454 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91136 256 128
      2179580741276941577050693 802160655013583893177761 h1 levelEleven_fractional_91392
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91136 512 =
      4217247601397708408733141 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91136 384 128
      2981741396290525470228454 1235506205107182938504687 h2 levelEleven_fractional_91520
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_178 : ∀ i : Fin 512,
    levelEleven.lookup (91136 + i.val) ≤ levelElevenRoots.lookup (91136 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_91136
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 91136 128 128
    h0 levelEleven_squares_91264
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 91136 256 128
    h1 levelEleven_squares_91392
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 91136 384 128
    h2 levelEleven_squares_91520
  exact h3

end WordCertDensity.Certificates
