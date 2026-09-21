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
theorem levelEleven_energy_33280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 33280 128 =
      46733041520136210569561283621124 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_33280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33280 128 =
      1183055875954633302635473 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_33280 : ∀ i : Fin 128,
    levelEleven.lookup (33280 + i.val) ≤ levelElevenRoots.lookup (33280 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_33408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 33408 128 =
      106691442276378831301473495853238 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_33408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33408 128 =
      1886307446070850701644842 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_33408 : ∀ i : Fin 128,
    levelEleven.lookup (33408 + i.val) ≤ levelElevenRoots.lookup (33408 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_33536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 33536 128 =
      21113636666346474466921478132121 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_33536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33536 128 =
      698970377029871496781536 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_33536 : ∀ i : Fin 128,
    levelEleven.lookup (33536 + i.val) ≤ levelElevenRoots.lookup (33536 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_33664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 33664 128 =
      64815088321697719826158348883678 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_33664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33664 128 =
      1379365796711088457130336 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_33664 : ∀ i : Fin 128,
    levelEleven.lookup (33664 + i.val) ≤ levelElevenRoots.lookup (33664 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_65 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 33280 512 =
      239353208784559236164114606490161 := by
  have h0 := levelEleven_energy_33280
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 33280 256 =
      153424483796515041871034779474362 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 33280 128 128
      46733041520136210569561283621124 106691442276378831301473495853238 h0 levelEleven_energy_33408
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 33280 384 =
      174538120462861516337956257606483 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 33280 256 128
      153424483796515041871034779474362 21113636666346474466921478132121 h1 levelEleven_energy_33536
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 33280 512 =
      239353208784559236164114606490161 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 33280 384 128
      174538120462861516337956257606483 64815088321697719826158348883678 h2 levelEleven_energy_33664
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_65 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33280 512 =
      5147699495766443958192187 := by
  have h0 := levelEleven_fractional_33280
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33280 256 =
      3069363322025484004280315 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33280 128 128
      1183055875954633302635473 1886307446070850701644842 h0 levelEleven_fractional_33408
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33280 384 =
      3768333699055355501061851 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33280 256 128
      3069363322025484004280315 698970377029871496781536 h1 levelEleven_fractional_33536
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33280 512 =
      5147699495766443958192187 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 33280 384 128
      3768333699055355501061851 1379365796711088457130336 h2 levelEleven_fractional_33664
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_65 : ∀ i : Fin 512,
    levelEleven.lookup (33280 + i.val) ≤ levelElevenRoots.lookup (33280 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_33280
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 33280 128 128
    h0 levelEleven_squares_33408
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 33280 256 128
    h1 levelEleven_squares_33536
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 33280 384 128
    h2 levelEleven_squares_33664
  exact h3

end WordCertDensity.Certificates
