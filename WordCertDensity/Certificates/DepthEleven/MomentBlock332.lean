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
theorem levelEleven_energy_169984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 169984 128 =
      57613804942436623442821912991810 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_169984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169984 128 =
      1293383752627299003526326 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_169984 : ∀ i : Fin 128,
    levelEleven.lookup (169984 + i.val) ≤ levelElevenRoots.lookup (169984 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_170112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 170112 128 =
      46825432126494750562693097920942 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_170112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170112 128 =
      1179518616641228835038807 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_170112 : ∀ i : Fin 128,
    levelEleven.lookup (170112 + i.val) ≤ levelElevenRoots.lookup (170112 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_170240 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 170240 128 =
      25972770480309736538155289250066 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_170240 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170240 128 =
      861219385489284566338144 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_170240 : ∀ i : Fin 128,
    levelEleven.lookup (170240 + i.val) ≤ levelElevenRoots.lookup (170240 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_170368 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 170368 128 =
      47761463425318041886733448433204 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_170368 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 170368 128 =
      1066972584295453273095307 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_170368 : ∀ i : Fin 128,
    levelEleven.lookup (170368 + i.val) ≤ levelElevenRoots.lookup (170368 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_332 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 169984 512 =
      178173470974559152430403748596022 := by
  have h0 := levelEleven_energy_169984
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 169984 256 =
      104439237068931374005515010912752 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 169984 128 128
      57613804942436623442821912991810 46825432126494750562693097920942 h0 levelEleven_energy_170112
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 169984 384 =
      130412007549241110543670300162818 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 169984 256 128
      104439237068931374005515010912752 25972770480309736538155289250066 h1 levelEleven_energy_170240
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 169984 512 =
      178173470974559152430403748596022 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 169984 384 128
      130412007549241110543670300162818 47761463425318041886733448433204 h2 levelEleven_energy_170368
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_332 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169984 512 =
      4401094339053265677998584 := by
  have h0 := levelEleven_fractional_169984
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169984 256 =
      2472902369268527838565133 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169984 128 128
      1293383752627299003526326 1179518616641228835038807 h0 levelEleven_fractional_170112
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169984 384 =
      3334121754757812404903277 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169984 256 128
      2472902369268527838565133 861219385489284566338144 h1 levelEleven_fractional_170240
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169984 512 =
      4401094339053265677998584 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 169984 384 128
      3334121754757812404903277 1066972584295453273095307 h2 levelEleven_fractional_170368
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_332 : ∀ i : Fin 512,
    levelEleven.lookup (169984 + i.val) ≤ levelElevenRoots.lookup (169984 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_169984
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 169984 128 128
    h0 levelEleven_squares_170112
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 169984 256 128
    h1 levelEleven_squares_170240
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 169984 384 128
    h2 levelEleven_squares_170368
  exact h3

end WordCertDensity.Certificates
