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
theorem levelEleven_energy_43008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 43008 128 =
      27813462058192586156661458555516 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_43008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43008 128 =
      771140431920583352865982 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_43008 : ∀ i : Fin 128,
    levelEleven.lookup (43008 + i.val) ≤ levelElevenRoots.lookup (43008 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_43136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 43136 128 =
      91078113672649478414978766708372 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_43136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43136 128 =
      1623456903897336556756236 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_43136 : ∀ i : Fin 128,
    levelEleven.lookup (43136 + i.val) ≤ levelElevenRoots.lookup (43136 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_43264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 43264 128 =
      37805472236834970462302966947449 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_43264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43264 128 =
      1053583066229921830517174 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_43264 : ∀ i : Fin 128,
    levelEleven.lookup (43264 + i.val) ≤ levelElevenRoots.lookup (43264 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_43392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 43392 128 =
      37317802697303359829137109254088 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_43392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43392 128 =
      993286925534789564179266 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_43392 : ∀ i : Fin 128,
    levelEleven.lookup (43392 + i.val) ≤ levelElevenRoots.lookup (43392 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_84 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 43008 512 =
      194014850664980394863080301465425 := by
  have h0 := levelEleven_energy_43008
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 43008 256 =
      118891575730842064571640225263888 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 43008 128 128
      27813462058192586156661458555516 91078113672649478414978766708372 h0 levelEleven_energy_43136
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 43008 384 =
      156697047967677035033943192211337 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 43008 256 128
      118891575730842064571640225263888 37805472236834970462302966947449 h1 levelEleven_energy_43264
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 43008 512 =
      194014850664980394863080301465425 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 43008 384 128
      156697047967677035033943192211337 37317802697303359829137109254088 h2 levelEleven_energy_43392
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_84 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43008 512 =
      4441467327582631304318658 := by
  have h0 := levelEleven_fractional_43008
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43008 256 =
      2394597335817919909622218 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43008 128 128
      771140431920583352865982 1623456903897336556756236 h0 levelEleven_fractional_43136
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43008 384 =
      3448180402047841740139392 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43008 256 128
      2394597335817919909622218 1053583066229921830517174 h1 levelEleven_fractional_43264
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43008 512 =
      4441467327582631304318658 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 43008 384 128
      3448180402047841740139392 993286925534789564179266 h2 levelEleven_fractional_43392
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_84 : ∀ i : Fin 512,
    levelEleven.lookup (43008 + i.val) ≤ levelElevenRoots.lookup (43008 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_43008
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 43008 128 128
    h0 levelEleven_squares_43136
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 43008 256 128
    h1 levelEleven_squares_43264
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 43008 384 128
    h2 levelEleven_squares_43392
  exact h3

end WordCertDensity.Certificates
