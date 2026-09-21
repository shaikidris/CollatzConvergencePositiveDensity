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
theorem levelEleven_energy_164864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 164864 128 =
      36765511235854636946447208522299 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_164864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164864 128 =
      957856010153579565370466 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_164864 : ∀ i : Fin 128,
    levelEleven.lookup (164864 + i.val) ≤ levelElevenRoots.lookup (164864 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_164992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 164992 128 =
      44674892012594268924422740859961 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_164992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164992 128 =
      1175870935347904735339299 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_164992 : ∀ i : Fin 128,
    levelEleven.lookup (164992 + i.val) ≤ levelElevenRoots.lookup (164992 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_165120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 165120 128 =
      25067750484053224110072756794388 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_165120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165120 128 =
      798393425552424203672846 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_165120 : ∀ i : Fin 128,
    levelEleven.lookup (165120 + i.val) ≤ levelElevenRoots.lookup (165120 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_165248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 165248 128 =
      28604973907113317915053864556629 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_165248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 165248 128 =
      885235726746353789274293 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_165248 : ∀ i : Fin 128,
    levelEleven.lookup (165248 + i.val) ≤ levelElevenRoots.lookup (165248 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_322 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 164864 512 =
      135113127639615447895996570733277 := by
  have h0 := levelEleven_energy_164864
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 164864 256 =
      81440403248448905870869949382260 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 164864 128 128
      36765511235854636946447208522299 44674892012594268924422740859961 h0 levelEleven_energy_164992
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 164864 384 =
      106508153732502129980942706176648 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 164864 256 128
      81440403248448905870869949382260 25067750484053224110072756794388 h1 levelEleven_energy_165120
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 164864 512 =
      135113127639615447895996570733277 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 164864 384 128
      106508153732502129980942706176648 28604973907113317915053864556629 h2 levelEleven_energy_165248
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_322 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164864 512 =
      3817356097800262293656904 := by
  have h0 := levelEleven_fractional_164864
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164864 256 =
      2133726945501484300709765 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164864 128 128
      957856010153579565370466 1175870935347904735339299 h0 levelEleven_fractional_164992
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164864 384 =
      2932120371053908504382611 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164864 256 128
      2133726945501484300709765 798393425552424203672846 h1 levelEleven_fractional_165120
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164864 512 =
      3817356097800262293656904 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 164864 384 128
      2932120371053908504382611 885235726746353789274293 h2 levelEleven_fractional_165248
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_322 : ∀ i : Fin 512,
    levelEleven.lookup (164864 + i.val) ≤ levelElevenRoots.lookup (164864 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_164864
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 164864 128 128
    h0 levelEleven_squares_164992
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 164864 256 128
    h1 levelEleven_squares_165120
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 164864 384 128
    h2 levelEleven_squares_165248
  exact h3

end WordCertDensity.Certificates
