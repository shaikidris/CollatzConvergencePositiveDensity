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
theorem levelEleven_energy_22016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 22016 128 =
      127415157330166887266502530780906 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_22016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22016 128 =
      2178625592474702368378208 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_22016 : ∀ i : Fin 128,
    levelEleven.lookup (22016 + i.val) ≤ levelElevenRoots.lookup (22016 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_22144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 22144 128 =
      22853856378134054305969930063248 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_22144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22144 128 =
      753004117482912513107036 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_22144 : ∀ i : Fin 128,
    levelEleven.lookup (22144 + i.val) ≤ levelElevenRoots.lookup (22144 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_22272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 22272 128 =
      68682109071188416352551669713711 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_22272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22272 128 =
      1527492594769706420173740 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_22272 : ∀ i : Fin 128,
    levelEleven.lookup (22272 + i.val) ≤ levelElevenRoots.lookup (22272 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_22400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 22400 128 =
      34026127092511099079180801016113 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_22400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22400 128 =
      953846740884036497868578 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_22400 : ∀ i : Fin 128,
    levelEleven.lookup (22400 + i.val) ≤ levelElevenRoots.lookup (22400 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_43 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 22016 512 =
      252977249872000457004204931573978 := by
  have h0 := levelEleven_energy_22016
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 22016 256 =
      150269013708300941572472460844154 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 22016 128 128
      127415157330166887266502530780906 22853856378134054305969930063248 h0 levelEleven_energy_22144
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 22016 384 =
      218951122779489357925024130557865 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 22016 256 128
      150269013708300941572472460844154 68682109071188416352551669713711 h1 levelEleven_energy_22272
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 22016 512 =
      252977249872000457004204931573978 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 22016 384 128
      218951122779489357925024130557865 34026127092511099079180801016113 h2 levelEleven_energy_22400
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_43 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22016 512 =
      5412969045611357799527562 := by
  have h0 := levelEleven_fractional_22016
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22016 256 =
      2931629709957614881485244 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22016 128 128
      2178625592474702368378208 753004117482912513107036 h0 levelEleven_fractional_22144
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22016 384 =
      4459122304727321301658984 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22016 256 128
      2931629709957614881485244 1527492594769706420173740 h1 levelEleven_fractional_22272
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22016 512 =
      5412969045611357799527562 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22016 384 128
      4459122304727321301658984 953846740884036497868578 h2 levelEleven_fractional_22400
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_43 : ∀ i : Fin 512,
    levelEleven.lookup (22016 + i.val) ≤ levelElevenRoots.lookup (22016 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_22016
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 22016 128 128
    h0 levelEleven_squares_22144
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 22016 256 128
    h1 levelEleven_squares_22272
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 22016 384 128
    h2 levelEleven_squares_22400
  exact h3

end WordCertDensity.Certificates
