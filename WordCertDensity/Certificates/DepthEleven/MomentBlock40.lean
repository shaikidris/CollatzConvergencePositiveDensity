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
theorem levelEleven_energy_20480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 20480 128 =
      106840991316221488912060999755312 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_20480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20480 128 =
      1864221085749561668302519 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_20480 : ∀ i : Fin 128,
    levelEleven.lookup (20480 + i.val) ≤ levelElevenRoots.lookup (20480 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_20608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 20608 128 =
      33942818130911793173422146246637 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_20608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20608 128 =
      909267622940479570472538 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_20608 : ∀ i : Fin 128,
    levelEleven.lookup (20608 + i.val) ≤ levelElevenRoots.lookup (20608 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_20736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 20736 128 =
      216853889537648875150996671473847 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_20736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20736 128 =
      2528926685772345041282606 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_20736 : ∀ i : Fin 128,
    levelEleven.lookup (20736 + i.val) ≤ levelElevenRoots.lookup (20736 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_20864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 20864 128 =
      20279992763660054781272156558686 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_20864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20864 128 =
      703482154824730467452726 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_20864 : ∀ i : Fin 128,
    levelEleven.lookup (20864 + i.val) ≤ levelElevenRoots.lookup (20864 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_40 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 20480 512 =
      377917691748442212017751974034482 := by
  have h0 := levelEleven_energy_20480
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 20480 256 =
      140783809447133282085483146001949 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 20480 128 128
      106840991316221488912060999755312 33942818130911793173422146246637 h0 levelEleven_energy_20608
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 20480 384 =
      357637698984782157236479817475796 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 20480 256 128
      140783809447133282085483146001949 216853889537648875150996671473847 h1 levelEleven_energy_20736
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 20480 512 =
      377917691748442212017751974034482 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 20480 384 128
      357637698984782157236479817475796 20279992763660054781272156558686 h2 levelEleven_energy_20864
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_40 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20480 512 =
      6005897549287116747510389 := by
  have h0 := levelEleven_fractional_20480
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20480 256 =
      2773488708690041238775057 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20480 128 128
      1864221085749561668302519 909267622940479570472538 h0 levelEleven_fractional_20608
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20480 384 =
      5302415394462386280057663 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20480 256 128
      2773488708690041238775057 2528926685772345041282606 h1 levelEleven_fractional_20736
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20480 512 =
      6005897549287116747510389 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 20480 384 128
      5302415394462386280057663 703482154824730467452726 h2 levelEleven_fractional_20864
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_40 : ∀ i : Fin 512,
    levelEleven.lookup (20480 + i.val) ≤ levelElevenRoots.lookup (20480 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_20480
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 20480 128 128
    h0 levelEleven_squares_20608
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 20480 256 128
    h1 levelEleven_squares_20736
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 20480 384 128
    h2 levelEleven_squares_20864
  exact h3

end WordCertDensity.Certificates
