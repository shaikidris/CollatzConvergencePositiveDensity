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
theorem levelEleven_energy_30720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 30720 128 =
      96426547734704908279608409850112 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_30720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30720 128 =
      1733229647686800940451405 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_30720 : ∀ i : Fin 128,
    levelEleven.lookup (30720 + i.val) ≤ levelElevenRoots.lookup (30720 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_30848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 30848 128 =
      80154842262755829385652231452995 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_30848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30848 128 =
      1528069228046454846175984 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_30848 : ∀ i : Fin 128,
    levelEleven.lookup (30848 + i.val) ≤ levelElevenRoots.lookup (30848 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_30976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 30976 128 =
      51788544315622380188494735928783 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_30976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30976 128 =
      1219357927279911394415019 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_30976 : ∀ i : Fin 128,
    levelEleven.lookup (30976 + i.val) ≤ levelElevenRoots.lookup (30976 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_31104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 31104 128 =
      19361283578127286317707300448254 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_31104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 31104 128 =
      699343028389236853450266 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_31104 : ∀ i : Fin 128,
    levelEleven.lookup (31104 + i.val) ≤ levelElevenRoots.lookup (31104 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_60 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 30720 512 =
      247731217891210404171462677680144 := by
  have h0 := levelEleven_energy_30720
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 30720 256 =
      176581389997460737665260641303107 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 30720 128 128
      96426547734704908279608409850112 80154842262755829385652231452995 h0 levelEleven_energy_30848
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 30720 384 =
      228369934313083117853755377231890 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 30720 256 128
      176581389997460737665260641303107 51788544315622380188494735928783 h1 levelEleven_energy_30976
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 30720 512 =
      247731217891210404171462677680144 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 30720 384 128
      228369934313083117853755377231890 19361283578127286317707300448254 h2 levelEleven_energy_31104
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_60 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30720 512 =
      5179999831402404034492674 := by
  have h0 := levelEleven_fractional_30720
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30720 256 =
      3261298875733255786627389 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30720 128 128
      1733229647686800940451405 1528069228046454846175984 h0 levelEleven_fractional_30848
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30720 384 =
      4480656803013167181042408 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30720 256 128
      3261298875733255786627389 1219357927279911394415019 h1 levelEleven_fractional_30976
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30720 512 =
      5179999831402404034492674 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 30720 384 128
      4480656803013167181042408 699343028389236853450266 h2 levelEleven_fractional_31104
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_60 : ∀ i : Fin 512,
    levelEleven.lookup (30720 + i.val) ≤ levelElevenRoots.lookup (30720 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_30720
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 30720 128 128
    h0 levelEleven_squares_30848
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 30720 256 128
    h1 levelEleven_squares_30976
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 30720 384 128
    h2 levelEleven_squares_31104
  exact h3

end WordCertDensity.Certificates
