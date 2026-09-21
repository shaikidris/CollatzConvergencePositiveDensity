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
theorem levelEleven_energy_50688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 50688 128 =
      64462784285626841864755712441927 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_50688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50688 128 =
      1415108025538999312269745 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_50688 : ∀ i : Fin 128,
    levelEleven.lookup (50688 + i.val) ≤ levelElevenRoots.lookup (50688 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_50816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 50816 128 =
      29962241583505879594117537265721 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_50816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50816 128 =
      836461418480083161395151 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_50816 : ∀ i : Fin 128,
    levelEleven.lookup (50816 + i.val) ≤ levelElevenRoots.lookup (50816 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_50944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 50944 128 =
      25216858211174521209388071301816 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_50944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50944 128 =
      835130476910567551323890 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_50944 : ∀ i : Fin 128,
    levelEleven.lookup (50944 + i.val) ≤ levelElevenRoots.lookup (50944 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_51072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 51072 128 =
      55782516669193623997245206561036 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_51072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51072 128 =
      1230883690276092586576598 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_51072 : ∀ i : Fin 128,
    levelEleven.lookup (51072 + i.val) ≤ levelElevenRoots.lookup (51072 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_99 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 50688 512 =
      175424400749500866665506527570500 := by
  have h0 := levelEleven_energy_50688
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 50688 256 =
      94425025869132721458873249707648 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 50688 128 128
      64462784285626841864755712441927 29962241583505879594117537265721 h0 levelEleven_energy_50816
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 50688 384 =
      119641884080307242668261321009464 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 50688 256 128
      94425025869132721458873249707648 25216858211174521209388071301816 h1 levelEleven_energy_50944
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 50688 512 =
      175424400749500866665506527570500 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 50688 384 128
      119641884080307242668261321009464 55782516669193623997245206561036 h2 levelEleven_energy_51072
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_99 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50688 512 =
      4317583611205742611565384 := by
  have h0 := levelEleven_fractional_50688
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50688 256 =
      2251569444019082473664896 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50688 128 128
      1415108025538999312269745 836461418480083161395151 h0 levelEleven_fractional_50816
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50688 384 =
      3086699920929650024988786 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50688 256 128
      2251569444019082473664896 835130476910567551323890 h1 levelEleven_fractional_50944
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50688 512 =
      4317583611205742611565384 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50688 384 128
      3086699920929650024988786 1230883690276092586576598 h2 levelEleven_fractional_51072
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_99 : ∀ i : Fin 512,
    levelEleven.lookup (50688 + i.val) ≤ levelElevenRoots.lookup (50688 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_50688
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 50688 128 128
    h0 levelEleven_squares_50816
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 50688 256 128
    h1 levelEleven_squares_50944
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 50688 384 128
    h2 levelEleven_squares_51072
  exact h3

end WordCertDensity.Certificates
