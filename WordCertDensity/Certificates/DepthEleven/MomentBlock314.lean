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
theorem levelEleven_energy_160768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 160768 128 =
      34222527635879509133703927530140 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_160768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160768 128 =
      1021288066223633615164449 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_160768 : ∀ i : Fin 128,
    levelEleven.lookup (160768 + i.val) ≤ levelElevenRoots.lookup (160768 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_160896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 160896 128 =
      37560694677791071683437521435701 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_160896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160896 128 =
      982342005306677812916403 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_160896 : ∀ i : Fin 128,
    levelEleven.lookup (160896 + i.val) ≤ levelElevenRoots.lookup (160896 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_161024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 161024 128 =
      67013182977248295444575263863441 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_161024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161024 128 =
      1420157479721713563462720 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_161024 : ∀ i : Fin 128,
    levelEleven.lookup (161024 + i.val) ≤ levelElevenRoots.lookup (161024 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_161152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 161152 128 =
      18938980682182679208921511125199 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_161152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 161152 128 =
      678658941793162737284551 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_161152 : ∀ i : Fin 128,
    levelEleven.lookup (161152 + i.val) ≤ levelElevenRoots.lookup (161152 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_314 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 160768 512 =
      157735385973101555470638223954481 := by
  have h0 := levelEleven_energy_160768
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 160768 256 =
      71783222313670580817141448965841 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 160768 128 128
      34222527635879509133703927530140 37560694677791071683437521435701 h0 levelEleven_energy_160896
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 160768 384 =
      138796405290918876261716712829282 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 160768 256 128
      71783222313670580817141448965841 67013182977248295444575263863441 h1 levelEleven_energy_161024
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 160768 512 =
      157735385973101555470638223954481 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 160768 384 128
      138796405290918876261716712829282 18938980682182679208921511125199 h2 levelEleven_energy_161152
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_314 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160768 512 =
      4102446493045187728828123 := by
  have h0 := levelEleven_fractional_160768
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160768 256 =
      2003630071530311428080852 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160768 128 128
      1021288066223633615164449 982342005306677812916403 h0 levelEleven_fractional_160896
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160768 384 =
      3423787551252024991543572 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160768 256 128
      2003630071530311428080852 1420157479721713563462720 h1 levelEleven_fractional_161024
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160768 512 =
      4102446493045187728828123 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 160768 384 128
      3423787551252024991543572 678658941793162737284551 h2 levelEleven_fractional_161152
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_314 : ∀ i : Fin 512,
    levelEleven.lookup (160768 + i.val) ≤ levelElevenRoots.lookup (160768 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_160768
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 160768 128 128
    h0 levelEleven_squares_160896
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 160768 256 128
    h1 levelEleven_squares_161024
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 160768 384 128
    h2 levelEleven_squares_161152
  exact h3

end WordCertDensity.Certificates
