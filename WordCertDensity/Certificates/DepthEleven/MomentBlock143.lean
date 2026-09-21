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
theorem levelEleven_energy_73216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 73216 128 =
      51229191157196801563094812444972 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_73216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73216 128 =
      1241364020558745840807973 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_73216 : ∀ i : Fin 128,
    levelEleven.lookup (73216 + i.val) ≤ levelElevenRoots.lookup (73216 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_73344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 73344 128 =
      16849452294904314955968530343263 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_73344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73344 128 =
      658999596130148608114476 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_73344 : ∀ i : Fin 128,
    levelEleven.lookup (73344 + i.val) ≤ levelElevenRoots.lookup (73344 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_73472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 73472 128 =
      40509718408831949278719515045346 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_73472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73472 128 =
      1044665669689425135008415 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_73472 : ∀ i : Fin 128,
    levelEleven.lookup (73472 + i.val) ≤ levelElevenRoots.lookup (73472 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_73600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 73600 128 =
      37407662888729764168881919100473 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_73600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73600 128 =
      893824977774185239259431 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_73600 : ∀ i : Fin 128,
    levelEleven.lookup (73600 + i.val) ≤ levelElevenRoots.lookup (73600 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_143 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 73216 512 =
      145996024749662829966664776934054 := by
  have h0 := levelEleven_energy_73216
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 73216 256 =
      68078643452101116519063342788235 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 73216 128 128
      51229191157196801563094812444972 16849452294904314955968530343263 h0 levelEleven_energy_73344
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 73216 384 =
      108588361860933065797782857833581 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 73216 256 128
      68078643452101116519063342788235 40509718408831949278719515045346 h1 levelEleven_energy_73472
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 73216 512 =
      145996024749662829966664776934054 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 73216 384 128
      108588361860933065797782857833581 37407662888729764168881919100473 h2 levelEleven_energy_73600
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_143 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73216 512 =
      3838854264152504823190295 := by
  have h0 := levelEleven_fractional_73216
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73216 256 =
      1900363616688894448922449 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73216 128 128
      1241364020558745840807973 658999596130148608114476 h0 levelEleven_fractional_73344
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73216 384 =
      2945029286378319583930864 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73216 256 128
      1900363616688894448922449 1044665669689425135008415 h1 levelEleven_fractional_73472
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73216 512 =
      3838854264152504823190295 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 73216 384 128
      2945029286378319583930864 893824977774185239259431 h2 levelEleven_fractional_73600
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_143 : ∀ i : Fin 512,
    levelEleven.lookup (73216 + i.val) ≤ levelElevenRoots.lookup (73216 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_73216
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 73216 128 128
    h0 levelEleven_squares_73344
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 73216 256 128
    h1 levelEleven_squares_73472
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 73216 384 128
    h2 levelEleven_squares_73600
  exact h3

end WordCertDensity.Certificates
