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
theorem levelEleven_energy_91648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 91648 128 =
      38554663287745267110370579533201 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_91648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91648 128 =
      1043160126819021620531340 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_91648 : ∀ i : Fin 128,
    levelEleven.lookup (91648 + i.val) ≤ levelElevenRoots.lookup (91648 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_91776 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 91776 128 =
      88907468649047212795244251582800 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_91776 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91776 128 =
      1645629558829387547352669 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_91776 : ∀ i : Fin 128,
    levelEleven.lookup (91776 + i.val) ≤ levelElevenRoots.lookup (91776 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_91904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 91904 128 =
      31089657608644243172531666935607 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_91904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91904 128 =
      938331264849840625662711 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_91904 : ∀ i : Fin 128,
    levelEleven.lookup (91904 + i.val) ≤ levelElevenRoots.lookup (91904 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_92032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 92032 128 =
      239543948673563175677029719286175 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_92032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92032 128 =
      2762593402720304659902396 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_92032 : ∀ i : Fin 128,
    levelEleven.lookup (92032 + i.val) ≤ levelElevenRoots.lookup (92032 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_179 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 91648 512 =
      398095738218999898755176217337783 := by
  have h0 := levelEleven_energy_91648
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 91648 256 =
      127462131936792479905614831116001 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 91648 128 128
      38554663287745267110370579533201 88907468649047212795244251582800 h0 levelEleven_energy_91776
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 91648 384 =
      158551789545436723078146498051608 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 91648 256 128
      127462131936792479905614831116001 31089657608644243172531666935607 h1 levelEleven_energy_91904
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 91648 512 =
      398095738218999898755176217337783 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 91648 384 128
      158551789545436723078146498051608 239543948673563175677029719286175 h2 levelEleven_energy_92032
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_179 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91648 512 =
      6389714353218554453449116 := by
  have h0 := levelEleven_fractional_91648
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91648 256 =
      2688789685648409167884009 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91648 128 128
      1043160126819021620531340 1645629558829387547352669 h0 levelEleven_fractional_91776
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91648 384 =
      3627120950498249793546720 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91648 256 128
      2688789685648409167884009 938331264849840625662711 h1 levelEleven_fractional_91904
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91648 512 =
      6389714353218554453449116 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91648 384 128
      3627120950498249793546720 2762593402720304659902396 h2 levelEleven_fractional_92032
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_179 : ∀ i : Fin 512,
    levelEleven.lookup (91648 + i.val) ≤ levelElevenRoots.lookup (91648 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_91648
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 91648 128 128
    h0 levelEleven_squares_91776
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 91648 256 128
    h1 levelEleven_squares_91904
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 91648 384 128
    h2 levelEleven_squares_92032
  exact h3

end WordCertDensity.Certificates
