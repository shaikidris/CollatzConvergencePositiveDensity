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
theorem levelEleven_energy_153088 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 153088 128 =
      54325042589295739717230839271659 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_153088 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153088 128 =
      1097889741593100684829750 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_153088 : ∀ i : Fin 128,
    levelEleven.lookup (153088 + i.val) ≤ levelElevenRoots.lookup (153088 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_153216 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 153216 128 =
      33461143098638392040679112611128 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_153216 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153216 128 =
      980291790374846046204840 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_153216 : ∀ i : Fin 128,
    levelEleven.lookup (153216 + i.val) ≤ levelElevenRoots.lookup (153216 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_153344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 153344 128 =
      29650351942707366235878897116536 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_153344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153344 128 =
      913348002416053024480636 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_153344 : ∀ i : Fin 128,
    levelEleven.lookup (153344 + i.val) ≤ levelElevenRoots.lookup (153344 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_153472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 153472 128 =
      66174906789104149249444462981444 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_153472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153472 128 =
      1449017681871041259341855 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_153472 : ∀ i : Fin 128,
    levelEleven.lookup (153472 + i.val) ≤ levelElevenRoots.lookup (153472 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_299 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 153088 512 =
      183611444419745647243233311980767 := by
  have h0 := levelEleven_energy_153088
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 153088 256 =
      87786185687934131757909951882787 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 153088 128 128
      54325042589295739717230839271659 33461143098638392040679112611128 h0 levelEleven_energy_153216
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 153088 384 =
      117436537630641497993788848999323 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 153088 256 128
      87786185687934131757909951882787 29650351942707366235878897116536 h1 levelEleven_energy_153344
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 153088 512 =
      183611444419745647243233311980767 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 153088 384 128
      117436537630641497993788848999323 66174906789104149249444462981444 h2 levelEleven_energy_153472
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_299 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153088 512 =
      4440547216255041014857081 := by
  have h0 := levelEleven_fractional_153088
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153088 256 =
      2078181531967946731034590 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153088 128 128
      1097889741593100684829750 980291790374846046204840 h0 levelEleven_fractional_153216
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153088 384 =
      2991529534383999755515226 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153088 256 128
      2078181531967946731034590 913348002416053024480636 h1 levelEleven_fractional_153344
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153088 512 =
      4440547216255041014857081 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 153088 384 128
      2991529534383999755515226 1449017681871041259341855 h2 levelEleven_fractional_153472
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_299 : ∀ i : Fin 512,
    levelEleven.lookup (153088 + i.val) ≤ levelElevenRoots.lookup (153088 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_153088
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 153088 128 128
    h0 levelEleven_squares_153216
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 153088 256 128
    h1 levelEleven_squares_153344
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 153088 384 128
    h2 levelEleven_squares_153472
  exact h3

end WordCertDensity.Certificates
