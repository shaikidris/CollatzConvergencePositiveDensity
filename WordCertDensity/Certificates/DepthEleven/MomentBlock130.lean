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
theorem levelEleven_energy_66560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 66560 128 =
      26801893913582614366176317468660 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_66560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66560 128 =
      862013573246801231186762 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_66560 : ∀ i : Fin 128,
    levelEleven.lookup (66560 + i.val) ≤ levelElevenRoots.lookup (66560 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_66688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 66688 128 =
      42764738092346627577414069695061 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_66688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66688 128 =
      1123685212046683625658111 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_66688 : ∀ i : Fin 128,
    levelEleven.lookup (66688 + i.val) ≤ levelElevenRoots.lookup (66688 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_66816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 66816 128 =
      47991646146459361925873383305174 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_66816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66816 128 =
      1140322252231586066141084 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_66816 : ∀ i : Fin 128,
    levelEleven.lookup (66816 + i.val) ≤ levelElevenRoots.lookup (66816 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_66944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 66944 128 =
      42390153838168157917471109322277 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_66944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66944 128 =
      1116060987168327625453768 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_66944 : ∀ i : Fin 128,
    levelEleven.lookup (66944 + i.val) ≤ levelElevenRoots.lookup (66944 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_130 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 66560 512 =
      159948431990556761786934879791172 := by
  have h0 := levelEleven_energy_66560
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 66560 256 =
      69566632005929241943590387163721 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 66560 128 128
      26801893913582614366176317468660 42764738092346627577414069695061 h0 levelEleven_energy_66688
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 66560 384 =
      117558278152388603869463770468895 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 66560 256 128
      69566632005929241943590387163721 47991646146459361925873383305174 h1 levelEleven_energy_66816
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 66560 512 =
      159948431990556761786934879791172 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 66560 384 128
      117558278152388603869463770468895 42390153838168157917471109322277 h2 levelEleven_energy_66944
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_130 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66560 512 =
      4242082024693398548439725 := by
  have h0 := levelEleven_fractional_66560
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66560 256 =
      1985698785293484856844873 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66560 128 128
      862013573246801231186762 1123685212046683625658111 h0 levelEleven_fractional_66688
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66560 384 =
      3126021037525070922985957 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66560 256 128
      1985698785293484856844873 1140322252231586066141084 h1 levelEleven_fractional_66816
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66560 512 =
      4242082024693398548439725 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 66560 384 128
      3126021037525070922985957 1116060987168327625453768 h2 levelEleven_fractional_66944
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_130 : ∀ i : Fin 512,
    levelEleven.lookup (66560 + i.val) ≤ levelElevenRoots.lookup (66560 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_66560
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 66560 128 128
    h0 levelEleven_squares_66688
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 66560 256 128
    h1 levelEleven_squares_66816
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 66560 384 128
    h2 levelEleven_squares_66944
  exact h3

end WordCertDensity.Certificates
