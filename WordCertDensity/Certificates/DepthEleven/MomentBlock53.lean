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
theorem levelEleven_energy_27136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 27136 128 =
      23214178796164675677734998279363 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_27136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27136 128 =
      792653106656782160676407 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_27136 : ∀ i : Fin 128,
    levelEleven.lookup (27136 + i.val) ≤ levelElevenRoots.lookup (27136 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_27264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 27264 128 =
      217260741761736253692503192756320 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_27264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27264 128 =
      2553262257387831220073966 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_27264 : ∀ i : Fin 128,
    levelEleven.lookup (27264 + i.val) ≤ levelElevenRoots.lookup (27264 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_27392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 27392 128 =
      22798750828331394345368397018059 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_27392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27392 128 =
      769997153363165714066296 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_27392 : ∀ i : Fin 128,
    levelEleven.lookup (27392 + i.val) ≤ levelElevenRoots.lookup (27392 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_27520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 27520 128 =
      57663445569125512371797201624719 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_27520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27520 128 =
      1341947050250239847611125 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_27520 : ∀ i : Fin 128,
    levelEleven.lookup (27520 + i.val) ≤ levelElevenRoots.lookup (27520 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_53 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 27136 512 =
      320937116955357836087403789678461 := by
  have h0 := levelEleven_energy_27136
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 27136 256 =
      240474920557900929370238191035683 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 27136 128 128
      23214178796164675677734998279363 217260741761736253692503192756320 h0 levelEleven_energy_27264
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 27136 384 =
      263273671386232323715606588053742 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 27136 256 128
      240474920557900929370238191035683 22798750828331394345368397018059 h1 levelEleven_energy_27392
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 27136 512 =
      320937116955357836087403789678461 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 27136 384 128
      263273671386232323715606588053742 57663445569125512371797201624719 h2 levelEleven_energy_27520
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_53 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27136 512 =
      5457859567658018942427794 := by
  have h0 := levelEleven_fractional_27136
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27136 256 =
      3345915364044613380750373 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27136 128 128
      792653106656782160676407 2553262257387831220073966 h0 levelEleven_fractional_27264
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27136 384 =
      4115912517407779094816669 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27136 256 128
      3345915364044613380750373 769997153363165714066296 h1 levelEleven_fractional_27392
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27136 512 =
      5457859567658018942427794 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 27136 384 128
      4115912517407779094816669 1341947050250239847611125 h2 levelEleven_fractional_27520
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_53 : ∀ i : Fin 512,
    levelEleven.lookup (27136 + i.val) ≤ levelElevenRoots.lookup (27136 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_27136
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 27136 128 128
    h0 levelEleven_squares_27264
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 27136 256 128
    h1 levelEleven_squares_27392
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 27136 384 128
    h2 levelEleven_squares_27520
  exact h3

end WordCertDensity.Certificates
