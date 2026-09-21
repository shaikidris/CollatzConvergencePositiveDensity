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
theorem levelEleven_energy_22528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 22528 128 =
      44149091400931041080592164429487 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_22528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22528 128 =
      1064338767718840230465847 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_22528 : ∀ i : Fin 128,
    levelEleven.lookup (22528 + i.val) ≤ levelElevenRoots.lookup (22528 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_22656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 22656 128 =
      263042878320329845040751262400018 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_22656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22656 128 =
      2852861832103048205601310 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_22656 : ∀ i : Fin 128,
    levelEleven.lookup (22656 + i.val) ≤ levelElevenRoots.lookup (22656 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_22784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 22784 128 =
      217927238799103390937589259366308 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_22784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22784 128 =
      2457340177745526250970259 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_22784 : ∀ i : Fin 128,
    levelEleven.lookup (22784 + i.val) ≤ levelElevenRoots.lookup (22784 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_22912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 22912 128 =
      53387029792758398556893112356148 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_22912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22912 128 =
      1330072670705459622178668 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_22912 : ∀ i : Fin 128,
    levelEleven.lookup (22912 + i.val) ≤ levelElevenRoots.lookup (22912 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_44 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 22528 512 =
      578506238313122675615825798551961 := by
  have h0 := levelEleven_energy_22528
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 22528 256 =
      307191969721260886121343426829505 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 22528 128 128
      44149091400931041080592164429487 263042878320329845040751262400018 h0 levelEleven_energy_22656
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 22528 384 =
      525119208520364277058932686195813 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 22528 256 128
      307191969721260886121343426829505 217927238799103390937589259366308 h1 levelEleven_energy_22784
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 22528 512 =
      578506238313122675615825798551961 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 22528 384 128
      525119208520364277058932686195813 53387029792758398556893112356148 h2 levelEleven_energy_22912
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_44 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22528 512 =
      7704613448272874309216084 := by
  have h0 := levelEleven_fractional_22528
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22528 256 =
      3917200599821888436067157 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22528 128 128
      1064338767718840230465847 2852861832103048205601310 h0 levelEleven_fractional_22656
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22528 384 =
      6374540777567414687037416 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22528 256 128
      3917200599821888436067157 2457340177745526250970259 h1 levelEleven_fractional_22784
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22528 512 =
      7704613448272874309216084 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 22528 384 128
      6374540777567414687037416 1330072670705459622178668 h2 levelEleven_fractional_22912
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_44 : ∀ i : Fin 512,
    levelEleven.lookup (22528 + i.val) ≤ levelElevenRoots.lookup (22528 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_22528
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 22528 128 128
    h0 levelEleven_squares_22656
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 22528 256 128
    h1 levelEleven_squares_22784
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 22528 384 128
    h2 levelEleven_squares_22912
  exact h3

end WordCertDensity.Certificates
