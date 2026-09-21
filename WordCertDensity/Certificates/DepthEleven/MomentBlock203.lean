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
theorem levelEleven_energy_103936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 103936 128 =
      34824113866038776824017539017093 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_103936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103936 128 =
      949266137473448789099428 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_103936 : ∀ i : Fin 128,
    levelEleven.lookup (103936 + i.val) ≤ levelElevenRoots.lookup (103936 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_104064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 104064 128 =
      42530231265775099609874719913313 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_104064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104064 128 =
      1059107475646815645307577 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_104064 : ∀ i : Fin 128,
    levelEleven.lookup (104064 + i.val) ≤ levelElevenRoots.lookup (104064 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_104192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 104192 128 =
      48098989824886931344731180961897 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_104192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104192 128 =
      1121484757636416079068599 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_104192 : ∀ i : Fin 128,
    levelEleven.lookup (104192 + i.val) ≤ levelElevenRoots.lookup (104192 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_104320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 104320 128 =
      50194950832511317165744834238073 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_104320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 104320 128 =
      1240805679377270004227663 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_104320 : ∀ i : Fin 128,
    levelEleven.lookup (104320 + i.val) ≤ levelElevenRoots.lookup (104320 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_203 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 103936 512 =
      175648285789212124944368274130376 := by
  have h0 := levelEleven_energy_103936
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 103936 256 =
      77354345131813876433892258930406 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 103936 128 128
      34824113866038776824017539017093 42530231265775099609874719913313 h0 levelEleven_energy_104064
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 103936 384 =
      125453334956700807778623439892303 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 103936 256 128
      77354345131813876433892258930406 48098989824886931344731180961897 h1 levelEleven_energy_104192
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 103936 512 =
      175648285789212124944368274130376 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 103936 384 128
      125453334956700807778623439892303 50194950832511317165744834238073 h2 levelEleven_energy_104320
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_203 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103936 512 =
      4370664050133950517703267 := by
  have h0 := levelEleven_fractional_103936
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103936 256 =
      2008373613120264434407005 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103936 128 128
      949266137473448789099428 1059107475646815645307577 h0 levelEleven_fractional_104064
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103936 384 =
      3129858370756680513475604 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103936 256 128
      2008373613120264434407005 1121484757636416079068599 h1 levelEleven_fractional_104192
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103936 512 =
      4370664050133950517703267 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103936 384 128
      3129858370756680513475604 1240805679377270004227663 h2 levelEleven_fractional_104320
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_203 : ∀ i : Fin 512,
    levelEleven.lookup (103936 + i.val) ≤ levelElevenRoots.lookup (103936 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_103936
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 103936 128 128
    h0 levelEleven_squares_104064
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 103936 256 128
    h1 levelEleven_squares_104192
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 103936 384 128
    h2 levelEleven_squares_104320
  exact h3

end WordCertDensity.Certificates
