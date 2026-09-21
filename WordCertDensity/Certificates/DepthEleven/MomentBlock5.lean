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
theorem levelEleven_energy_2560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 2560 128 =
      55457385240819015300735894794148 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_2560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2560 128 =
      1291631191369494151000157 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_2560 : ∀ i : Fin 128,
    levelEleven.lookup (2560 + i.val) ≤ levelElevenRoots.lookup (2560 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_2688 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 2688 128 =
      44517183916070136431509741727746 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_2688 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2688 128 =
      1117279147562033767532696 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_2688 : ∀ i : Fin 128,
    levelEleven.lookup (2688 + i.val) ≤ levelElevenRoots.lookup (2688 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_2816 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 2816 128 =
      36682100643777529784050168112115 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_2816 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2816 128 =
      1040454623811316115934410 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_2816 : ∀ i : Fin 128,
    levelEleven.lookup (2816 + i.val) ≤ levelElevenRoots.lookup (2816 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_2944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 2944 128 =
      22753295560705194824671290123003 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_2944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2944 128 =
      734057909067407593626541 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_2944 : ∀ i : Fin 128,
    levelEleven.lookup (2944 + i.val) ≤ levelElevenRoots.lookup (2944 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_5 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 2560 512 =
      159409965361371876340967094757012 := by
  have h0 := levelEleven_energy_2560
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 2560 256 =
      99974569156889151732245636521894 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 2560 128 128
      55457385240819015300735894794148 44517183916070136431509741727746 h0 levelEleven_energy_2688
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 2560 384 =
      136656669800666681516295804634009 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 2560 256 128
      99974569156889151732245636521894 36682100643777529784050168112115 h1 levelEleven_energy_2816
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 2560 512 =
      159409965361371876340967094757012 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 2560 384 128
      136656669800666681516295804634009 22753295560705194824671290123003 h2 levelEleven_energy_2944
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_5 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2560 512 =
      4183422871810251628093804 := by
  have h0 := levelEleven_fractional_2560
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2560 256 =
      2408910338931527918532853 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2560 128 128
      1291631191369494151000157 1117279147562033767532696 h0 levelEleven_fractional_2688
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2560 384 =
      3449364962742844034467263 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2560 256 128
      2408910338931527918532853 1040454623811316115934410 h1 levelEleven_fractional_2816
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2560 512 =
      4183422871810251628093804 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 2560 384 128
      3449364962742844034467263 734057909067407593626541 h2 levelEleven_fractional_2944
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_5 : ∀ i : Fin 512,
    levelEleven.lookup (2560 + i.val) ≤ levelElevenRoots.lookup (2560 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_2560
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 2560 128 128
    h0 levelEleven_squares_2688
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 2560 256 128
    h1 levelEleven_squares_2816
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 2560 384 128
    h2 levelEleven_squares_2944
  exact h3

end WordCertDensity.Certificates
