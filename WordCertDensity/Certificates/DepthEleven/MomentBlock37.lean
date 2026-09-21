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
theorem levelEleven_energy_18944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 18944 128 =
      55618236618730376324832283906215 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_18944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18944 128 =
      1242788798685653483459848 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_18944 : ∀ i : Fin 128,
    levelEleven.lookup (18944 + i.val) ≤ levelElevenRoots.lookup (18944 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_19072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 19072 128 =
      35418547730673572934009019818972 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_19072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19072 128 =
      1026466817954609194810599 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_19072 : ∀ i : Fin 128,
    levelEleven.lookup (19072 + i.val) ≤ levelElevenRoots.lookup (19072 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_19200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 19200 128 =
      50029726231845671339462109227409 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_19200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19200 128 =
      1172159856292462823146876 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_19200 : ∀ i : Fin 128,
    levelEleven.lookup (19200 + i.val) ≤ levelElevenRoots.lookup (19200 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_19328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 19328 128 =
      74341528336247392269339933604016 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_19328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 19328 128 =
      1440560833644040463996986 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_19328 : ∀ i : Fin 128,
    levelEleven.lookup (19328 + i.val) ≤ levelElevenRoots.lookup (19328 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_37 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 18944 512 =
      215408038917497012867643346556612 := by
  have h0 := levelEleven_energy_18944
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 18944 256 =
      91036784349403949258841303725187 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 18944 128 128
      55618236618730376324832283906215 35418547730673572934009019818972 h0 levelEleven_energy_19072
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 18944 384 =
      141066510581249620598303412952596 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 18944 256 128
      91036784349403949258841303725187 50029726231845671339462109227409 h1 levelEleven_energy_19200
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 18944 512 =
      215408038917497012867643346556612 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 18944 384 128
      141066510581249620598303412952596 74341528336247392269339933604016 h2 levelEleven_energy_19328
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_37 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18944 512 =
      4881976306576765965414309 := by
  have h0 := levelEleven_fractional_18944
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18944 256 =
      2269255616640262678270447 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18944 128 128
      1242788798685653483459848 1026466817954609194810599 h0 levelEleven_fractional_19072
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18944 384 =
      3441415472932725501417323 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18944 256 128
      2269255616640262678270447 1172159856292462823146876 h1 levelEleven_fractional_19200
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18944 512 =
      4881976306576765965414309 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 18944 384 128
      3441415472932725501417323 1440560833644040463996986 h2 levelEleven_fractional_19328
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_37 : ∀ i : Fin 512,
    levelEleven.lookup (18944 + i.val) ≤ levelElevenRoots.lookup (18944 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_18944
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 18944 128 128
    h0 levelEleven_squares_19072
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 18944 256 128
    h1 levelEleven_squares_19200
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 18944 384 128
    h2 levelEleven_squares_19328
  exact h3

end WordCertDensity.Certificates
