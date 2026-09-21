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
theorem levelEleven_energy_124416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 124416 128 =
      90384274457561774829099961009641 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_124416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124416 128 =
      1497553341662207551940247 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_124416 : ∀ i : Fin 128,
    levelEleven.lookup (124416 + i.val) ≤ levelElevenRoots.lookup (124416 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_124544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 124544 128 =
      93382939339383523592873222620349 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_124544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124544 128 =
      1710748870311526324214961 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_124544 : ∀ i : Fin 128,
    levelEleven.lookup (124544 + i.val) ≤ levelElevenRoots.lookup (124544 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_124672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 124672 128 =
      21186903805713989222239145984642 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_124672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124672 128 =
      707669615413152043170598 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_124672 : ∀ i : Fin 128,
    levelEleven.lookup (124672 + i.val) ≤ levelElevenRoots.lookup (124672 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_124800 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 124800 128 =
      122804866082596932037333212137112 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_124800 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124800 128 =
      2099050125727969629639114 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_124800 : ∀ i : Fin 128,
    levelEleven.lookup (124800 + i.val) ≤ levelElevenRoots.lookup (124800 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_243 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 124416 512 =
      327758983685256219681545541751744 := by
  have h0 := levelEleven_energy_124416
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 124416 256 =
      183767213796945298421973183629990 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 124416 128 128
      90384274457561774829099961009641 93382939339383523592873222620349 h0 levelEleven_energy_124544
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 124416 384 =
      204954117602659287644212329614632 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 124416 256 128
      183767213796945298421973183629990 21186903805713989222239145984642 h1 levelEleven_energy_124672
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 124416 512 =
      327758983685256219681545541751744 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 124416 384 128
      204954117602659287644212329614632 122804866082596932037333212137112 h2 levelEleven_energy_124800
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_243 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124416 512 =
      6015021953114855548964920 := by
  have h0 := levelEleven_fractional_124416
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124416 256 =
      3208302211973733876155208 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124416 128 128
      1497553341662207551940247 1710748870311526324214961 h0 levelEleven_fractional_124544
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124416 384 =
      3915971827386885919325806 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124416 256 128
      3208302211973733876155208 707669615413152043170598 h1 levelEleven_fractional_124672
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124416 512 =
      6015021953114855548964920 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124416 384 128
      3915971827386885919325806 2099050125727969629639114 h2 levelEleven_fractional_124800
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_243 : ∀ i : Fin 512,
    levelEleven.lookup (124416 + i.val) ≤ levelElevenRoots.lookup (124416 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_124416
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 124416 128 128
    h0 levelEleven_squares_124544
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 124416 256 128
    h1 levelEleven_squares_124672
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 124416 384 128
    h2 levelEleven_squares_124800
  exact h3

end WordCertDensity.Certificates
