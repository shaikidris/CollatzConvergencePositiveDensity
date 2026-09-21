/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.SeedTwo

/-! # Initial fractional integer certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Complete initial integer enclosure tree. -/
def seedOne48 : Entries :=
  (.node (.node (.leaf 0) (.leaf 562949953421312)) (.leaf 281474976710656))

/-- Complete initial integer enclosure tree. -/
def seedOne48Roots : Entries :=
  (.node (.node (.leaf 0) (.leaf 23726567)) (.leaf 16777216))

/-- Complete initial integer enclosure tree. -/
def seedTwo48Roots : Entries :=
  (.node (.node (.node (.node (.leaf 0) (.leaf 29742826)) (.leaf 21031354)) (.node (.leaf 25364767) (.leaf 0))) (.node (.node (.leaf 17935599) (.leaf 12682384)) (.node (.leaf 0) (.leaf 8967800))))

/-- Every initial square enclosure is checked in the kernel. -/
theorem seedOne48_square_enclosures : ∀ i : Fin 3,
    seedOne48.lookup i.val ≤ seedOne48Roots.lookup i.val ^ 2 := by decide +kernel

/-- Complete fractional numerator comparison. -/
theorem seedOne48_fractional_comparison :
    1000000 * ((List.range 3).map
      (fun i => seedOne48.lookup i * seedOne48Roots.lookup i)).sum ≤
        1276143 * 3 * 2 ^ 72 := by decide +kernel

/-- Every initial square enclosure is checked in the kernel. -/
theorem seedTwo48_square_enclosures : ∀ i : Fin 9,
    seedTwo48.lookup i.val ≤ seedTwo48Roots.lookup i.val ^ 2 := by decide +kernel

/-- Complete fractional numerator comparison. -/
theorem seedTwo48_fractional_comparison :
    500000 * ((List.range 9).map
      (fun i => seedTwo48.lookup i * seedTwo48Roots.lookup i)).sum ≤
        711317 * 9 * 2 ^ 72 := by decide +kernel

end WordCertDensity.Certificates
