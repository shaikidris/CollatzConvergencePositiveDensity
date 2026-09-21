/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.DirectEvaluator

/-! # Exact binary-precision starting tree for the direct certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- The complete depth-two vector rounded upward at scale two to the forty-eighth power. -/
def seedTwo48 : Entries :=
  .node
    (.node
      (.node (.node (.leaf 0) (.leaf 884635641090634)) (.leaf 442317820545317))
      (.node (.leaf 643371375338643) (.leaf 0)))
    (.node
      (.node (.leaf 321685687669322) (.leaf 160842843834661))
      (.node (.leaf 0) (.leaf 80421421917331)))

/-- Every stored starting value passes the exact natural maximum check. -/
theorem seedTwo48_cap : seedTwo48.allLE 884635641090634 = true := by decide +kernel

end WordCertDensity.Certificates
