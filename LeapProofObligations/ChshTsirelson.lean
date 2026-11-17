import LeapProofObligations.Definitions

open scoped Real

namespace Leap

/-- Wilde Ex 3.6.4, Tsirelson (qubit, |Φ⁺⟩ form): no projective strategy does better. -/
theorem chsh_tsirelson (SA SB : ProjStrategy) : chshWin SA SB ≤ Real.cos (π / 8) ^ 2 := by
  sorry

end Leap
