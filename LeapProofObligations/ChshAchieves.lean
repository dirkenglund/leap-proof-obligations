import LeapProofObligations.Definitions

open scoped Real

namespace Leap

/-- Wilde Ex 3.6.4: some projective qubit strategy on |Φ⁺⟩ wins CHSH with probability cos²(π/8). -/
theorem chsh_achieves : ∃ SA SB : ProjStrategy, chshWin SA SB = Real.cos (π / 8) ^ 2 := by
  sorry

end Leap
