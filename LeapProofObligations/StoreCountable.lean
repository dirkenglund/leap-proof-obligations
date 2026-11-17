import LeapProofObligations.Definitions

namespace Leap

/-- The set of stores on a finite variable set with integer values is countable. -/
theorem store_countable (Var : Type*) [Finite Var] : Countable (Var → ℤ) := by
  sorry

end Leap
