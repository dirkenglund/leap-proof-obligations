import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Golden–Thompson inequality (premise of Wilde Lemma 17.3.3). -/
theorem golden_thompson (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (cfc Real.exp (A + B)).trace.re ≤ (cfc Real.exp A * cfc Real.exp B).trace.re := by
  sorry

end Leap
