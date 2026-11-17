import LeapProofObligations.Definitions

namespace Leap

/-- Wielandt–Wintner: no two elements of a nontrivial normed ℂ-algebra satisfy `[a, b] = 1`
(so `[Q, P] = iħ` has no bounded representation). -/
theorem wielandt {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] (a b : A) :
    a * b - b * a ≠ 1 := by
  sorry

end Leap
