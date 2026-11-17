import LeapProofObligations.Definitions

open scoped Real

namespace Leap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- Schatten Hölder / duality, `|tr(T X)| ≤ ‖T‖_p ‖X‖_q` for conjugate `p, q`. -/
theorem schatten_holder (T : H →L[ℂ] H) (X : H →L[ℂ] H) {p q : ℝ} (hp : 1 < p)
    (hpq : 1 / p + 1 / q = 1) :
    ‖LinearMap.trace ℂ H (T ∘L X : H →L[ℂ] H)‖ ≤ schattenNorm p T * schattenNorm q X := by
  sorry

end Leap
