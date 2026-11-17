import LeapProofObligations.Definitions

open Complex Complex.HadamardThreeLines MeasureTheory
open scoped Real

namespace Leap

/-- Wilde Thm 12.2.2: Hirschman's strip inequality, both kernels. -/
theorem hirschman_strip (f : ℂ → ℂ) (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hb : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hfθ : f θ ≠ 0)
    (hα : Integrable fun t : ℝ => hirschmanAlpha θ t * Real.log (‖f (I * t)‖ ^ (1 - θ)))
    (hβ : Integrable fun t : ℝ => hirschmanBeta θ t * Real.log (‖f (1 + I * t)‖ ^ θ)) :
    Real.log ‖f θ‖ ≤ ∫ t : ℝ, (hirschmanAlpha θ t * Real.log (‖f (I * t)‖ ^ (1 - θ))
      + hirschmanBeta θ t * Real.log (‖f (1 + I * t)‖ ^ θ)) := by
  sorry

end Leap
