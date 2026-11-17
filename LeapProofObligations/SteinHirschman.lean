import LeapProofObligations.Definitions

open Complex Complex.HadamardThreeLines MeasureTheory
open scoped Real

namespace Leap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

/-- Wilde Thm 12.2.3: operator Stein–Hirschman interpolation, general exponents. -/
theorem stein_hirschman (G : ℂ → H →L[ℂ] K) (hd : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hb : BddAbove ((norm ∘ G) '' verticalClosedStrip 0 1)) {θ p₀ p₁ pθ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hpθ : 1 / pθ = (1 - θ) / p₀ + θ / p₁) (hGθ : schattenNorm pθ (G θ) ≠ 0)
    (hα : Integrable fun t : ℝ =>
      hirschmanAlpha θ t * Real.log (schattenNorm p₀ (G (I * t)) ^ (1 - θ)))
    (hβ : Integrable fun t : ℝ =>
      hirschmanBeta θ t * Real.log (schattenNorm p₁ (G (1 + I * t)) ^ θ)) :
    Real.log (schattenNorm pθ (G θ)) ≤
      ∫ t : ℝ, (hirschmanAlpha θ t * Real.log (schattenNorm p₀ (G (I * t)) ^ (1 - θ))
        + hirschmanBeta θ t * Real.log (schattenNorm p₁ (G (1 + I * t)) ^ θ)) := by
  sorry

end Leap
