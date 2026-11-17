import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Wilde Ex 11.9.2 / Thm 11.6.1: Holevo bound for one finite-outcome POVM. -/
theorem holevo_bound {ι o : Type*} [Fintype ι] [Fintype o]
    (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x) (hps : ∑ x, p x = 1)
    (ρ : ι → Matrix n n ℂ) (hρ : ∀ x, (ρ x).PosSemidef) (htr : ∀ x, (ρ x).trace = 1)
    (Λ : o → Matrix n n ℂ) (hΛ : ∀ y, (Λ y).PosSemidef) (hΛ1 : ∑ y, Λ y = 1) :
    let P : ι → o → ℝ := fun x y => p x * (Λ y * ρ x).trace.re
    let q : o → ℝ := fun y => ∑ x, P x y
    (∑ x, ∑ y, P x y * Real.log (P x y / (p x * q y))) ≤
      vnEntropy (∑ x, (p x : ℂ) • ρ x) - ∑ x, p x * vnEntropy (ρ x) := by
  sorry

end Leap
