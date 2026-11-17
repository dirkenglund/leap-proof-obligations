import LeapProofObligations.Definitions

open scoped BigOperators

namespace Leap

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Wilde Property 15.2.7: size of the conditionally typical set. -/
theorem condTypical_card_le (W : α → β → ℝ) (hW : ∀ a b, 0 ≤ W a b) (hW1 : ∀ a, ∑ b, W a b = 1) :
    ∃ c : ℝ, ∀ δ > 0, ∀ (k : ℕ) (x : Fin k → α),
      ((condTypical W δ x).card : ℝ) ≤
        Real.exp (k * (∑ a, (count x a : ℝ) / k * entropy (W a) + c * δ)) := by
  sorry

end Leap
