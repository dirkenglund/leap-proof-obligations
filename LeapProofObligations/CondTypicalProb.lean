import LeapProofObligations.Definitions

open scoped BigOperators

namespace Leap

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Wilde Def 15.2.4 / Property 15.2.5: uniform conditional typicality. -/
theorem condTypical_prob (W : α → β → ℝ) (hW : ∀ a b, 0 ≤ W a b) (hW1 : ∀ a, ∑ b, W a b = 1)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ x : Fin k → α, 1 - ε ≤ condProb W x (condTypical W δ x) := by
  sorry

end Leap
