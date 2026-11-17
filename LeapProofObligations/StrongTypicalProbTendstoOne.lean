import LeapProofObligations.Definitions

open scoped BigOperators
open Filter Topology

namespace Leap

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Wilde Def 15.2.3: strong typicality concentrates. -/
theorem strongTypical_prob_tendsto_one (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => iidProb p (strongTypical p δ k)) atTop (𝓝 1) := by
  sorry

end Leap
