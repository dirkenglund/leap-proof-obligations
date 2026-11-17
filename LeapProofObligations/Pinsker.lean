import LeapProofObligations.Definitions

open scoped BigOperators

namespace Leap

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Wilde Thm / Lemma 10.8.1: classical Pinsker inequality, in nats. -/
theorem pinsker (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) (hac : ∀ a, q a = 0 → p a = 0) :
    (∑ a, |p a - q a|) ^ 2 / 2 ≤ ∑ a, p a * Real.log (p a / q a) := by
  sorry

end Leap
