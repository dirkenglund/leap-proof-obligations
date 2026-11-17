import LeapProofObligations.Definitions

open scoped MatrixOrder

namespace Leap

/-- An increasing chain of effects `0 ≤ fₖ ≤ 1` has a Löwner supremum. -/
theorem loewner_chain_sup {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℕ → Matrix n n ℂ) (hf : Monotone f) (h0 : ∀ k, 0 ≤ f k) (h1 : ∀ k, f k ≤ 1) :
    ∃ S, IsLUB (Set.range f) S ∧ 0 ≤ S ∧ S ≤ 1 := by
  sorry

end Leap
