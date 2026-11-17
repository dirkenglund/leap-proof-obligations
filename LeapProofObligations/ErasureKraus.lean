import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Wilde Ex 4.7.9: the erasure channel has a Kraus form (is a channel). -/
theorem erasure_kraus {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∃ K : Option n → Matrix (Option n) n ℂ,
      (∑ i, (K i)ᴴ * K i = 1) ∧ ∀ X, erasure ε X = kraus K X := by
  sorry

end Leap
