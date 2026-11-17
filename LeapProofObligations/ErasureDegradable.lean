import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Wilde Ex 13.5.2: for `ε ≤ 1/2` the erasure channel is degradable:
its complement `E_{1-ε}` is `E_ε` followed by a re-erasure with `η = (1-2ε)/(1-ε)`. -/
theorem erasure_degradable {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) :
    let η := (1 - 2 * ε) / (1 - ε)
    0 ≤ η ∧ η ≤ 1 ∧ ∀ X : Matrix n n ℂ, reErase η (erasure ε X) = erasure (1 - ε) X := by
  sorry

end Leap
