import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Ex 4.4.1 / Thm 4.4.1: Choi's theorem and Kraus representation. -/
theorem choi_theorem (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) :
    (IsCP Φ ↔ (choi Φ).PosSemidef) ∧
      (IsCP Φ ↔ ∃ K : m × n → Matrix n m ℂ, ∀ X, Φ X = kraus K X) := by
  sorry

end Leap
