import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Def 12.3.2: every rotated Petz map recovers σ, is trace-preserving on the
support, and is completely positive (has a Kraus form). -/
theorem rotatedPetz_props {ι : Type*} [Fintype ι] (K : ι → Matrix n m ℂ)
    (hTP : ∑ i, (K i)ᴴ * K i = 1) (σ : Matrix m m ℂ) (hσ : σ.PosSemidef) (t : ℝ) :
    rotatedPetz K σ t (kraus K σ) = σ ∧
      (∀ X : Matrix n n ℂ, (rotatedPetz K σ t X).trace = (rpowS (kraus K σ) 0 * X).trace) ∧
      ∃ L : ι → Matrix m n ℂ, ∀ X, rotatedPetz K σ t X = kraus L X := by
  sorry

end Leap
