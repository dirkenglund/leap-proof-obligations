import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Def 12.3.1, book form for singular σ: Petz recovers σ exactly and is
trace-preserving on the support of `N(σ)` (`rpowS _ 0` is the support projector). -/
theorem petz_recovers {ι : Type*} [Fintype ι] (K : ι → Matrix n m ℂ)
    (hTP : ∑ i, (K i)ᴴ * K i = 1) (σ : Matrix m m ℂ) (hσ : σ.PosSemidef) :
    petz K σ (kraus K σ) = σ ∧
      ∀ X : Matrix n n ℂ, (petz K σ X).trace = (rpowS (kraus K σ) 0 * X).trace := by
  sorry

end Leap
