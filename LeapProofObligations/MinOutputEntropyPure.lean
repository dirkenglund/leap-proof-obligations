import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Def 20.4.1 / Ex 20.4.2: minimum output entropy is attained on pure inputs. -/
theorem minOutputEntropy_pure {ι : Type*} [Fintype ι] (K : ι → Matrix n m ℂ)
    (hTP : ∑ i, (K i)ᴴ * K i = 1) (ρ : Matrix m m ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ v : m → ℂ, star v ⬝ᵥ v = 1 ∧
      vnEntropy (kraus K (Matrix.vecMulVec v (star v))) ≤ vnEntropy (kraus K ρ) := by
  sorry

end Leap
