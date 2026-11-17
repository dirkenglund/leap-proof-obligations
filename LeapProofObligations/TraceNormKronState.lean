import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Def 9.1.3: an untouched tensor factor leaves the trace distance alone. -/
theorem traceNorm_kron_state (A : Matrix m m ℂ) (ω : Matrix n n ℂ) (hω : ω.PosSemidef)
    (htr : ω.trace = 1) :
    traceNorm (Matrix.kroneckerMap (· * ·) A ω) = traceNorm A := by
  sorry

end Leap
