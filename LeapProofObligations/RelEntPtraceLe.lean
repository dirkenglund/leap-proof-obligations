import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Thm 11.9.2: monotonicity of relative entropy under partial trace
(Lindblad–Uhlmann; needs Lieb concavity). -/
theorem relEnt_ptrace_le (ρ σ : Matrix (m × n) (m × n) ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEnt (ptraceRight ρ) (ptraceRight σ) ≤ relEnt ρ σ := by
  sorry

end Leap
