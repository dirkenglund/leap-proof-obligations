import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n]

/-- Wilde Def 9.5.1 / Thm 9.5.1: `F_e = ∑ᵢ |Tr(Kᵢ ρ)|²`, so it does not depend on
the purification. -/
theorem entFid_eq {ι : Type*} [Fintype ι] (K : ι → Matrix n n ℂ) (ψ : n × r → ℂ) :
    entFid K ψ = ∑ i, ‖(K i * reduced ψ).trace‖ ^ 2 := by
  sorry

end Leap
