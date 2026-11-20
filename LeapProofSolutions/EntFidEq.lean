import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n]

/-- Wilde Def 9.5.1 / Thm 9.5.1: `F_e = ∑ᵢ |Tr(Kᵢ ρ)|²`, so it does not depend on
the purification. -/
theorem entFid_eq {ι : Type*} [Fintype ι] (K : ι → Matrix n n ℂ) (ψ : n × r → ℂ) :
    entFid K ψ = ∑ i, ‖(K i * reduced ψ).trace‖ ^ 2 := by
  dsimp only [entFid]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine congrArg (fun z : ℂ => ‖z‖ ^ 2) ?_
  rw [Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, reduced, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, mul_assoc]

end Leap
