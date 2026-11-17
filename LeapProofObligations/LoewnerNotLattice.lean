import LeapProofObligations.Definitions

open scoped MatrixOrder

namespace Leap

/-- Hermitian 2×2 matrices are not a lattice under the Löwner order. -/
theorem loewner_not_lattice :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A.IsHermitian ∧ B.IsHermitian ∧
      ¬ ∃ S : Matrix (Fin 2) (Fin 2) ℂ,
        IsLUB {M | M.IsHermitian ∧ (M = A ∨ M = B)} S ∧ S.IsHermitian := by
  sorry

end Leap
