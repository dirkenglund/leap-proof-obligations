import LeapProofObligations.Definitions

open TensorProduct

namespace Leap

/-- Wilde Ex 3.7.12 / 3.7.11: transpose trick on a genuine tensor product. -/
theorem transpose_trick (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    TensorProduct.map (Matrix.toEuclideanLin A) LinearMap.id (maxEnt d) =
      TensorProduct.map LinearMap.id (Matrix.toEuclideanLin A.transpose) (maxEnt d) := by
  sorry

end Leap
