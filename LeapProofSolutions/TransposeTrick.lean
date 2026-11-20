import LeapProofObligations.Definitions

open TensorProduct

namespace Leap

/-- Wilde Ex 3.7.12 / 3.7.11: transpose trick on a genuine tensor product. -/
theorem transpose_trick (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    TensorProduct.map (Matrix.toEuclideanLin A) LinearMap.id (maxEnt d) =
      TensorProduct.map LinearMap.id (Matrix.toEuclideanLin A.transpose) (maxEnt d) := by
  have hb : ∀ k : Fin d,
      (EuclideanSpace.basisFun (Fin d) ℂ).toBasis k = EuclideanSpace.single k (1 : ℂ) := by
    intro k
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  have h_act : ∀ (M : Matrix (Fin d) (Fin d) ℂ) (i : Fin d),
      (Matrix.toEuclideanLin M) (EuclideanSpace.single i (1 : ℂ)) =
        ∑ j : Fin d, M j i • EuclideanSpace.single j (1 : ℂ) := by
    intro M i
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← hb i, Matrix.toLin_self]
    simp only [hb]
  simp only [maxEnt, map_sum, TensorProduct.map_tmul, LinearMap.id_apply, h_act,
    Matrix.transpose_apply, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    TensorProduct.smul_tmul]
  exact Finset.sum_comm

end Leap
