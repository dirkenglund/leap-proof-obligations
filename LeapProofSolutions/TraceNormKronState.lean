import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Def 9.1.3: an untouched tensor factor leaves the trace distance alone. -/
theorem traceNorm_kron_state (A : Matrix m m ℂ) (ω : Matrix n n ℂ) (hω : ω.PosSemidef)
    (htr : ω.trace = 1) :
    traceNorm (Matrix.kroneckerMap (· * ·) A ω) = traceNorm A := by
  let B : Matrix m m ℂ := cfc Real.sqrt (Aᴴ * A)
  have hB : B.PosSemidef ∧ B * B = Aᴴ * A := by
    let _ := @Matrix.instPartialOrder ℂ m _
    have := @Matrix.instStarOrderedRing ℂ m _ _
    have := @Matrix.instNonnegSpectrumClass ℂ m _ _
    have h0 : 0 ≤ Aᴴ * A :=
      Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self A)
    have h_eq : CFC.sqrt (Aᴴ * A) = B :=
      (CFC.sqrt_eq_real_sqrt (Aᴴ * A) h0).trans
        (cfcₙ_eq_cfc : cfcₙ Real.sqrt (Aᴴ * A) = cfc Real.sqrt (Aᴴ * A))
    have hB0 : 0 ≤ B := by
      rw [← h_eq]
      exact CFC.sqrt_nonneg (Aᴴ * A)
    have hmul : B * B = Aᴴ * A := by
      rw [← h_eq]
      exact CFC.sqrt_mul_sqrt_self (Aᴴ * A) h0
    exact ⟨Matrix.nonneg_iff_posSemidef.mp hB0, hmul⟩
  let Q : Matrix (m × n) (m × n) ℂ := Matrix.kroneckerMap (· * ·) B ω
  let X : Matrix (m × n) (m × n) ℂ := Matrix.kroneckerMap (· * ·) A ω
  have hQ_psd : Q.PosSemidef := Matrix.PosSemidef.kronecker hB.1 hω
  have hQ_sq : Q * Q = Xᴴ * X := by
    dsimp only [Q, X]
    calc
      Matrix.kroneckerMap (· * ·) B ω * Matrix.kroneckerMap (· * ·) B ω
          = Matrix.kroneckerMap (· * ·) (B * B) (ω * ω) :=
        (Matrix.mul_kronecker_mul B B ω ω).symm
      _ = Matrix.kroneckerMap (· * ·) (Aᴴ * A) (ωᴴ * ω) := by
        rw [hB.2, hω.isHermitian.eq]
      _ = Matrix.kroneckerMap (· * ·) Aᴴ ωᴴ * Matrix.kroneckerMap (· * ·) A ω :=
        Matrix.mul_kronecker_mul Aᴴ A ωᴴ ω
      _ = (Matrix.kroneckerMap (· * ·) A ω)ᴴ * Matrix.kroneckerMap (· * ·) A ω := by
        rw [Matrix.conjTranspose_kronecker]
  have h_cfc : cfc Real.sqrt (Xᴴ * X) = Q := by
    let _ := @Matrix.instPartialOrder ℂ (m × n) _
    have := @Matrix.instStarOrderedRing ℂ (m × n) _ _
    have := @Matrix.instNonnegSpectrumClass ℂ (m × n) _ _
    have hX0 : 0 ≤ Xᴴ * X :=
      Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
    have hQ0 : 0 ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ_psd
    have h_eq : CFC.sqrt (Xᴴ * X) = cfc Real.sqrt (Xᴴ * X) :=
      (CFC.sqrt_eq_real_sqrt (Xᴴ * X) hX0).trans
        (cfcₙ_eq_cfc : cfcₙ Real.sqrt (Xᴴ * X) = cfc Real.sqrt (Xᴴ * X))
    exact h_eq.symm.trans (CFC.sqrt_unique hQ_sq hQ0)
  simp only [traceNorm]
  change (cfc Real.sqrt (Xᴴ * X)).trace.re = B.trace.re
  rw [h_cfc]
  dsimp only [Q]
  rw [Matrix.trace_kronecker, htr, mul_one]

end Leap
