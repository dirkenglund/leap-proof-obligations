import LeapProofObligations.Definitions

open scoped MatrixOrder

namespace Leap

/-- Hermitian 2×2 matrices are not a lattice under the Löwner order. -/
theorem loewner_not_lattice :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A.IsHermitian ∧ B.IsHermitian ∧
      ¬ ∃ S : Matrix (Fin 2) (Fin 2) ℂ,
        IsLUB {M | M.IsHermitian ∧ (M = A ∨ M = B)} S ∧ S.IsHermitian := by
  letI : PartialOrder ℂ := Complex.partialOrder
  letI : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(1 : ℂ), -1]
  let B : Matrix (Fin 2) (Fin 2) ℂ := 0
  have hA : A.IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i; fin_cases i <;> simp [IsSelfAdjoint]
  have hB : B.IsHermitian := Matrix.isHermitian_zero
  refine ⟨A, B, hA, hB, ?_⟩
  rintro ⟨S, hS_lub, _⟩
  have hAS : A ≤ S := hS_lub.1 ⟨hA, Or.inl rfl⟩
  have h0S : 0 ≤ S := hS_lub.1 ⟨hB, Or.inr rfl⟩
  have hS_le : ∀ U : Matrix (Fin 2) (Fin 2) ℂ, A ≤ U → 0 ≤ U → S ≤ U := by
    intro U hAU h0U
    apply hS_lub.2
    rintro M ⟨_, rfl | rfl⟩
    · exact hAU
    · exact h0U
  let U0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(1 : ℂ), 0]
  have h0U0 : 0 ≤ U0 := by
    rw [Matrix.nonneg_iff_posSemidef, Matrix.posSemidef_diagonal_iff]
    intro i; fin_cases i <;> rw [Complex.nonneg_iff] <;> simp
  have hAU0 : A ≤ U0 := by
    rw [Matrix.le_iff]
    have hdiff : U0 - A = Matrix.diagonal ![(0 : ℂ), 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [U0, A]
    rw [hdiff, Matrix.posSemidef_diagonal_iff]
    intro i; fin_cases i <;> rw [Complex.nonneg_iff] <;> simp
  have hSU0 : S ≤ U0 := hS_le U0 hAU0 h0U0
  have h1 : (S - A).PosSemidef := Matrix.le_iff.mp hAS
  have h2 : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp h0S
  have h3 : (U0 - S).PosSemidef := Matrix.le_iff.mp hSU0
  have h1_0 : 0 ≤ (S - A) 0 0 := h1.diag_nonneg
  have h3_0 : 0 ≤ (U0 - S) 0 0 := h3.diag_nonneg
  have h2_1 : 0 ≤ S 1 1 := h2.diag_nonneg
  have h3_1 : 0 ≤ (U0 - S) 1 1 := h3.diag_nonneg
  rw [Complex.nonneg_iff] at h1_0 h3_0 h2_1 h3_1
  have hd0 : (U0 - S) 0 0 = 0 := by
    apply Complex.ext
    · simp [U0, A] at h1_0 h3_0 ⊢; linarith
    · simp [U0, A] at h1_0 h3_0 ⊢; linarith
  have hd1 : (U0 - S) 1 1 = 0 := by
    apply Complex.ext
    · simp [U0] at h2_1 h3_1 ⊢; linarith
    · simp [U0] at h2_1 h3_1 ⊢; linarith
  have htr : (U0 - S).trace = 0 := by
    rw [Matrix.trace_fin_two, hd0, hd1, add_zero]
  have hU0_eq_S : U0 = S := sub_eq_zero.mp (h3.trace_eq_zero_iff.mp htr)
  let C2 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![3, 2], ![0, 0]]
  let U1 : Matrix (Fin 2) (Fin 2) ℂ := C2.conjTranspose * C2
  let C3 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![2, 2], ![2, 1]]
  have h0U1 : 0 ≤ U1 :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self C2)
  have hAU1 : A ≤ U1 := by
    rw [Matrix.le_iff]
    have hU1A : U1 - A = C3.conjTranspose * C3 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [U1, C2, C3, A, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat] <;> norm_num
    rw [hU1A]
    exact Matrix.posSemidef_conjTranspose_mul_self C3
  have hU0U1 : U0 ≤ U1 := hU0_eq_S ▸ hS_le U1 hAU1 h0U1
  have h4 : (U1 - U0).PosSemidef := Matrix.le_iff.mp hU0U1
  let v : Fin 2 → ℂ := ![-2, 3]
  have hv : 0 ≤ dotProduct (star v) ((U1 - U0).mulVec v) := h4.dotProduct_mulVec_nonneg v
  have hv_val : dotProduct (star v) ((U1 - U0).mulVec v) = (-4 : ℂ) := by
    simp [v, U1, U0, C2, dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
    norm_num
  rw [hv_val, Complex.nonneg_iff] at hv
  norm_num at hv

end Leap
