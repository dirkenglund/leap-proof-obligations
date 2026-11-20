import LeapProofObligations.Definitions

open scoped Real

namespace Leap

/-- Wilde Ex 3.6.4: some projective qubit strategy on |Φ⁺⟩ wins CHSH with probability cos²(π/8). -/
theorem chsh_achieves : ∃ SA SB : ProjStrategy, chshWin SA SB = Real.cos (π / 8) ^ 2 := by
  let planarProj (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.of ![![((Real.cos φ ^ 2 : ℝ) : ℂ), ((Real.cos φ * Real.sin φ : ℝ) : ℂ)],
                ![((Real.cos φ * Real.sin φ : ℝ) : ℂ), ((Real.sin φ ^ 2 : ℝ) : ℂ)]]
  have h_herm : ∀ φ : ℝ, (planarProj φ).IsHermitian := by
    intro φ
    rw [Matrix.IsHermitian, ← Matrix.ext_iff]
    simp only [Fin.forall_fin_two, planarProj, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.star_def, Complex.conj_ofReal, and_self]
  have h_idem : ∀ φ : ℝ, planarProj φ * planarProj φ = planarProj φ := by
    intro φ
    have hcs : (Real.cos φ : ℂ) ^ 2 + (Real.sin φ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq φ
    rw [← Matrix.ext_iff]
    simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, planarProj,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.ofReal_mul, Complex.ofReal_pow]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linear_combination (Real.cos φ : ℂ) ^ 2 * hcs
    · linear_combination (Real.cos φ : ℂ) * (Real.sin φ : ℂ) * hcs
    · linear_combination (Real.cos φ : ℂ) * (Real.sin φ : ℂ) * hcs
    · linear_combination (Real.sin φ : ℂ) ^ 2 * hcs
  have h_complete : ∀ φ : ℝ, planarProj φ + planarProj (φ + π / 2) = 1 := by
    intro φ
    have hcs : (Real.cos φ : ℂ) ^ 2 + (Real.sin φ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq φ
    have h01 : ((0 : Fin 2) = 1) = False := by decide
    have h10 : ((1 : Fin 2) = 0) = False := by decide
    rw [← Matrix.ext_iff]
    simp only [Fin.forall_fin_two, Matrix.add_apply, Matrix.one_apply, planarProj,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
      h01, h10, ite_false, ite_true]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linear_combination hcs
    · ring
    · ring
    · linear_combination hcs
  have h_expect : ∀ α β : ℝ,
      (star phiPlus ⬝ᵥ
        (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (planarProj α) (planarProj β)).mulVec phiPlus).re =
        (1 / 2 : ℝ) * Real.cos (α - β) ^ 2 := by
    intro α β
    have h_inv_sq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have h01 : ((0 : Fin 2) = 1) = False := by decide
    have h10 : ((1 : Fin 2) = 0) = False := by decide
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Pi.star_apply, phiPlus, planarProj,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      h01, h10, ite_false, ite_true, mul_zero, zero_mul, add_zero, zero_add, map_zero,
      ← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
    rw [Real.cos_sub α β]
    linear_combination (Real.cos α * Real.cos β + Real.sin α * Real.sin β) ^ 2 * h_inv_sq
  let mkStrat (θ : Fin 2 → ℝ) : ProjStrategy :=
    { P := fun x a => if a = 0 then planarProj (θ x) else planarProj (θ x + π / 2)
      herm := fun x a => by by_cases ha : a = 0 <;> simp [ha, h_herm]
      idem := fun x a => by by_cases ha : a = 0 <;> simp [ha, h_idem]
      complete := fun x => by
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        simp [h10, h_complete] }
  refine ⟨mkStrat ![0, π / 4], mkStrat ![π / 8, -(π / 8)], ?_⟩
  simp only [chshWin, Fin.sum_univ_two]
  simp only [mkStrat, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hf00 : (0 : Fin 2) + 0 = 0 := rfl
  have hf01 : (0 : Fin 2) + 1 = 1 := rfl
  have hf10 : (1 : Fin 2) + 0 = 1 := rfl
  have hf11 : (1 : Fin 2) + 1 = 0 := rfl
  have hm00 : (0 : Fin 2) * 0 = 0 := rfl
  have hm01 : (0 : Fin 2) * 1 = 0 := rfl
  have hm10 : (1 : Fin 2) * 0 = 0 := rfl
  have hm11 : (1 : Fin 2) * 1 = 1 := rfl
  have hne01 : ((0 : Fin 2) = 1) = False := by decide
  have hne10 : ((1 : Fin 2) = 0) = False := by decide
  simp only [hf00, hf01, hf10, hf11, hm00, hm01, hm10, hm11, hne01, hne10,
    ite_true, ite_false, add_zero, zero_add, h_expect]
  have ha1 : (0 : ℝ) - π / 8 = -(π / 8) := by ring
  have ha2 : π / 2 - (π / 8 + π / 2) = -(π / 8) := by ring
  have ha3 : (0 : ℝ) - -(π / 8) = π / 8 := by ring
  have ha4 : π / 2 - (-(π / 8) + π / 2) = π / 8 := by ring
  have ha5 : π / 4 - π / 8 = π / 8 := by ring
  have ha6 : π / 4 + π / 2 - (π / 8 + π / 2) = π / 8 := by ring
  have ha7 : π / 4 - (-(π / 8) + π / 2) = -(π / 8) := by ring
  have ha8 : π / 4 + π / 2 - -(π / 8) = π - π / 8 := by ring
  rw [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
  simp only [Real.cos_neg, Real.cos_pi_sub]
  ring

end Leap
