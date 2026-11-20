import LeapProofObligations.Definitions

open scoped Real

namespace Leap

/-- Wilde Ex 3.6.4, Tsirelson (qubit, |Φ⁺⟩ form): no projective strategy does better. -/
theorem chsh_tsirelson (SA SB : ProjStrategy) : chshWin SA SB ≤ Real.cos (π / 8) ^ 2 := by
  let projObs : ProjStrategy → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
    fun S x => S.P x 0 - S.P x 1
  let chshTerm : Fin 2 → Fin 2 → ℝ :=
    fun i j =>
      (projObs SA 0 i j * projObs SB 0 i j +
       projObs SA 0 i j * projObs SB 1 i j +
       projObs SA 1 i j * projObs SB 0 i j -
       projObs SA 1 i j * projObs SB 1 i j).re
  have h01 : ((0 : Fin 2) = 1) = False := by decide
  have h10 : ((1 : Fin 2) = 0) = False := by decide
  have h_inv_sq : star ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    have hs2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hs2
      norm_num at hs2
    have hstar : star ((↑(Real.sqrt 2) : ℂ)⁻¹) = ((↑(Real.sqrt 2) : ℂ)⁻¹) := by
      rw [star_inv₀]
      exact congrArg Inv.inv (Complex.conj_ofReal _)
    rw [hstar]
    field_simp [hs_ne]
    linear_combination -hs2
  have h_bell : ∀ M N : Matrix (Fin 2) (Fin 2) ℂ,
      (star phiPlus ⬝ᵥ (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M N).mulVec phiPlus).re =
        1 / 2 * ((M 0 0 * N 0 0).re + (M 0 1 * N 0 1).re +
                 (M 1 0 * N 1 0).re + (M 1 1 * N 1 1).re) := by
    intro M N
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, phiPlus, Pi.star_apply, ↓reduceIte, h01, h10,
      star_zero, zero_mul, mul_zero, add_zero, zero_add]
    have hring :
        star ((↑(Real.sqrt 2) : ℂ)⁻¹) *
          (M 0 0 * N 0 0 * (↑(Real.sqrt 2) : ℂ)⁻¹ + M 0 1 * N 0 1 * (↑(Real.sqrt 2) : ℂ)⁻¹) +
        star ((↑(Real.sqrt 2) : ℂ)⁻¹) *
          (M 1 0 * N 1 0 * (↑(Real.sqrt 2) : ℂ)⁻¹ + M 1 1 * N 1 1 * (↑(Real.sqrt 2) : ℂ)⁻¹) =
        (star ((↑(Real.sqrt 2) : ℂ)⁻¹) * ((↑(Real.sqrt 2) : ℂ)⁻¹)) *
          (M 0 0 * N 0 0 + M 0 1 * N 0 1 + M 1 0 * N 1 0 + M 1 1 * N 1 1) := by
      ring
    rw [hring, h_inv_sq]
    have hhalf_re : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    have hhalf_im : ((1 / 2 : ℂ)).im = 0 := by norm_num
    simp only [Complex.mul_re, Complex.add_re, hhalf_re, hhalf_im, zero_mul, sub_zero]
  have h_chsh : chshWin SA SB =
      1 / 2 + 1 / 16 * (chshTerm 0 0 + chshTerm 0 1 + chshTerm 1 0 + chshTerm 1 1) := by
    have hP0 : ∀ (S : ProjStrategy) (x i j : Fin 2),
        S.P x 0 i j = (1 / 2 : ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j + projObs S x i j) := by
      intro S x i j
      have hc := congr_fun (congr_fun (S.complete x) i) j
      simp only [Matrix.add_apply] at hc
      dsimp only [projObs]
      rw [Matrix.sub_apply, ← hc]
      ring
    have hP1 : ∀ (S : ProjStrategy) (x i j : Fin 2),
        S.P x 1 i j = (1 / 2 : ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j - projObs S x i j) := by
      intro S x i j
      have hc := congr_fun (congr_fun (S.complete x) i) j
      simp only [Matrix.add_apply] at hc
      dsimp only [projObs]
      rw [Matrix.sub_apply, ← hc]
      ring
    have ha01 : (0 : Fin 2) + 1 = 1 := by decide
    have ha11 : (1 : Fin 2) + 1 = 0 := by decide
    have hm00 : (0 : Fin 2) * 0 = 0 := by decide
    have hm01 : (0 : Fin 2) * 1 = 0 := by decide
    have hm10 : (1 : Fin 2) * 0 = 0 := by decide
    have hm11 : (1 : Fin 2) * 1 = 1 := by decide
    have hhalf_re : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    have hhalf_im : ((1 / 2 : ℂ)).im = 0 := by norm_num
    simp only [chshWin, Fin.sum_univ_two, ha01, ha11, hm00, hm01, hm10, hm11,
      h01, h10, ↓reduceIte, add_zero, zero_add, h_bell]
    dsimp only [chshTerm]
    simp only [hP0, hP1, Matrix.one_apply, ↓reduceIte, h01, h10,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im, hhalf_re, hhalf_im]
    ring
  have h_norm : ∀ (S : ProjStrategy) (x : Fin 2),
      Complex.normSq (projObs S x 0 0) + Complex.normSq (projObs S x 0 1) +
      Complex.normSq (projObs S x 1 0) + Complex.normSq (projObs S x 1 1) = 2 := by
    intro S x
    let P0 := S.P x 0
    let M := projObs S x
    have hM_herm : M.IsHermitian := (S.herm x 0).sub (S.herm x 1)
    have h_entry : ∀ i j : Fin 2, M j i = star (M i j) := by
      intro i j
      have h := congr_fun (congr_fun hM_herm j) i
      simpa [Matrix.conjTranspose_apply] using h.symm
    have h2P : (P0 + P0) * (P0 + P0) = (P0 + P0) + (P0 + P0) := by
      rw [mul_add, add_mul, S.idem x 0]
    have hM_sq : M * M = 1 := by
      have hM_eq : M = (P0 + P0) - 1 := by
        dsimp only [M, projObs, P0]
        rw [eq_sub_of_add_eq' (S.complete x)]
        abel
      rw [hM_eq, sub_mul, mul_sub, mul_sub, h2P, mul_one, one_mul, one_mul]
      abel
    have h_mul_star : ∀ z : ℂ, (z * star z).re = Complex.normSq z := by
      intro z
      simp only [Complex.mul_re, Complex.normSq_apply, Complex.star_def,
        Complex.conj_re, Complex.conj_im]
      ring
    have hd0 : ((M * M) 0 0).re = ((1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re :=
      congrArg Complex.re (congr_fun (congr_fun hM_sq 0) 0)
    have hd1 : ((M * M) 1 1).re = ((1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re :=
      congrArg Complex.re (congr_fun (congr_fun hM_sq 1) 1)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, ↓reduceIte,
      Complex.add_re, Complex.one_re] at hd0 hd1
    have he00 : (M 0 0 * M 0 0).re = Complex.normSq (M 0 0) := by
      rw [congrArg (M 0 0 * ·) (h_entry 0 0), h_mul_star]
    have he01 : (M 0 1 * M 1 0).re = Complex.normSq (M 0 1) := by
      rw [h_entry 0 1, h_mul_star]
    have he10 : (M 1 0 * M 0 1).re = Complex.normSq (M 1 0) := by
      rw [h_entry 1 0, h_mul_star]
    have he11 : (M 1 1 * M 1 1).re = Complex.normSq (M 1 1) := by
      rw [congrArg (M 1 1 * ·) (h_entry 1 1), h_mul_star]
    rw [he00, he01] at hd0
    rw [he10, he11] at hd1
    dsimp only [M] at hd0 hd1
    linarith
  have h_quad : ∀ a0 a1 b0 b1 : ℂ,
      Real.sqrt 2 * (a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1).re ≤
        Complex.normSq a0 + Complex.normSq a1 + Complex.normSq b0 + Complex.normSq b1 := by
    intro a0 a1 b0 b1
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.normSq_apply]
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs1 : 0 ≤ (Real.sqrt 2 * a0.re - (b0.re + b1.re)) ^ 2 := sq_nonneg _
    have hs2 : 0 ≤ (Real.sqrt 2 * a1.re - (b0.re - b1.re)) ^ 2 := sq_nonneg _
    have hs3 : 0 ≤ (Real.sqrt 2 * a0.im + (b0.im + b1.im)) ^ 2 := sq_nonneg _
    have hs4 : 0 ≤ (Real.sqrt 2 * a1.im + (b0.im - b1.im)) ^ 2 := sq_nonneg _
    have hid :
        (Real.sqrt 2 * a0.re - (b0.re + b1.re)) ^ 2 +
        (Real.sqrt 2 * a1.re - (b0.re - b1.re)) ^ 2 +
        (Real.sqrt 2 * a0.im + (b0.im + b1.im)) ^ 2 +
        (Real.sqrt 2 * a1.im + (b0.im - b1.im)) ^ 2 =
        Real.sqrt 2 ^ 2 * (a0.re * a0.re + a0.im * a0.im + a1.re * a1.re + a1.im * a1.im) +
        2 * (b0.re * b0.re + b0.im * b0.im + b1.re * b1.re + b1.im * b1.im) -
        2 * Real.sqrt 2 * ((a0.re * b0.re - a0.im * b0.im) + (a0.re * b1.re - a0.im * b1.im) +
          (a1.re * b0.re - a1.im * b0.im) - (a1.re * b1.re - a1.im * b1.im)) := by
      ring
    rw [hsq2] at hid
    linarith
  have hq00 := h_quad (projObs SA 0 0 0) (projObs SA 1 0 0) (projObs SB 0 0 0) (projObs SB 1 0 0)
  have hq01 := h_quad (projObs SA 0 0 1) (projObs SA 1 0 1) (projObs SB 0 0 1) (projObs SB 1 0 1)
  have hq10 := h_quad (projObs SA 0 1 0) (projObs SA 1 1 0) (projObs SB 0 1 0) (projObs SB 1 1 0)
  have hq11 := h_quad (projObs SA 0 1 1) (projObs SA 1 1 1) (projObs SB 0 1 1) (projObs SB 1 1 1)
  have hnA0 := h_norm SA 0
  have hnA1 := h_norm SA 1
  have hnB0 := h_norm SB 0
  have hnB1 := h_norm SB 1
  have hS_sqrt : Real.sqrt 2 * (chshTerm 0 0 + chshTerm 0 1 + chshTerm 1 0 + chshTerm 1 1) ≤ 8 := by
    dsimp only [chshTerm]
    linarith
  have hS_bound : chshTerm 0 0 + chshTerm 0 1 + chshTerm 1 0 + chshTerm 1 1 ≤ 4 * Real.sqrt 2 := by
    have hmul := mul_le_mul_of_nonneg_left hS_sqrt (Real.sqrt_nonneg 2)
    have h2 : Real.sqrt 2 * (Real.sqrt 2 * (chshTerm 0 0 + chshTerm 0 1 + chshTerm 1 0 + chshTerm 1 1)) =
        2 * (chshTerm 0 0 + chshTerm 0 1 + chshTerm 1 0 + chshTerm 1 1) := by
      rw [← mul_assoc, Real.mul_self_sqrt (by norm_num)]
    linarith
  have hcos : Real.cos (π / 8) ^ 2 = 1 / 2 + Real.sqrt 2 / 4 := by
    rw [Real.cos_sq]
    have hangle : 2 * (π / 8) = π / 4 := by ring
    rw [hangle, Real.cos_pi_div_four]
    ring
  linarith

end Leap
