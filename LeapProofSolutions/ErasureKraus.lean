import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Wilde Ex 4.7.9: the erasure channel has a Kraus form (is a channel). -/
theorem erasure_kraus {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∃ K : Option n → Matrix (Option n) n ℂ,
      (∑ i, (K i)ᴴ * K i = 1) ∧ ∀ X, erasure ε X = kraus K X := by
  let α : ℂ := ((Real.sqrt (1 - ε) : ℝ) : ℂ)
  let β : ℂ := ((Real.sqrt ε : ℝ) : ℂ)
  let K : Option n → Matrix (Option n) n ℂ := fun i => Matrix.of fun r c =>
    match i, r with
    | none, some a => if a = c then α else 0
    | none, none => 0
    | some _, some _ => 0
    | some k, none => if k = c then β else 0
  have hstar : ∀ x : ℝ, star (x : ℂ) = (x : ℂ) := fun x => by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hα_star : star α = α := hstar (Real.sqrt (1 - ε))
  have hβ_star : star β = β := hstar (Real.sqrt ε)
  have hα_sq : α * α = ((1 - ε : ℝ) : ℂ) := by
    dsimp only [α]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.mpr h1)]
  have hβ_sq : β * β = ((ε : ℝ) : ℂ) := by
    dsimp only [β]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  refine ⟨K, ?_, ?_⟩
  · ext a b
    rw [Fintype.sum_option, Matrix.add_apply, Matrix.sum_apply, Matrix.one_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_option, K, Matrix.of_apply,
      apply_ite star, star_zero, ite_mul, mul_ite, mul_zero, zero_mul, add_zero, zero_add,
      Finset.sum_const_zero, Fintype.sum_ite_eq']
    rw [hα_star, hβ_star, hα_sq, hβ_sq]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab, hab.symm]
  · intro X
    ext r s
    rw [kraus, Fintype.sum_option, Matrix.add_apply, Matrix.sum_apply]
    cases r with
    | none =>
      cases s with
      | none =>
        simp only [erasure, Matrix.mul_apply, Matrix.conjTranspose_apply, K, Matrix.of_apply,
          apply_ite star, star_zero, ite_mul, mul_ite, mul_zero, zero_mul, zero_add,
          Finset.sum_const_zero, Fintype.sum_ite_eq]
        rw [Matrix.trace, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.diag_apply, hβ_star, ← hβ_sq]
        ring
      | some b =>
        simp only [erasure, Matrix.mul_apply, Matrix.conjTranspose_apply, K, Matrix.of_apply,
          apply_ite star, star_zero, ite_mul, mul_ite, mul_zero, zero_mul, add_zero,
          Finset.sum_const_zero, Fintype.sum_ite_eq]
    | some a =>
      cases s with
      | none =>
        simp only [erasure, Matrix.mul_apply, Matrix.conjTranspose_apply, K, Matrix.of_apply,
          apply_ite star, star_zero, ite_mul, mul_ite, mul_zero, zero_mul, add_zero,
          Finset.sum_const_zero, Fintype.sum_ite_eq]
      | some b =>
        simp only [erasure, Matrix.mul_apply, Matrix.conjTranspose_apply, K, Matrix.of_apply,
          apply_ite star, star_zero, ite_mul, mul_ite, mul_zero, zero_mul, add_zero,
          Finset.sum_const_zero, Fintype.sum_ite_eq]
        rw [hα_star, ← hα_sq]
        ring

end Leap
