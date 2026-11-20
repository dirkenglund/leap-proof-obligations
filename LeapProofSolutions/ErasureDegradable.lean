import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Wilde Ex 13.5.2: for `ε ≤ 1/2` the erasure channel is degradable:
its complement `E_{1-ε}` is `E_ε` followed by a re-erasure with `η = (1-2ε)/(1-ε)`. -/
theorem erasure_degradable {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) :
    let η := (1 - 2 * ε) / (1 - ε)
    0 ≤ η ∧ η ≤ 1 ∧ ∀ X : Matrix n n ℂ, reErase η (erasure ε X) = erasure (1 - ε) X := by
  intro η
  have h1_sub_nonneg : 0 ≤ 1 - ε := by linarith
  have h1_sub_ne : 1 - ε ≠ 0 := by linarith
  have h_num_nonneg : 0 ≤ 1 - 2 * ε := by linarith
  have h_num_le : 1 - 2 * ε ≤ 1 - ε := by linarith
  have hη_nonneg : 0 ≤ η := div_nonneg h_num_nonneg h1_sub_nonneg
  have hη_le_one : η ≤ 1 := div_le_one_of_le₀ h_num_le h1_sub_nonneg
  have hη_mul : η * (1 - ε) = 1 - 2 * ε := div_mul_cancel₀ (1 - 2 * ε) h1_sub_ne
  have h_some_real : (1 - η) * (1 - ε) = 1 - (1 - ε) := by
    rw [sub_mul, one_mul, hη_mul]
    ring
  have h_none_real : η * (1 - ε) + ε = 1 - ε := by
    rw [hη_mul]
    ring
  have h_some_cplx : ((1 - η : ℝ) : ℂ) * ((1 - ε : ℝ) : ℂ) = ((1 - (1 - ε) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal h_some_real
  have h_none_cplx : ((η : ℝ) : ℂ) * ((1 - ε : ℝ) : ℂ) + ((ε : ℝ) : ℂ) = ((1 - ε : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_mul] using congrArg Complex.ofReal h_none_real
  refine ⟨hη_nonneg, hη_le_one, fun X => Matrix.ext fun i j => ?_⟩
  cases i <;> cases j
  · dsimp only [reErase, erasure]
    have h_sum : (∑ a : n, ((1 - ε : ℝ) : ℂ) * X a a) = ((1 - ε : ℝ) : ℂ) * X.trace := by
      rw [← Finset.mul_sum]
      rfl
    rw [h_sum, ← mul_assoc, ← add_mul, h_none_cplx]
  · rfl
  · rfl
  · dsimp only [reErase, erasure]
    rw [← mul_assoc, h_some_cplx]

end Leap
