import LeapProofObligations.Definitions

namespace Leap

/-- Wielandt–Wintner: no two elements of a nontrivial normed ℂ-algebra satisfy `[a, b] = 1`
(so `[Q, P] = iħ` has no bounded representation). -/
theorem wielandt {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] (a b : A) :
    a * b - b * a ≠ 1 := by
  intro h
  have h_comm : ∀ n : ℕ, a ^ (n + 1) * b - b * a ^ (n + 1) = (n + 1) • a ^ n := by
    intro n
    induction n with
    | zero =>
      simp [h]
    | succ n ih =>
      have h_leibniz :
          a ^ (n + 2) * b - b * a ^ (n + 2) =
            a ^ (n + 1) * (a * b - b * a) + (a ^ (n + 1) * b - b * a ^ (n + 1)) * a := by
        rw [pow_succ a (n + 1), mul_sub, sub_mul]
        simp only [mul_assoc]
        rw [sub_add_sub_cancel]
      rw [h_leibniz, h, ih, mul_one, smul_mul_assoc, ← pow_succ, add_comm]
      simp only [add_nsmul, one_nsmul]
  have h_norm_grow : ∀ n : ℕ, ((n : ℝ) + 1) * ‖a ^ n‖ ≤ 2 * ‖a ^ (n + 1)‖ * ‖b‖ := by
    intro n
    calc
      ((n : ℝ) + 1) * ‖a ^ n‖
        = ‖(n + 1) • a ^ n‖ := by
          rw [RCLike.norm_nsmul ℂ, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      _ = ‖a ^ (n + 1) * b - b * a ^ (n + 1)‖ := by rw [h_comm n]
      _ ≤ ‖a ^ (n + 1) * b‖ + ‖b * a ^ (n + 1)‖ := norm_sub_le _ _
      _ ≤ ‖a ^ (n + 1)‖ * ‖b‖ + ‖b‖ * ‖a ^ (n + 1)‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 * ‖a ^ (n + 1)‖ * ‖b‖ := by ring
  have h_pos : ∀ n : ℕ, 0 < ‖a ^ n‖ := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, norm_one]
      exact zero_lt_one
    | succ n ih =>
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have h_lhs : 0 < ((n : ℝ) + 1) * ‖a ^ n‖ := mul_pos hn1 ih
      have h_rhs : 0 < 2 * ‖a ^ (n + 1)‖ * ‖b‖ := lt_of_lt_of_le h_lhs (h_norm_grow n)
      by_contra h_le
      have h_eq : ‖a ^ (n + 1)‖ = 0 := le_antisymm (not_lt.mp h_le) (norm_nonneg _)
      rw [h_eq] at h_rhs
      simp at h_rhs
  have h_bound : ∀ n : ℕ, (n : ℝ) + 1 ≤ 2 * ‖a‖ * ‖b‖ := by
    intro n
    have h_step : ‖a ^ (n + 1)‖ ≤ ‖a ^ n‖ * ‖a‖ := by
      rw [pow_succ]
      exact norm_mul_le _ _
    have h_mul : ((n : ℝ) + 1) * ‖a ^ n‖ ≤ (2 * ‖a‖ * ‖b‖) * ‖a ^ n‖ := calc
      ((n : ℝ) + 1) * ‖a ^ n‖ ≤ 2 * ‖a ^ (n + 1)‖ * ‖b‖ := h_norm_grow n
      _ ≤ 2 * (‖a ^ n‖ * ‖a‖) * ‖b‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_step (by norm_num)) (norm_nonneg b)
      _ = (2 * ‖a‖ * ‖b‖) * ‖a ^ n‖ := by ring
    exact le_of_mul_le_mul_right h_mul (h_pos n)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖a‖ * ‖b‖)
  linarith [h_bound N]

end Leap
