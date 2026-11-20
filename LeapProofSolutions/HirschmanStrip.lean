import LeapProofObligations.Definitions

open Complex Complex.HadamardThreeLines MeasureTheory
open scoped Real

namespace Leap

/-- Wilde Thm 12.2.2: Hirschman's strip inequality, both kernels. -/
theorem hirschman_strip (f : ℂ → ℂ) (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hb : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hfθ : f θ ≠ 0)
    (hα : Integrable fun t : ℝ => hirschmanAlpha θ t * Real.log (‖f (I * t)‖ ^ (1 - θ)))
    (hβ : Integrable fun t : ℝ => hirschmanBeta θ t * Real.log (‖f (1 + I * t)‖ ^ θ)) :
    Real.log ‖f θ‖ ≤ ∫ t : ℝ, (hirschmanAlpha θ t * Real.log (‖f (I * t)‖ ^ (1 - θ))
      + hirschmanBeta θ t * Real.log (‖f (1 + I * t)‖ ^ θ)) := by
  set hirschmanHalfPlane : ℝ → ℂ → ℂ := fun θ' w =>
    (((Real.sin (π * θ') : ℂ) - Complex.I * (Real.cos (π * θ') : ℂ)) +
     ((Real.sin (π * θ') : ℂ) + Complex.I * (Real.cos (π * θ') : ℂ)) * w) / (1 - w)
  set hirschmanStripMap : ℝ → ℂ → ℂ := fun θ' w =>
    (1 / 2 : ℂ) - (Complex.I / (π : ℂ)) * Complex.log (hirschmanHalfPlane θ' w)
  have harctan_mono : StrictMono Real.arctan :=
    strictMono_of_deriv_pos (fun x => by rw [(Real.hasDerivAt_arctan x).deriv]; positivity)
  have cayley_circleMap_arctan : ∀ A : ℝ,
      circleMap 0 1 (π - 2 * Real.arctan A) =
        (Complex.I * (A : ℂ) - 1) / (Complex.I * (A : ℂ) + 1) := by
    intro A
    set α := Real.arctan A
    have hcos_pos : 0 < Real.cos α := Real.cos_arctan_pos A
    have hcos_ne : (Real.cos α : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hcos_pos)
    have hden_ne : Complex.I * (A : ℂ) + 1 ≠ 0 := by
      intro h
      have hre := congr_arg Complex.re h
      simp at hre
    have htan : (Real.sin α : ℂ) = (A : ℂ) * (Real.cos α : ℂ) := by
      have h := Real.tan_arctan A
      rw [Real.tan_eq_sin_div_cos, div_eq_iff (ne_of_gt hcos_pos)] at h
      exact_mod_cast h
    have hsq : (Real.cos α : ℂ) ^ 2 + (Real.sin α : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq α
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hc2 : Real.cos (π - 2 * α) = Real.sin α ^ 2 - Real.cos α ^ 2 := by
      rw [Real.cos_pi_sub, Real.cos_two_mul']
      ring
    have hs2 : Real.sin (π - 2 * α) = 2 * Real.sin α * Real.cos α := by
      rw [Real.sin_pi_sub, Real.sin_two_mul]
    rw [hc2, hs2]
    simp only [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [eq_div_iff hden_ne]
    have h1 : ((Real.sin α : ℂ) ^ 2 - (Real.cos α : ℂ) ^ 2 +
        2 * (Real.sin α : ℂ) * (Real.cos α : ℂ) * Complex.I) *
        (Complex.I * (A : ℂ) + 1) * (Real.cos α : ℂ) =
        (Complex.I * (A : ℂ) - 1) * (Real.cos α : ℂ) := by
      calc ((Real.sin α : ℂ) ^ 2 - (Real.cos α : ℂ) ^ 2 +
            2 * (Real.sin α : ℂ) * (Real.cos α : ℂ) * Complex.I) *
            (Complex.I * (A : ℂ) + 1) * (Real.cos α : ℂ)
          = ((Real.sin α : ℂ) ^ 2 - (Real.cos α : ℂ) ^ 2 +
            2 * (Real.sin α : ℂ) * (Real.cos α : ℂ) * Complex.I) *
            (Complex.I * ((A : ℂ) * (Real.cos α : ℂ)) + (Real.cos α : ℂ)) := by ring
        _ = ((Real.sin α : ℂ) ^ 2 - (Real.cos α : ℂ) ^ 2 +
            2 * (Real.sin α : ℂ) * (Real.cos α : ℂ) * Complex.I) *
            (Complex.I * (Real.sin α : ℂ) + (Real.cos α : ℂ)) := by rw [← htan]
        _ = (Complex.I * (Real.sin α : ℂ) - (Real.cos α : ℂ)) *
            ((Real.cos α : ℂ) ^ 2 + (Real.sin α : ℂ) ^ 2) := by
              ring_nf
              rw [Complex.I_sq]
              ring
        _ = Complex.I * (Real.sin α : ℂ) - (Real.cos α : ℂ) := by rw [hsq, mul_one]
        _ = Complex.I * ((A : ℂ) * (Real.cos α : ℂ)) - (Real.cos α : ℂ) := by rw [htan]
        _ = (Complex.I * (A : ℂ) - 1) * (Real.cos α : ℂ) := by ring
    exact mul_right_cancel₀ hcos_ne h1
  have hirschmanHalfPlane_cayley : ∀ (θ' A : ℝ),
      hirschmanHalfPlane θ' ((Complex.I * (A : ℂ) - 1) / (Complex.I * (A : ℂ) + 1)) =
        Complex.I * ((A * Real.sin (π * θ') - Real.cos (π * θ') : ℝ) : ℂ) := by
    intro θ' A
    have hden_ne : Complex.I * (A : ℂ) + 1 ≠ 0 := by
      intro h
      have hre := congr_arg Complex.re h
      simp at hre
    dsimp only [hirschmanHalfPlane]
    have hsub : (1 : ℂ) - (Complex.I * (A : ℂ) - 1) / (Complex.I * (A : ℂ) + 1) =
        2 / (Complex.I * (A : ℂ) + 1) := by
      field_simp [hden_ne]
      ring
    rw [hsub]
    push_cast
    field_simp [hden_ne]
    ring
  have hirschmanHalfPlane_re : ∀ (θ' : ℝ) (w : ℂ),
      (hirschmanHalfPlane θ' w).re =
        Real.sin (π * θ') * (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
    intro θ' w
    dsimp only [hirschmanHalfPlane]
    rw [Complex.div_re]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.normSq_apply]
    ring
  have hirschmanStripMap_disc_props :
      hirschmanStripMap θ 0 = (θ : ℂ) ∧
      Set.MapsTo (hirschmanStripMap θ) (Metric.ball (0 : ℂ) 1) (verticalStrip 0 1) ∧
      DifferentiableOn ℂ (hirschmanStripMap θ) (Metric.ball (0 : ℂ) 1) ∧
      (∀ φ ∈ Set.Ioo (0 : ℝ) (2 * π), φ ≠ 2 * π * θ →
        hirschmanStripMap θ (circleMap 0 1 φ) ∈ verticalClosedStrip 0 1 ∧
        ContinuousAt (hirschmanStripMap θ) (circleMap 0 1 φ)) := by
    have hpi : 0 < π := Real.pi_pos
    have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpi)
    have hsin_pos : 0 < Real.sin (π * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hθ.1) (by nlinarith [hθ.2])
    have hre_strip : ∀ w : ℂ, (hirschmanStripMap θ w).re =
        1 / 2 + (hirschmanHalfPlane θ w).arg / π := by
      intro w
      dsimp only [hirschmanStripMap]
      have hdiv : Complex.I / (π : ℂ) = ((π⁻¹ : ℝ) : ℂ) * Complex.I := by
        rw [div_eq_mul_inv, ← Complex.ofReal_inv]
        ring
      rw [hdiv]
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.log_im,
        Complex.mul_im]
      ring
    have hdiff_of_slit : ∀ w : ℂ, 1 - w ≠ 0 → hirschmanHalfPlane θ w ∈ Complex.slitPlane →
        DifferentiableAt ℂ (hirschmanStripMap θ) w := by
      intro w hw hslit
      have hu : DifferentiableAt ℂ (hirschmanHalfPlane θ) w := by
        dsimp only [hirschmanHalfPlane]
        exact (((differentiableAt_const _).add
          ((differentiableAt_const _).mul differentiableAt_id)).div
          ((differentiableAt_const _).sub differentiableAt_id) hw)
      dsimp only [hirschmanStripMap]
      exact (differentiableAt_const _).sub
        ((differentiableAt_const _).mul ((Complex.differentiableAt_log hslit).comp w hu))
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [hirschmanStripMap, hirschmanHalfPlane]
      simp only [mul_zero, add_zero, sub_zero, div_one]
      set z0 : ℂ := ((π * (θ - 1 / 2) : ℝ) : ℂ) * Complex.I
      have hexp0 : ((Real.sin (π * θ) : ℂ) - Complex.I * (Real.cos (π * θ) : ℂ)) =
          Complex.exp z0 := by
        rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        have hc : Real.cos (π * (θ - 1 / 2)) = Real.sin (π * θ) := by
          have : π * (θ - 1 / 2) = -(π / 2 - π * θ) := by ring
          rw [this, Real.cos_neg, Real.cos_pi_div_two_sub]
        have hs : Real.sin (π * (θ - 1 / 2)) = -Real.cos (π * θ) := by
          have : π * (θ - 1 / 2) = -(π / 2 - π * θ) := by ring
          rw [this, Real.sin_neg, Real.sin_pi_div_two_sub]
        rw [hc, hs]
        push_cast
        ring
      rw [hexp0]
      have him0 : z0.im = π * (θ - 1 / 2) := by simp [z0]
      have hlog0 : Complex.log (Complex.exp z0) = z0 := by
        apply Complex.log_exp
        · rw [him0]; nlinarith [hθ.1]
        · rw [him0]; nlinarith [hθ.2]
      rw [hlog0]
      simp only [z0]
      push_cast
      field_simp [hpi_ne]
      ring_nf
      rw [Complex.I_sq]
      ring
    · intro w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      have hw_sq : Complex.normSq w < 1 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg w]
      have h1w : 1 - w ≠ 0 := by
        intro h
        have hw1 : w = 1 := (sub_eq_zero.mp h).symm
        rw [hw1, norm_one] at hw
        exact lt_irrefl 1 hw
      have h1w_pos : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr h1w
      have hure_pos : 0 < (hirschmanHalfPlane θ w).re := by
        rw [hirschmanHalfPlane_re]
        exact div_pos (mul_pos hsin_pos (by linarith)) h1w_pos
      set u := hirschmanHalfPlane θ w
      have hu_ne : u ≠ 0 := by
        intro h; rw [h, Complex.zero_re] at hure_pos; exact lt_irrefl 0 hure_pos
      have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
      have him_lt : |u.im| < ‖u‖ := by
        have hnsq : u.im ^ 2 < ‖u‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          nlinarith [hure_pos]
        have habs : |u.im| ^ 2 < ‖u‖ ^ 2 := by rw [sq_abs]; exact hnsq
        nlinarith [abs_nonneg u.im, hu_norm_pos]
      have hdiv_lt1 : u.im / ‖u‖ < 1 := (div_lt_one hu_norm_pos).mpr ((abs_lt.mp him_lt).2)
      have hdiv_gt1 : -1 < u.im / ‖u‖ := by
        rw [lt_div_iff₀ hu_norm_pos]
        linarith [(abs_lt.mp him_lt).1]
      have harg_eq : u.arg = Real.arcsin (u.im / ‖u‖) :=
        Complex.arg_of_re_nonneg (le_of_lt hure_pos)
      have harg_lt : u.arg < π / 2 := by
        rw [harg_eq, Real.arcsin_lt_pi_div_two]; exact hdiv_lt1
      have harg_gt : -(π / 2) < u.arg := by
        rw [harg_eq, Real.neg_pi_div_two_lt_arcsin]; exact hdiv_gt1
      show hirschmanStripMap θ w ∈ Complex.re ⁻¹' Set.Ioo 0 1
      simp only [Set.mem_preimage, Set.mem_Ioo, hre_strip]
      have hlt1 : u.arg / π < 1 / 2 := by rw [div_lt_iff₀ hpi]; linarith
      have hgt0 : -(1 / 2) < u.arg / π := by rw [lt_div_iff₀ hpi]; linarith
      constructor <;> linarith
    · intro w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      have hw_sq : Complex.normSq w < 1 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg w]
      have h1w : 1 - w ≠ 0 := by
        intro h
        have hw1 : w = 1 := (sub_eq_zero.mp h).symm
        rw [hw1, norm_one] at hw
        exact lt_irrefl 1 hw
      have hure_pos : 0 < (hirschmanHalfPlane θ w).re := by
        rw [hirschmanHalfPlane_re]
        exact div_pos (mul_pos hsin_pos (by linarith)) (Complex.normSq_pos.mpr h1w)
      exact (hdiff_of_slit w h1w (Complex.mem_slitPlane_iff.mpr (Or.inl hure_pos))).differentiableWithinAt
    · intro φ hφ hφ_ne
      set β : ℝ := (π - φ) / 2
      have hβ1 : -(π / 2) < β := by dsimp [β]; linarith [hφ.2]
      have hβ2 : β < π / 2 := by dsimp [β]; linarith [hφ.1]
      set A : ℝ := Real.tan β
      have harctan : Real.arctan A = β := Real.arctan_tan hβ1 hβ2
      have hφ_eq : φ = π - 2 * Real.arctan A := by rw [harctan]; dsimp [β]; ring
      have hw_eq : circleMap 0 1 φ = (Complex.I * (A : ℂ) - 1) / (Complex.I * (A : ℂ) + 1) := by
        rw [hφ_eq, cayley_circleMap_arctan]
      have hden_ne : Complex.I * (A : ℂ) + 1 ≠ 0 := by
        intro h; have hre := congr_arg Complex.re h; simp at hre
      have h1w_ne : 1 - circleMap 0 1 φ ≠ 0 := by
        rw [hw_eq]
        have hsub : (1 : ℂ) - (Complex.I * (A : ℂ) - 1) / (Complex.I * (A : ℂ) + 1) =
            2 / (Complex.I * (A : ℂ) + 1) := by field_simp [hden_ne]; ring
        rw [hsub]
        exact div_ne_zero two_ne_zero hden_ne
      set y : ℝ := A * Real.sin (π * θ) - Real.cos (π * θ)
      have hu_eq : hirschmanHalfPlane θ (circleMap 0 1 φ) = Complex.I * (y : ℂ) := by
        rw [hw_eq, hirschmanHalfPlane_cayley]
      have hy_ne : y ≠ 0 := by
        intro hy
        have hAtan : Real.tan β = Real.tan (π / 2 - π * θ) := by
          rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos (π * θ), inv_div,
            eq_div_iff (ne_of_gt hsin_pos)]
          dsimp [y, A] at hy
          linarith [hy]
        have hθ_in : π / 2 - π * θ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
          constructor <;> nlinarith [hθ.1, hθ.2]
        have hβ_in : β ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨hβ1, hβ2⟩
        have hβ_eq : β = π / 2 - π * θ := Real.strictMonoOn_tan.injOn hβ_in hθ_in hAtan
        apply hφ_ne
        dsimp [β] at hβ_eq
        linarith
      have hslit : hirschmanHalfPlane θ (circleMap 0 1 φ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff, hu_eq]
        right
        simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, one_mul, zero_add]
        exact hy_ne
      refine ⟨?_, (hdiff_of_slit _ h1w_ne hslit).continuousAt⟩
      show hirschmanStripMap θ (circleMap 0 1 φ) ∈ Complex.re ⁻¹' Set.Icc 0 1
      simp only [Set.mem_preimage, Set.mem_Icc, hre_strip]
      have hure0 : 0 ≤ (hirschmanHalfPlane θ (circleMap 0 1 φ)).re := by
        rw [hu_eq]
        simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, mul_zero, sub_self, le_refl]
      have harg_eq : (hirschmanHalfPlane θ (circleMap 0 1 φ)).arg =
          Real.arcsin ((hirschmanHalfPlane θ (circleMap 0 1 φ)).im /
            ‖hirschmanHalfPlane θ (circleMap 0 1 φ)‖) :=
        Complex.arg_of_re_nonneg hure0
      have hle1 : (hirschmanHalfPlane θ (circleMap 0 1 φ)).arg / π ≤ 1 / 2 := by
        rw [div_le_iff₀ hpi, harg_eq]
        linarith [Real.arcsin_le_pi_div_two ((hirschmanHalfPlane θ (circleMap 0 1 φ)).im /
          ‖hirschmanHalfPlane θ (circleMap 0 1 φ)‖)]
      have hge0 : -(1 / 2) ≤ (hirschmanHalfPlane θ (circleMap 0 1 φ)).arg / π := by
        rw [le_div_iff₀ hpi, harg_eq]
        linarith [Real.neg_pi_div_two_le_arcsin ((hirschmanHalfPlane θ (circleMap 0 1 φ)).im /
          ‖hirschmanHalfPlane θ (circleMap 0 1 φ)‖)]
      constructor <;> linarith
  have disc_log_norm_le_boundary_integral : ∀ (g : ℂ → ℂ),
      DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) →
      BddAbove ((norm ∘ g) '' Metric.ball (0 : ℂ) 1) →
      g 0 ≠ 0 →
      (∀ᵐ φ ∂(volume.restrict (Set.Ioc (0 : ℝ) (2 * π))),
        Filter.Tendsto (fun n : ℕ => g (circleMap 0 (1 - 1 / ((n : ℝ) + 2)) φ))
          Filter.atTop (nhds (g (circleMap 0 1 φ)))) →
      IntegrableOn (fun φ : ℝ => Real.log ‖g (circleMap 0 1 φ)‖)
        (Set.Ioc (0 : ℝ) (2 * π)) →
      Real.log ‖g 0‖ ≤
        (2 * π)⁻¹ * ∫ φ in Set.Ioc (0 : ℝ) (2 * π), Real.log ‖g (circleMap 0 1 φ)‖ := by
    intro g hg hb_g hg0 hrad hint
    have hpi : 0 < π := Real.pi_pos
    have h2pi : 0 < 2 * π := by positivity
    rcases hb_g with ⟨B, hB⟩
    set M : ℝ := max 1 B
    have hM1 : 1 ≤ M := le_max_left 1 B
    have hlogM_nonneg : 0 ≤ Real.log M := Real.log_nonneg hM1
    have hnorm_le_M : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖g w‖ ≤ M := by
      intro w hw
      exact le_trans (hB ⟨w, hw, rfl⟩) (le_max_right 1 B)
    have hlog_le_logM : ∀ x : ℝ, 0 ≤ x → x ≤ M → Real.log x ≤ Real.log M := by
      intro x hx hxM
      rcases eq_or_lt_of_le hx with rfl | hx_pos
      · rw [Real.log_zero]; exact hlogM_nonneg
      · exact Real.log_le_log hx_pos hxM
    have hg0_le : Real.log ‖g 0‖ ≤ Real.log M :=
      hlog_le_logM ‖g 0‖ (norm_nonneg _) (hnorm_le_M 0 (Metric.mem_ball_self zero_lt_one))
    set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
    have hr_pos : ∀ n : ℕ, 0 < r n := by
      intro n
      simp only [r]
      have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hdiv : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one (by linarith)).mpr hn2
      linarith
    have hr_lt1 : ∀ n : ℕ, r n < 1 := by
      intro n
      simp only [r]
      have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      linarith [one_div_pos.mpr hn2]
    have han_ball : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) 1) :=
      hg.analyticOnNhd Metric.isOpen_ball
    have han0 : AnalyticAt ℂ g 0 := han_ball 0 (Metric.mem_ball_self zero_lt_one)
    have hmo0 : meromorphicOrderAt g 0 = 0 := by
      rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl]
      rw [meromorphicOrderAt_eq_int_iff han0.meromorphicAt]
      exact ⟨g, han0, hg0, Filter.Eventually.of_forall (fun z => by simp)⟩
    have hconst_int : IntegrableOn (fun _ : ℝ => Real.log M) (Set.Ioc (0 : ℝ) (2 * π)) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt h2pi)]
      exact intervalIntegrable_const
    have hconst_eval : ∫ _ in Set.Ioc (0 : ℝ) (2 * π), Real.log M = 2 * π * Real.log M := by
      rw [← intervalIntegral.integral_of_le (le_of_lt h2pi), intervalIntegral.integral_const,
        sub_zero, smul_eq_mul]
    have hjensen : ∀ n : ℕ,
        IntegrableOn (fun φ : ℝ => Real.log ‖g (circleMap 0 (r n) φ)‖)
          (Set.Ioc (0 : ℝ) (2 * π)) ∧
        2 * π * Real.log ‖g 0‖ ≤
          ∫ φ in Set.Ioc (0 : ℝ) (2 * π), Real.log ‖g (circleMap 0 (r n) φ)‖ := by
      intro n
      have hr_abs : |r n| = r n := abs_of_pos (hr_pos n)
      have hcb_sub : Metric.closedBall (0 : ℂ) |r n| ⊆ Metric.ball (0 : ℂ) 1 := by
        intro w hw
        rw [Metric.mem_closedBall, dist_zero_right, hr_abs] at hw
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt hw (hr_lt1 n)
      have han_cb : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) |r n|) :=
        han_ball.mono hcb_sub
      have hci : CircleIntegrable (fun x => Real.log ‖g x‖) 0 (r n) :=
        MeromorphicOn.circleIntegrable_log_norm (han_cb.mono Metric.sphere_subset_closedBall).meromorphicOn
      have hint_n : IntegrableOn (fun φ : ℝ => Real.log ‖g (circleMap 0 (r n) φ)‖)
          (Set.Ioc (0 : ℝ) (2 * π)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt h2pi)).mp hci
      have hca := AnalyticOnNhd.circleAverage_log_norm (ne_of_gt (hr_pos n)) han_cb hg0
      have hsum_nonneg : 0 ≤ ∑ᶠ u : ℂ,
          ↑(MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |r n|) u) *
            Real.log (r n * ‖(0 : ℂ) - u‖⁻¹) := by
        apply finsum_nonneg
        intro u
        set d := MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |r n|) u
        have hd_nonneg : 0 ≤ d := MeromorphicOn.AnalyticOnNhd.divisor_nonneg han_cb u
        rcases eq_or_lt_of_le hd_nonneg with hd0 | hd_pos
        · rw [← hd0]; simp
        · have hu_mem : u ∈ Metric.closedBall (0 : ℂ) |r n| := by
            by_contra hu_not
            have hd_zero : d = 0 := by simp [d, hu_not]
            omega
          have hu_ne : u ≠ 0 := by
            intro hu0
            have hd_zero : d = 0 := by
              subst hu0
              simp [d, MeromorphicOn.divisor_def, hmo0]
            omega
          have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
          have hu_norm_le : ‖u‖ ≤ r n := by
            rw [Metric.mem_closedBall, dist_zero_right, hr_abs] at hu_mem
            exact hu_mem
          have h1_le : 1 ≤ r n * ‖(0 : ℂ) - u‖⁻¹ := by
            simp only [zero_sub, norm_neg]
            rw [← div_eq_mul_inv, one_le_div hu_norm_pos]
            exact hu_norm_le
          have hd_cast : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd_pos
          exact mul_nonneg hd_cast (Real.log_nonneg h1_le)
      have hle_ca : Real.log ‖g 0‖ ≤ Real.circleAverage (fun x => Real.log ‖g x‖) 0 (r n) := by
        linarith [hca, hsum_nonneg]
      rw [Real.circleAverage_def, smul_eq_mul,
        intervalIntegral.integral_of_le (le_of_lt h2pi)] at hle_ca
      refine ⟨hint_n, ?_⟩
      have := mul_le_mul_of_nonneg_left hle_ca (le_of_lt h2pi)
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h2pi), one_mul] at this
    set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * π))
    set h : ℕ → ℝ → ℝ := fun n φ => Real.log M - Real.log ‖g (circleMap 0 (r n) φ)‖
    set H : ℝ → ℝ := fun φ => Real.log M - Real.log ‖g (circleMap 0 1 φ)‖
    have hh_nonneg : ∀ n φ, 0 ≤ h n φ := by
      intro n φ
      have hmem : circleMap (0 : ℂ) (r n) φ ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (hr_pos n)]
        exact hr_lt1 n
      have hle := hlog_le_logM ‖g (circleMap 0 (r n) φ)‖ (norm_nonneg _) (hnorm_le_M _ hmem)
      simp only [h]
      linarith
    have hh_meas : ∀ n : ℕ, Measurable (fun φ => ENNReal.ofReal (h n φ)) := by
      intro n
      have hcont_cm : Continuous (circleMap (0 : ℂ) (r n)) := continuous_circleMap 0 (r n)
      have hmaps : ∀ φ : ℝ, circleMap (0 : ℂ) (r n) φ ∈ Metric.ball (0 : ℂ) 1 := by
        intro φ
        rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (hr_pos n)]
        exact hr_lt1 n
      have hcont_g : Continuous (fun φ => g (circleMap 0 (r n) φ)) :=
        hg.continuousOn.comp_continuous hcont_cm hmaps
      exact ENNReal.measurable_ofReal.comp
        (measurable_const.sub (Real.measurable_log.comp hcont_g.norm.measurable))
    have hH_both : ∀ᵐ φ ∂μ, 0 ≤ H φ ∧ ENNReal.ofReal (H φ) ≤
        Filter.liminf (fun n : ℕ => ENNReal.ofReal (h n φ)) Filter.atTop := by
      filter_upwards [hrad] with φ hφ_tend
      have hnorm_tend : Filter.Tendsto (fun n : ℕ => ‖g (circleMap 0 (r n) φ)‖)
          Filter.atTop (nhds ‖g (circleMap 0 1 φ)‖) :=
        continuous_norm.continuousAt.tendsto.comp hφ_tend
      have hnorm_le_each : ∀ n : ℕ, ‖g (circleMap 0 (r n) φ)‖ ≤ M := by
        intro n
        apply hnorm_le_M
        rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (hr_pos n)]
        exact hr_lt1 n
      have hL_le_M : ‖g (circleMap 0 1 φ)‖ ≤ M :=
        le_of_tendsto' hnorm_tend hnorm_le_each
      have hH_nonneg_φ : 0 ≤ H φ := by
        have := hlog_le_logM ‖g (circleMap 0 1 φ)‖ (norm_nonneg _) hL_le_M
        simp only [H]
        linarith
      refine ⟨hH_nonneg_φ, ?_⟩
      by_cases hL0 : ‖g (circleMap 0 1 φ)‖ = 0
      · have hH_eq : H φ = Real.log M := by simp [H, hL0]
        have hev_lt1 : ∀ᶠ n : ℕ in Filter.atTop, ‖g (circleMap 0 (r n) φ)‖ < 1 := by
          rw [hL0] at hnorm_tend
          exact hnorm_tend.eventually (gt_mem_nhds zero_lt_one)
        have hev_le : ∀ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal (H φ) ≤ ENNReal.ofReal (h n φ) := by
          filter_upwards [hev_lt1] with n hn_lt1
          apply ENNReal.ofReal_le_ofReal
          rw [hH_eq]
          simp only [h]
          have hlog_np : Real.log ‖g (circleMap 0 (r n) φ)‖ ≤ 0 :=
            Real.log_nonpos (norm_nonneg _) (le_of_lt hn_lt1)
          linarith
        exact Filter.le_liminf_of_le (by isBoundedDefault) hev_le
      · have hlog_tend : Filter.Tendsto (fun n : ℕ => Real.log ‖g (circleMap 0 (r n) φ)‖)
            Filter.atTop (nhds (Real.log ‖g (circleMap 0 1 φ)‖)) :=
          (Real.continuousAt_log hL0).tendsto.comp hnorm_tend
        have hofr_tend : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (h n φ))
            Filter.atTop (nhds (ENNReal.ofReal (H φ))) :=
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub hlog_tend)
        exact le_of_eq hofr_tend.liminf_eq.symm
    have hH_ae_nonneg : 0 ≤ᵐ[μ] H := hH_both.mono (fun _ hφ => hφ.1)
    have hH_ae_liminf : ∀ᵐ φ ∂μ, ENNReal.ofReal (H φ) ≤
        Filter.liminf (fun n : ℕ => ENNReal.ofReal (h n φ)) Filter.atTop :=
      hH_both.mono (fun _ hφ => hφ.2)
    have hfatou : ∫⁻ φ, ENNReal.ofReal (H φ) ∂μ ≤
        Filter.liminf (fun n : ℕ => ∫⁻ φ, ENNReal.ofReal (h n φ) ∂μ) Filter.atTop :=
      le_trans (lintegral_mono_ae hH_ae_liminf) (lintegral_liminf_le hh_meas)
    have hH_int : Integrable H μ := hconst_int.sub hint
    have hlhs : ∫⁻ φ, ENNReal.ofReal (H φ) ∂μ =
        ENNReal.ofReal (2 * π * Real.log M -
          ∫ φ in Set.Ioc (0 : ℝ) (2 * π), Real.log ‖g (circleMap 0 1 φ)‖) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hH_int hH_ae_nonneg]
      congr 1
      show ∫ φ, (Real.log M - Real.log ‖g (circleMap 0 1 φ)‖) ∂μ = _
      rw [integral_sub hconst_int hint, hconst_eval]
    have hrhs_each : ∀ n : ℕ, ∫⁻ φ, ENNReal.ofReal (h n φ) ∂μ ≤
        ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)) := by
      intro n
      have hhn_int : Integrable (h n) μ := hconst_int.sub (hjensen n).1
      have hhn_ae : 0 ≤ᵐ[μ] h n := Filter.Eventually.of_forall (hh_nonneg n)
      rw [← ofReal_integral_eq_lintegral_ofReal hhn_int hhn_ae]
      apply ENNReal.ofReal_le_ofReal
      have hint_eq : ∫ φ, h n φ ∂μ = 2 * π * Real.log M -
          ∫ φ in Set.Ioc (0 : ℝ) (2 * π), Real.log ‖g (circleMap 0 (r n) φ)‖ := by
        show ∫ φ, (Real.log M - Real.log ‖g (circleMap 0 (r n) φ)‖) ∂μ = _
        rw [integral_sub hconst_int (hjensen n).1, hconst_eval]
      rw [hint_eq]
      linarith [(hjensen n).2]
    have hrhs : Filter.liminf (fun n : ℕ => ∫⁻ φ, ENNReal.ofReal (h n φ) ∂μ) Filter.atTop ≤
        ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)) := by
      calc Filter.liminf (fun n : ℕ => ∫⁻ φ, ENNReal.ofReal (h n φ) ∂μ) Filter.atTop
          ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖))) Filter.atTop :=
            Filter.liminf_le_liminf (Filter.Eventually.of_forall hrhs_each)
        _ = ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)) :=
            Filter.liminf_const (ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)))
    have hcomb : ENNReal.ofReal (2 * π * Real.log M -
          ∫ φ in Set.Ioc (0 : ℝ) (2 * π), Real.log ‖g (circleMap 0 1 φ)‖) ≤
        ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)) := by
      rw [← hlhs]
      exact le_trans hfatou hrhs
    have hreal_le : 2 * π * Real.log M -
        ∫ φ in Set.Ioc (0 : ℝ) (2 * π), Real.log ‖g (circleMap 0 1 φ)‖ ≤
        2 * π * (Real.log M - Real.log ‖g 0‖) := by
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_of_lt h2pi) (by linarith [hg0_le]))).mp hcomb
    have hmul : 2 * π * Real.log ‖g 0‖ ≤
        ∫ φ in Set.Ioc (0 : ℝ) (2 * π), Real.log ‖g (circleMap 0 1 φ)‖ := by
      linarith
    have hdiv := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr (le_of_lt h2pi))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h2pi), one_mul] at hdiv
  have hirschman_arc_beta_integral :
      IntegrableOn (fun φ : ℝ => Real.log ‖f (hirschmanStripMap θ (circleMap 0 1 φ))‖)
        (Set.Ioo 0 (2 * π * θ)) ∧
      (∫ φ in Set.Ioo 0 (2 * π * θ), Real.log ‖f (hirschmanStripMap θ (circleMap 0 1 φ))‖) =
        2 * π * ∫ t : ℝ, hirschmanBeta θ t * Real.log (‖f (1 + I * t)‖ ^ θ) := by
    have hpi : 0 < π := Real.pi_pos
    have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpi)
    have hsin_pos : 0 < Real.sin (π * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hθ.1) (by nlinarith [hθ.2])
    have hθ_in : π / 2 - π * θ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
      constructor <;> nlinarith [hθ.1, hθ.2]
    have htan_cot : Real.tan (π / 2 - π * θ) = Real.cos (π * θ) / Real.sin (π * θ) := by
      rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos (π * θ), inv_div]
    set Aβ : ℝ → ℝ := fun t => (Real.exp (-π * t) + Real.cos (π * θ)) / Real.sin (π * θ)
    set φβ : ℝ → ℝ := fun t => π - 2 * Real.arctan (Aβ t)
    set φβ' : ℝ → ℝ := fun t => 2 * π * θ * hirschmanBeta θ t
    have hstrict : StrictMono φβ := by
      intro t₁ t₂ ht
      have hexp : Real.exp (-π * t₂) < Real.exp (-π * t₁) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      have hA : Aβ t₂ < Aβ t₁ :=
        div_lt_div_of_pos_right (by linarith) hsin_pos
      have harc : Real.arctan (Aβ t₂) < Real.arctan (Aβ t₁) :=
        harctan_mono hA
      dsimp [φβ]
      linarith
    have hinj : Set.InjOn φβ Set.univ := hstrict.injective.injOn
    have himg : φβ '' Set.univ = Set.Ioo 0 (2 * π * θ) := by
      ext φ
      simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ioo]
      constructor
      · rintro ⟨t, rfl⟩
        have h1 : Real.arctan (Aβ t) < π / 2 := Real.arctan_lt_pi_div_two (Aβ t)
        have hA_gt : Real.tan (π / 2 - π * θ) < Aβ t := by
          rw [htan_cot]
          exact div_lt_div_of_pos_right (by linarith [Real.exp_pos (-π * t)]) hsin_pos
        have h2 : π / 2 - π * θ < Real.arctan (Aβ t) := by
          calc π / 2 - π * θ = Real.arctan (Real.tan (π / 2 - π * θ)) :=
                (Real.arctan_tan hθ_in.1 hθ_in.2).symm
            _ < Real.arctan (Aβ t) := harctan_mono hA_gt
        dsimp [φβ]
        constructor <;> linarith
      · rintro ⟨hφ0, hφ2⟩
        set β : ℝ := (π - φ) / 2
        have hβ_gt : π / 2 - π * θ < β := by dsimp [β]; linarith
        have hβ_lt : β < π / 2 := by dsimp [β]; linarith
        have hβ_in : β ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨lt_trans hθ_in.1 hβ_gt, hβ_lt⟩
        have htan_lt : Real.cos (π * θ) / Real.sin (π * θ) < Real.tan β := by
          rw [← htan_cot]
          exact Real.strictMonoOn_tan hθ_in hβ_in hβ_gt
        have hy_pos : 0 < Real.tan β * Real.sin (π * θ) - Real.cos (π * θ) := by
          have := (div_lt_iff₀ hsin_pos).mp htan_lt
          linarith
        set y : ℝ := Real.tan β * Real.sin (π * θ) - Real.cos (π * θ)
        refine ⟨-Real.log y / π, ?_⟩
        have hexp_t : Real.exp (-π * (-Real.log y / π)) = y := by
          have : -π * (-Real.log y / π) = Real.log y := by
            field_simp [ne_of_gt hpi]
          rw [this, Real.exp_log hy_pos]
        have hA_eq : Aβ (-Real.log y / π) = Real.tan β := by
          dsimp [Aβ]
          rw [hexp_t]
          dsimp [y]
          field_simp [ne_of_gt hsin_pos]
          ring
        dsimp [φβ]
        rw [hA_eq, Real.arctan_tan hβ_in.1 hβ_in.2]
        dsimp [β]
        ring
    have hdenom_all : ∀ t : ℝ,
        2 * Real.exp (-(π * t)) * (Real.cosh (π * t) + Real.cos (π * θ)) =
          Real.sin (π * θ) ^ 2 + (Real.exp (-(π * t)) + Real.cos (π * θ)) ^ 2 ∧
        0 < Real.cosh (π * t) + Real.cos (π * θ) := by
      intro t
      have hexp_inv : Real.exp (-(π * t)) * Real.exp (π * t) = 1 := by
        rw [← Real.exp_add]; simp
      have hsc : Real.sin (π * θ) ^ 2 + Real.cos (π * θ) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq (π * θ)
      have hid : 2 * Real.exp (-(π * t)) * (Real.cosh (π * t) + Real.cos (π * θ)) =
          Real.sin (π * θ) ^ 2 + (Real.exp (-(π * t)) + Real.cos (π * θ)) ^ 2 := by
        rw [Real.cosh_eq]
        calc 2 * Real.exp (-(π * t)) * ((Real.exp (π * t) + Real.exp (-(π * t))) / 2 + Real.cos (π * θ))
            = Real.exp (-(π * t)) * Real.exp (π * t) + Real.exp (-(π * t)) ^ 2 +
                2 * Real.exp (-(π * t)) * Real.cos (π * θ) := by ring
          _ = (Real.sin (π * θ) ^ 2 + Real.cos (π * θ) ^ 2) + Real.exp (-(π * t)) ^ 2 +
                2 * Real.exp (-(π * t)) * Real.cos (π * θ) := by rw [hexp_inv, hsc]
          _ = Real.sin (π * θ) ^ 2 + (Real.exp (-(π * t)) + Real.cos (π * θ)) ^ 2 := by ring
      have hsq_pos : 0 < Real.sin (π * θ) ^ 2 + (Real.exp (-(π * t)) + Real.cos (π * θ)) ^ 2 := by
        positivity
      have h2e_pos : 0 < 2 * Real.exp (-(π * t)) := by positivity
      exact ⟨hid, by nlinarith⟩
    have hderiv : ∀ t ∈ (Set.univ : Set ℝ), HasDerivWithinAt φβ (φβ' t) Set.univ t := by
      intro t _
      have hd1 : HasDerivAt (fun s : ℝ => -π * s) (-π) t := by
        simpa using (hasDerivAt_id t).const_mul (-π)
      have hd2 : HasDerivAt (fun s : ℝ => Real.exp (-π * s)) (Real.exp (-π * t) * (-π)) t :=
        (Real.hasDerivAt_exp (-π * t)).comp t hd1
      have hd3 : HasDerivAt Aβ ((Real.exp (-π * t) * (-π)) / Real.sin (π * θ)) t :=
        (hd2.add_const (Real.cos (π * θ))).div_const (Real.sin (π * θ))
      have hd4 : HasDerivAt (fun s => Real.arctan (Aβ s))
          ((1 / (1 + Aβ t ^ 2)) * ((Real.exp (-π * t) * (-π)) / Real.sin (π * θ))) t :=
        (Real.hasDerivAt_arctan (Aβ t)).comp t hd3
      have hd5 : HasDerivAt φβ
          (0 - 2 * ((1 / (1 + Aβ t ^ 2)) * ((Real.exp (-π * t) * (-π)) / Real.sin (π * θ)))) t :=
        (hasDerivAt_const t π).sub (hd4.const_mul 2)
      have hval_eq :
          0 - 2 * ((1 / (1 + Aβ t ^ 2)) * ((Real.exp (-π * t) * (-π)) / Real.sin (π * θ))) =
            φβ' t := by
        dsimp [φβ', hirschmanBeta, Aβ]
        have hθ_ne : θ ≠ 0 := ne_of_gt hθ.1
        have hsin_ne : Real.sin (π * θ) ≠ 0 := ne_of_gt hsin_pos
        have hcosh_ne : Real.cosh (π * t) + Real.cos (π * θ) ≠ 0 := ne_of_gt (hdenom_all t).2
        have h1A_ne : 1 + ((Real.exp (-π * t) + Real.cos (π * θ)) / Real.sin (π * θ)) ^ 2 ≠ 0 := by
          positivity
        field_simp [hθ_ne, hsin_ne, hcosh_ne, h1A_ne]
        rw [← (hdenom_all t).1]
        ring
      rw [← hval_eq]
      exact hd5.hasDerivWithinAt
    have hφβ'_pos : ∀ t : ℝ, 0 < φβ' t := by
      intro t
      dsimp [φβ', hirschmanBeta]
      have hcosh_pos := (hdenom_all t).2
      have hθ_pos := hθ.1
      positivity
    have hcomp : ∀ t : ℝ, hirschmanStripMap θ (circleMap 0 1 (φβ t)) = 1 + Complex.I * (t : ℂ) := by
      intro t
      have hw : circleMap 0 1 (φβ t) =
          (Complex.I * (Aβ t : ℂ) - 1) / (Complex.I * (Aβ t : ℂ) + 1) :=
        cayley_circleMap_arctan (Aβ t)
      have hu : hirschmanHalfPlane θ (circleMap 0 1 (φβ t)) =
          Complex.I * (Real.exp (-π * t) : ℂ) := by
        rw [hw, hirschmanHalfPlane_cayley]
        congr 1
        have h1 : Aβ t * Real.sin (π * θ) - Real.cos (π * θ) = Real.exp (-π * t) := by
          dsimp [Aβ]
          field_simp [ne_of_gt hsin_pos]
          ring
        exact_mod_cast h1
      set z : ℂ := ((-π * t : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I
      have hexp_z : Complex.exp z = Complex.I * (Real.exp (-π * t) : ℂ) := by
        dsimp [z]
        rw [Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
        simp [mul_comm]
      have hlog_z : Complex.log (Complex.I * (Real.exp (-π * t) : ℂ)) = z := by
        rw [← hexp_z]
        apply Complex.log_exp
        · simp [z]; linarith
        · simp [z]; linarith
      dsimp only [hirschmanStripMap]
      rw [hu, hlog_z]
      dsimp [z]
      push_cast
      field_simp [hpi_ne]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hintegrand : ∀ t : ℝ,
        |φβ' t| • Real.log ‖f (hirschmanStripMap θ (circleMap 0 1 (φβ t)))‖ =
          (2 * π) * (hirschmanBeta θ t * Real.log (‖f (1 + Complex.I * (t : ℂ))‖ ^ θ)) := by
      intro t
      rw [smul_eq_mul, abs_of_pos (hφβ'_pos t), hcomp t]
      have hlog_pow : θ * Real.log ‖f (1 + Complex.I * (t : ℂ))‖ =
          Real.log (‖f (1 + Complex.I * (t : ℂ))‖ ^ θ) := by
        rcases eq_or_lt_of_le (norm_nonneg (f (1 + Complex.I * (t : ℂ)))) with h0 | hpos
        · rw [← h0, Real.log_zero, mul_zero, Real.zero_rpow (ne_of_gt hθ.1), Real.log_zero]
        · exact (Real.log_rpow hpos θ).symm
      dsimp [φβ']
      calc 2 * π * θ * hirschmanBeta θ t * Real.log ‖f (1 + Complex.I * (t : ℂ))‖
          = 2 * π * (hirschmanBeta θ t * (θ * Real.log ‖f (1 + Complex.I * (t : ℂ))‖)) := by ring
        _ = 2 * π * (hirschmanBeta θ t * Real.log (‖f (1 + Complex.I * (t : ℂ))‖ ^ θ)) := by
              rw [hlog_pow]
    set F : ℝ → ℝ := fun φ => Real.log ‖f (hirschmanStripMap θ (circleMap 0 1 φ))‖
    have h_rhs_int : IntegrableOn (fun t : ℝ => |φβ' t| • F (φβ t)) Set.univ volume := by
      rw [integrableOn_univ]
      have heq : (fun t : ℝ => |φβ' t| • F (φβ t)) =
          (fun t : ℝ => (2 * π) * (hirschmanBeta θ t * Real.log (‖f (1 + Complex.I * (t : ℂ))‖ ^ θ))) :=
        funext hintegrand
      rw [heq]
      exact hβ.const_mul (2 * π)
    have h_lhs_int : IntegrableOn F (Set.Ioo 0 (2 * π * θ)) := by
      rw [← himg]
      exact (integrableOn_image_iff_integrableOn_abs_deriv_smul
        MeasurableSet.univ hderiv hinj F).mpr h_rhs_int
    refine ⟨h_lhs_int, ?_⟩
    rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj F,
      setIntegral_univ]
    have heq : (fun t : ℝ => |φβ' t| • F (φβ t)) =
        (fun t : ℝ => (2 * π) * (hirschmanBeta θ t * Real.log (‖f (1 + Complex.I * (t : ℂ))‖ ^ θ))) :=
      funext hintegrand
    rw [heq, integral_const_mul]
  have hirschman_arc_alpha_integral :
      IntegrableOn (fun φ : ℝ => Real.log ‖f (hirschmanStripMap θ (circleMap 0 1 φ))‖)
        (Set.Ioo (2 * π * θ) (2 * π)) ∧
      (∫ φ in Set.Ioo (2 * π * θ) (2 * π), Real.log ‖f (hirschmanStripMap θ (circleMap 0 1 φ))‖) =
        2 * π * ∫ t : ℝ, hirschmanAlpha θ t * Real.log (‖f (I * t)‖ ^ (1 - θ)) := by
    have hpi : 0 < π := Real.pi_pos
    have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpi)
    have h1mθ_pos : 0 < 1 - θ := sub_pos.mpr hθ.2
    have hsin_pos : 0 < Real.sin (π * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hθ.1) (by nlinarith [hθ.2])
    have hθ_in : π / 2 - π * θ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
      constructor <;> nlinarith [hθ.1, hθ.2]
    have htan_cot : Real.tan (π / 2 - π * θ) = Real.cos (π * θ) / Real.sin (π * θ) := by
      rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos (π * θ), inv_div]
    set Aα : ℝ → ℝ := fun t => (Real.cos (π * θ) - Real.exp (-π * t)) / Real.sin (π * θ)
    set φα : ℝ → ℝ := fun t => π - 2 * Real.arctan (Aα t)
    set φα' : ℝ → ℝ := fun t => -(2 * π * (1 - θ) * hirschmanAlpha θ t)
    have hstrict : StrictAnti φα := by
      intro t₁ t₂ ht
      have hexp : Real.exp (-π * t₂) < Real.exp (-π * t₁) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      have hA : Aα t₁ < Aα t₂ :=
        div_lt_div_of_pos_right (by linarith) hsin_pos
      have harc : Real.arctan (Aα t₁) < Real.arctan (Aα t₂) :=
        harctan_mono hA
      dsimp [φα]
      linarith
    have hinj : Set.InjOn φα Set.univ := hstrict.injective.injOn
    have himg : φα '' Set.univ = Set.Ioo (2 * π * θ) (2 * π) := by
      ext φ
      simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ioo]
      constructor
      · rintro ⟨t, rfl⟩
        have h1 : -(π / 2) < Real.arctan (Aα t) := Real.neg_pi_div_two_lt_arctan (Aα t)
        have hA_lt : Aα t < Real.tan (π / 2 - π * θ) := by
          rw [htan_cot]
          exact div_lt_div_of_pos_right (by linarith [Real.exp_pos (-π * t)]) hsin_pos
        have h2 : Real.arctan (Aα t) < π / 2 - π * θ := by
          calc Real.arctan (Aα t) < Real.arctan (Real.tan (π / 2 - π * θ)) :=
                harctan_mono hA_lt
            _ = π / 2 - π * θ := Real.arctan_tan hθ_in.1 hθ_in.2
        dsimp [φα]
        constructor <;> linarith
      · rintro ⟨hφ1, hφ2⟩
        set β : ℝ := (π - φ) / 2
        have hβ_gt : -(π / 2) < β := by dsimp [β]; linarith
        have hβ_lt : β < π / 2 - π * θ := by dsimp [β]; linarith
        have hβ_in : β ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨hβ_gt, lt_trans hβ_lt hθ_in.2⟩
        have htan_lt : Real.tan β < Real.cos (π * θ) / Real.sin (π * θ) := by
          rw [← htan_cot]
          exact Real.strictMonoOn_tan hβ_in hθ_in hβ_lt
        have hy_pos : 0 < Real.cos (π * θ) - Real.tan β * Real.sin (π * θ) := by
          have := (lt_div_iff₀ hsin_pos).mp htan_lt
          linarith
        set y : ℝ := Real.cos (π * θ) - Real.tan β * Real.sin (π * θ)
        refine ⟨-Real.log y / π, ?_⟩
        have hexp_t : Real.exp (-π * (-Real.log y / π)) = y := by
          have : -π * (-Real.log y / π) = Real.log y := by
            field_simp [ne_of_gt hpi]
          rw [this, Real.exp_log hy_pos]
        have hA_eq : Aα (-Real.log y / π) = Real.tan β := by
          dsimp [Aα]
          rw [hexp_t]
          dsimp [y]
          field_simp [ne_of_gt hsin_pos]
          ring
        dsimp [φα]
        rw [hA_eq, Real.arctan_tan hβ_in.1 hβ_in.2]
        dsimp [β]
        ring
    have hdenom_all : ∀ t : ℝ,
        2 * Real.exp (-(π * t)) * (Real.cosh (π * t) - Real.cos (π * θ)) =
          Real.sin (π * θ) ^ 2 + (Real.cos (π * θ) - Real.exp (-(π * t))) ^ 2 ∧
        0 < Real.cosh (π * t) - Real.cos (π * θ) := by
      intro t
      have hexp_inv : Real.exp (-(π * t)) * Real.exp (π * t) = 1 := by
        rw [← Real.exp_add]; simp
      have hsc : Real.sin (π * θ) ^ 2 + Real.cos (π * θ) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq (π * θ)
      have hid : 2 * Real.exp (-(π * t)) * (Real.cosh (π * t) - Real.cos (π * θ)) =
          Real.sin (π * θ) ^ 2 + (Real.cos (π * θ) - Real.exp (-(π * t))) ^ 2 := by
        rw [Real.cosh_eq]
        calc 2 * Real.exp (-(π * t)) * ((Real.exp (π * t) + Real.exp (-(π * t))) / 2 - Real.cos (π * θ))
            = Real.exp (-(π * t)) * Real.exp (π * t) + Real.exp (-(π * t)) ^ 2 -
                2 * Real.exp (-(π * t)) * Real.cos (π * θ) := by ring
          _ = (Real.sin (π * θ) ^ 2 + Real.cos (π * θ) ^ 2) + Real.exp (-(π * t)) ^ 2 -
                2 * Real.exp (-(π * t)) * Real.cos (π * θ) := by rw [hexp_inv, hsc]
          _ = Real.sin (π * θ) ^ 2 + (Real.cos (π * θ) - Real.exp (-(π * t))) ^ 2 := by ring
      have hsq_pos : 0 < Real.sin (π * θ) ^ 2 + (Real.cos (π * θ) - Real.exp (-(π * t))) ^ 2 := by
        positivity
      have h2e_pos : 0 < 2 * Real.exp (-(π * t)) := by positivity
      exact ⟨hid, by nlinarith⟩
    have hderiv : ∀ t ∈ (Set.univ : Set ℝ), HasDerivWithinAt φα (φα' t) Set.univ t := by
      intro t _
      have hd1 : HasDerivAt (fun s : ℝ => -π * s) (-π) t := by
        simpa using (hasDerivAt_id t).const_mul (-π)
      have hd2 : HasDerivAt (fun s : ℝ => Real.exp (-π * s)) (Real.exp (-π * t) * (-π)) t :=
        (Real.hasDerivAt_exp (-π * t)).comp t hd1
      have hd3 : HasDerivAt Aα ((0 - Real.exp (-π * t) * (-π)) / Real.sin (π * θ)) t :=
        ((hasDerivAt_const t (Real.cos (π * θ))).sub hd2).div_const (Real.sin (π * θ))
      have hd4 : HasDerivAt (fun s => Real.arctan (Aα s))
          ((1 / (1 + Aα t ^ 2)) * ((0 - Real.exp (-π * t) * (-π)) / Real.sin (π * θ))) t :=
        (Real.hasDerivAt_arctan (Aα t)).comp t hd3
      have hd5 : HasDerivAt φα
          (0 - 2 * ((1 / (1 + Aα t ^ 2)) * ((0 - Real.exp (-π * t) * (-π)) / Real.sin (π * θ)))) t :=
        (hasDerivAt_const t π).sub (hd4.const_mul 2)
      have hval_eq :
          0 - 2 * ((1 / (1 + Aα t ^ 2)) * ((0 - Real.exp (-π * t) * (-π)) / Real.sin (π * θ))) =
            φα' t := by
        dsimp [φα', hirschmanAlpha, Aα]
        have h1mθ_ne : 1 - θ ≠ 0 := ne_of_gt h1mθ_pos
        have hsin_ne : Real.sin (π * θ) ≠ 0 := ne_of_gt hsin_pos
        have hcosh_ne : Real.cosh (π * t) - Real.cos (π * θ) ≠ 0 := ne_of_gt (hdenom_all t).2
        have h1A_ne : 1 + ((Real.cos (π * θ) - Real.exp (-π * t)) / Real.sin (π * θ)) ^ 2 ≠ 0 := by
          positivity
        field_simp [h1mθ_ne, hsin_ne, hcosh_ne, h1A_ne]
        rw [← (hdenom_all t).1]
        ring
      rw [← hval_eq]
      exact hd5.hasDerivWithinAt
    have hφα'_abs : ∀ t : ℝ, |φα' t| = 2 * π * (1 - θ) * hirschmanAlpha θ t := by
      intro t
      have hpos : 0 < 2 * π * (1 - θ) * hirschmanAlpha θ t := by
        dsimp [hirschmanAlpha]
        have hcosh_pos := (hdenom_all t).2
        positivity
      dsimp [φα']
      rw [abs_neg, abs_of_pos hpos]
    have hcomp : ∀ t : ℝ, hirschmanStripMap θ (circleMap 0 1 (φα t)) = Complex.I * (t : ℂ) := by
      intro t
      have hw : circleMap 0 1 (φα t) =
          (Complex.I * (Aα t : ℂ) - 1) / (Complex.I * (Aα t : ℂ) + 1) :=
        cayley_circleMap_arctan (Aα t)
      have hu : hirschmanHalfPlane θ (circleMap 0 1 (φα t)) =
          -Complex.I * (Real.exp (-π * t) : ℂ) := by
        rw [hw, hirschmanHalfPlane_cayley]
        have h1 : Aα t * Real.sin (π * θ) - Real.cos (π * θ) = -Real.exp (-π * t) := by
          dsimp [Aα]
          field_simp [ne_of_gt hsin_pos]
          ring
        rw [h1, Complex.ofReal_neg]
        ring
      set z : ℂ := ((-π * t : ℝ) : ℂ) + ((-(π / 2) : ℝ) : ℂ) * Complex.I
      have hexp_z : Complex.exp z = -Complex.I * (Real.exp (-π * t) : ℂ) := by
        dsimp [z]
        rw [Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
          Real.cos_pi_div_two, Real.sin_pi_div_two]
        simp [mul_comm]
      have hlog_z : Complex.log (-Complex.I * (Real.exp (-π * t) : ℂ)) = z := by
        rw [← hexp_z]
        apply Complex.log_exp
        · simp [z]; linarith
        · simp [z]; linarith
      dsimp only [hirschmanStripMap]
      rw [hu, hlog_z]
      dsimp [z]
      push_cast
      field_simp [hpi_ne]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hintegrand : ∀ t : ℝ,
        |φα' t| • Real.log ‖f (hirschmanStripMap θ (circleMap 0 1 (φα t)))‖ =
          (2 * π) * (hirschmanAlpha θ t * Real.log (‖f (Complex.I * (t : ℂ))‖ ^ (1 - θ))) := by
      intro t
      rw [smul_eq_mul, hφα'_abs t, hcomp t]
      have hlog_pow : (1 - θ) * Real.log ‖f (Complex.I * (t : ℂ))‖ =
          Real.log (‖f (Complex.I * (t : ℂ))‖ ^ (1 - θ)) := by
        rcases eq_or_lt_of_le (norm_nonneg (f (Complex.I * (t : ℂ)))) with h0 | hpos
        · rw [← h0, Real.log_zero, mul_zero, Real.zero_rpow (ne_of_gt h1mθ_pos), Real.log_zero]
        · exact (Real.log_rpow hpos (1 - θ)).symm
      calc 2 * π * (1 - θ) * hirschmanAlpha θ t * Real.log ‖f (Complex.I * (t : ℂ))‖
          = 2 * π * (hirschmanAlpha θ t * ((1 - θ) * Real.log ‖f (Complex.I * (t : ℂ))‖)) := by ring
        _ = 2 * π * (hirschmanAlpha θ t * Real.log (‖f (Complex.I * (t : ℂ))‖ ^ (1 - θ))) := by
              rw [hlog_pow]
    set F : ℝ → ℝ := fun φ => Real.log ‖f (hirschmanStripMap θ (circleMap 0 1 φ))‖
    have h_rhs_int : IntegrableOn (fun t : ℝ => |φα' t| • F (φα t)) Set.univ volume := by
      rw [integrableOn_univ]
      have heq : (fun t : ℝ => |φα' t| • F (φα t)) =
          (fun t : ℝ => (2 * π) * (hirschmanAlpha θ t * Real.log (‖f (Complex.I * (t : ℂ))‖ ^ (1 - θ)))) :=
        funext hintegrand
      rw [heq]
      exact hα.const_mul (2 * π)
    have h_lhs_int : IntegrableOn F (Set.Ioo (2 * π * θ) (2 * π)) := by
      rw [← himg]
      exact (integrableOn_image_iff_integrableOn_abs_deriv_smul
        MeasurableSet.univ hderiv hinj F).mpr h_rhs_int
    refine ⟨h_lhs_int, ?_⟩
    rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj F,
      setIntegral_univ]
    have heq : (fun t : ℝ => |φα' t| • F (φα t)) =
        (fun t : ℝ => (2 * π) * (hirschmanAlpha θ t * Real.log (‖f (Complex.I * (t : ℂ))‖ ^ (1 - θ)))) :=
      funext hintegrand
    rw [heq, integral_const_mul]
  have hpi : 0 < π := Real.pi_pos
  have h2pi_ne : 2 * π ≠ 0 := ne_of_gt (by positivity)
  have hcl_eq : closure (verticalStrip 0 1) = verticalClosedStrip 0 1 := by
    show closure (Complex.re ⁻¹' Set.Ioo 0 1) = Complex.re ⁻¹' Set.Icc 0 1
    rw [Complex.closure_preimage_re, closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
  have hf_diff : DifferentiableOn ℂ f (verticalStrip 0 1) := hd.differentiableOn
  have hf_cont : ContinuousOn f (verticalClosedStrip 0 1) := hcl_eq ▸ hd.continuousOn
  obtain ⟨hΦ0, hΦ_maps, hΦ_diff, hΦ_bdry⟩ := hirschmanStripMap_disc_props
  obtain ⟨hint_β, heval_β⟩ := hirschman_arc_beta_integral
  obtain ⟨hint_α, heval_α⟩ := hirschman_arc_alpha_integral
  set g : ℂ → ℂ := f ∘ hirschmanStripMap θ
  have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) :=
    hf_diff.comp hΦ_diff hΦ_maps
  have hg_bdd : BddAbove ((norm ∘ g) '' Metric.ball (0 : ℂ) 1) := by
    apply hb.mono
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨hirschmanStripMap θ w, ?_, rfl⟩
    have hmem := hΦ_maps hw
    exact ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
  have hg0 : g 0 ≠ 0 := by
    show f (hirschmanStripMap θ 0) ≠ 0
    rwa [hΦ0]
  set I₁ : Set ℝ := Set.Ioo 0 (2 * π * θ)
  set I₂ : Set ℝ := Set.Ioo (2 * π * θ) (2 * π)
  set N : Set ℝ := {2 * π * θ, 2 * π}
  have hN_zero : volume N = 0 := N.toFinite.measure_zero volume
  have hdisj : Disjoint I₁ I₂ := by
    rw [Set.disjoint_iff]
    rintro φ ⟨h1, h2⟩
    exact lt_asymm h1.2 h2.1
  have hae_set : (I₁ ∪ I₂ : Set ℝ) =ᵐ[volume] Set.Ioc (0 : ℝ) (2 * π) := by
    have hae_not_N : ∀ᵐ φ : ℝ ∂volume, φ ∉ N :=
      compl_mem_ae_iff.mpr hN_zero
    filter_upwards [hae_not_N] with φ hφN
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, N, not_or] at hφN
    apply propext
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ioc, I₁, I₂]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_of_lt (lt_trans h2 (by nlinarith [hθ.2]))⟩
      · exact ⟨lt_trans (by nlinarith [hθ.1]) h1, le_of_lt h2⟩
    · rintro ⟨h1, h2⟩
      have hlt2pi : φ < 2 * π := lt_of_le_of_ne h2 hφN.2
      rcases lt_trichotomy φ (2 * π * θ) with hlt | heq | hgt
      · exact Or.inl ⟨h1, hlt⟩
      · exact absurd heq hφN.1
      · exact Or.inr ⟨hgt, hlt2pi⟩
  set F : ℝ → ℝ := fun φ => Real.log ‖g (circleMap 0 1 φ)‖
  have hint_union : IntegrableOn F (I₁ ∪ I₂) := hint_β.union hint_α
  have hint_Ioc : IntegrableOn F (Set.Ioc (0 : ℝ) (2 * π)) :=
    (integrableOn_congr_set_ae hae_set).mp hint_union
  have heval_Ioc : ∫ φ in Set.Ioc (0 : ℝ) (2 * π), F φ =
      2 * π * ∫ t : ℝ, (hirschmanAlpha θ t * Real.log (‖f (I * t)‖ ^ (1 - θ))
        + hirschmanBeta θ t * Real.log (‖f (1 + I * t)‖ ^ θ)) := by
    rw [← setIntegral_congr_set hae_set]
    dsimp only [F, g, Function.comp_apply]
    rw [setIntegral_union hdisj measurableSet_Ioo hint_β hint_α,
      heval_β, heval_α, integral_add hα hβ]
    ring
  have hrad : ∀ᵐ φ ∂(volume.restrict (Set.Ioc (0 : ℝ) (2 * π))),
      Filter.Tendsto (fun n : ℕ => g (circleMap 0 (1 - 1 / ((n : ℝ) + 2)) φ))
        Filter.atTop (nhds (g (circleMap 0 1 φ))) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hae_not_N : ∀ᵐ φ : ℝ ∂volume, φ ∉ N :=
      compl_mem_ae_iff.mpr hN_zero
    filter_upwards [hae_not_N] with φ hφN hφ_Ioc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, N, not_or] at hφN
    have hφ_Ioo : φ ∈ Set.Ioo (0 : ℝ) (2 * π) :=
      ⟨hφ_Ioc.1, lt_of_le_of_ne hφ_Ioc.2 hφN.2⟩
    obtain ⟨hbdry_mem, hbdry_cont⟩ := hΦ_bdry φ hφ_Ioo hφN.1
    have hr_tend : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 1) := by
      have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 0) :=
        (h1.comp (Filter.tendsto_add_atTop_nat 1)).congr (fun n => by dsimp; push_cast; ring_nf)
      simpa using tendsto_const_nhds.sub h0
    have hcm_tend : Filter.Tendsto (fun n : ℕ => circleMap (0 : ℂ) (1 - 1 / ((n : ℝ) + 2)) φ)
        Filter.atTop (nhds (circleMap 0 1 φ)) := by
      have hcont_r : Continuous (fun r : ℝ => circleMap (0 : ℂ) r φ) := by
        unfold circleMap
        fun_prop
      exact hcont_r.continuousAt.tendsto.comp hr_tend
    have hΦ_tend : Filter.Tendsto (fun n : ℕ => hirschmanStripMap θ (circleMap 0 (1 - 1 / ((n : ℝ) + 2)) φ))
        Filter.atTop (nhds (hirschmanStripMap θ (circleMap 0 1 φ))) :=
      hbdry_cont.tendsto.comp hcm_tend
    have hΦ_mem_each : ∀ n : ℕ,
        hirschmanStripMap θ (circleMap 0 (1 - 1 / ((n : ℝ) + 2)) φ) ∈ verticalClosedStrip 0 1 := by
      intro n
      have hr_pos : 0 < (1 : ℝ) - 1 / ((n : ℝ) + 2) := by
        have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        have hdiv : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one (by linarith)).mpr hn2
        linarith
      have hr_lt1 : (1 : ℝ) - 1 / ((n : ℝ) + 2) < 1 := by
        have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        linarith [one_div_pos.mpr hn2]
      have hball : circleMap (0 : ℂ) (1 - 1 / ((n : ℝ) + 2)) φ ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hr_pos]
        exact hr_lt1
      have hmem := hΦ_maps hball
      exact ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
    have hnhdsW : Filter.Tendsto (fun n : ℕ => hirschmanStripMap θ (circleMap 0 (1 - 1 / ((n : ℝ) + 2)) φ))
        Filter.atTop (nhdsWithin (hirschmanStripMap θ (circleMap 0 1 φ)) (verticalClosedStrip 0 1)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hΦ_tend
        (Filter.Eventually.of_forall hΦ_mem_each)
    exact (hf_cont _ hbdry_mem).tendsto.comp hnhdsW
  have hmain := disc_log_norm_le_boundary_integral g hg_diff hg_bdd hg0 hrad hint_Ioc
  have hg0_eq : Real.log ‖g 0‖ = Real.log ‖f θ‖ := by
    show Real.log ‖f (hirschmanStripMap θ 0)‖ = Real.log ‖f θ‖
    rw [hΦ0]
  rw [hg0_eq, heval_Ioc, ← mul_assoc, inv_mul_cancel₀ h2pi_ne, one_mul] at hmain
  exact hmain

end Leap
