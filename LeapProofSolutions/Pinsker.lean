import LeapProofObligations.Definitions

open scoped BigOperators

namespace Leap

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Wilde Thm / Lemma 10.8.1: classical Pinsker inequality, in nats. -/
theorem pinsker (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) (hac : ∀ a, q a = 0 → p a = 0) :
    (∑ a, |p a - q a|) ^ 2 / 2 ≤ ∑ a, p a * Real.log (p a / q a) := by
  classical
  let A : Finset α := Finset.univ.filter (fun a => q a ≤ p a)
  set P : ℝ := ∑ a ∈ A, p a with hP_def
  set Q : ℝ := ∑ a ∈ A, q a with hQ_def
  have hP_compl : ∑ a ∈ Aᶜ, p a = 1 - P := by
    have h := Finset.sum_add_sum_compl A p
    linarith [hps]
  have hQ_compl : ∑ a ∈ Aᶜ, q a = 1 - Q := by
    have h := Finset.sum_add_sum_compl A q
    linarith [hqs]
  have hl1 : ∑ a, |p a - q a| = 2 * (P - Q) := by
    have hsplit := Finset.sum_add_sum_compl A (fun a => |p a - q a|)
    have hs1 : ∑ a ∈ A, |p a - q a| = P - Q := by
      calc ∑ a ∈ A, |p a - q a|
          = ∑ a ∈ A, (p a - q a) := by
            refine Finset.sum_congr rfl (fun a ha => ?_)
            have hqp : q a ≤ p a := (Finset.mem_filter.mp ha).2
            exact abs_of_nonneg (sub_nonneg.mpr hqp)
        _ = P - Q := by rw [Finset.sum_sub_distrib, hP_def, hQ_def]
    have hs2 : ∑ a ∈ Aᶜ, |p a - q a| = (1 - Q) - (1 - P) := by
      calc ∑ a ∈ Aᶜ, |p a - q a|
          = ∑ a ∈ Aᶜ, (q a - p a) := by
            refine Finset.sum_congr rfl (fun a ha => ?_)
            have hnot : a ∉ A := Finset.mem_compl.mp ha
            have hpq : p a ≤ q a := by
              by_contra hlt
              exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ a, by linarith⟩)
            rw [abs_of_nonpos (sub_nonpos.mpr hpq)]
            ring
        _ = (1 - Q) - (1 - P) := by rw [Finset.sum_sub_distrib, hQ_compl, hP_compl]
    linarith
  have hlhs : (∑ a, |p a - q a|) ^ 2 / 2 = 2 * (P - Q) ^ 2 := by
    rw [hl1]
    ring
  have hlog_sum : ∀ (s : Finset α),
      (∑ a ∈ s, p a) * Real.log ((∑ a ∈ s, p a) / (∑ a ∈ s, q a)) ≤
        ∑ a ∈ s, p a * Real.log (p a / q a) := by
    intro s
    set Ps : ℝ := ∑ a ∈ s, p a with hPs_def
    set Qs : ℝ := ∑ a ∈ s, q a with hQs_def
    have hPs_nonneg : 0 ≤ Ps := Finset.sum_nonneg (fun a _ => hp a)
    have hQs_nonneg : 0 ≤ Qs := Finset.sum_nonneg (fun a _ => hq a)
    rcases eq_or_lt_of_le hPs_nonneg with hPs0 | hPs_pos
    · have hp_zero : ∀ a ∈ s, p a = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hp a)).mp hPs0.symm
      rw [← hPs0, zero_mul]
      have hrhs0 : ∑ a ∈ s, p a * Real.log (p a / q a) = 0 :=
        Finset.sum_eq_zero (fun a ha => by rw [hp_zero a ha, zero_mul])
      rw [hrhs0]
    · have hQs_ne : Qs ≠ 0 := by
        intro hQs0
        have hq_zero : ∀ a ∈ s, q a = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hq a)).mp hQs0
        have hp_zero : ∀ a ∈ s, p a = 0 := fun a ha => hac a (hq_zero a ha)
        have : Ps = 0 := Finset.sum_eq_zero hp_zero
        linarith
      have hQs_pos : 0 < Qs := lt_of_le_of_ne hQs_nonneg (Ne.symm hQs_ne)
      let sp : Finset α := s.filter (fun a => 0 < p a)
      have hsp_sub : sp ⊆ s := Finset.filter_subset _ s
      have hPs_sp : ∑ a ∈ sp, p a = Ps := by
        refine Finset.sum_subset hsp_sub (fun a ha hnot => ?_)
        have hnp : ¬ 0 < p a := by
          intro hpos
          exact hnot (Finset.mem_filter.mpr ⟨ha, hpos⟩)
        linarith [hp a]
      have hrhs_sp : ∑ a ∈ sp, p a * Real.log (p a / q a) =
          ∑ a ∈ s, p a * Real.log (p a / q a) := by
        refine Finset.sum_subset hsp_sub (fun a ha hnot => ?_)
        have hnp : ¬ 0 < p a := by
          intro hpos
          exact hnot (Finset.mem_filter.mpr ⟨ha, hpos⟩)
        have hp0 : p a = 0 := by linarith [hp a]
        rw [hp0, zero_mul]
      have hpt : ∀ a ∈ sp,
          p a * Real.log (Ps / Qs) - (Ps / Qs) * q a + p a ≤
            p a * Real.log (p a / q a) := by
        intro a ha
        have hpa_pos : 0 < p a := (Finset.mem_filter.mp ha).2
        have hpa_ne : p a ≠ 0 := ne_of_gt hpa_pos
        have hqa_ne : q a ≠ 0 := fun hq0 => hpa_ne (hac a hq0)
        have hqa_pos : 0 < q a := lt_of_le_of_ne (hq a) (Ne.symm hqa_ne)
        have hPsQs_pos : 0 < Ps / Qs := div_pos hPs_pos hQs_pos
        have hpq_pos : 0 < p a / q a := div_pos hpa_pos hqa_pos
        have hratio_pos : 0 < (Ps / Qs) / (p a / q a) := div_pos hPsQs_pos hpq_pos
        have hlog_eq : Real.log ((Ps / Qs) / (p a / q a)) =
            Real.log (Ps / Qs) - Real.log (p a / q a) :=
          Real.log_div (ne_of_gt hPsQs_pos) (ne_of_gt hpq_pos)
        have htan : Real.log ((Ps / Qs) / (p a / q a)) ≤
            (Ps / Qs) / (p a / q a) - 1 :=
          Real.log_le_sub_one_of_pos hratio_pos
        have hmul : p a * (Real.log (Ps / Qs) - Real.log (p a / q a)) ≤
            p a * ((Ps / Qs) / (p a / q a) - 1) := by
          rw [← hlog_eq]
          exact mul_le_mul_of_nonneg_left htan (le_of_lt hpa_pos)
        have halg : p a * ((Ps / Qs) / (p a / q a) - 1) = (Ps / Qs) * q a - p a := by
          field_simp [hpa_ne, hqa_ne, hQs_ne]
        linarith
      have hsum_pt := Finset.sum_le_sum hpt
      have hsum_lhs : ∑ a ∈ sp, (p a * Real.log (Ps / Qs) - (Ps / Qs) * q a + p a) =
          Ps * Real.log (Ps / Qs) - (Ps / Qs) * (∑ a ∈ sp, q a) + Ps := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
          ← Finset.mul_sum, hPs_sp]
      have hq_sub : ∑ a ∈ sp, q a ≤ Qs :=
        Finset.sum_le_sum_of_subset_of_nonneg hsp_sub (fun a _ _ => hq a)
      have hq_mul : (Ps / Qs) * (∑ a ∈ sp, q a) ≤ Ps := by
        calc (Ps / Qs) * (∑ a ∈ sp, q a)
            ≤ (Ps / Qs) * Qs :=
              mul_le_mul_of_nonneg_left hq_sub (div_nonneg hPs_nonneg hQs_nonneg)
          _ = Ps := div_mul_cancel₀ Ps hQs_ne
      linarith [hrhs_sp]
  have hkl_A : P * Real.log (P / Q) ≤ ∑ a ∈ A, p a * Real.log (p a / q a) :=
    hlog_sum A
  have hkl_Ac : (1 - P) * Real.log ((1 - P) / (1 - Q)) ≤
      ∑ a ∈ Aᶜ, p a * Real.log (p a / q a) := by
    have h := hlog_sum Aᶜ
    rwa [hP_compl, hQ_compl] at h
  have hkl_coarse : P * Real.log (P / Q) + (1 - P) * Real.log ((1 - P) / (1 - Q)) ≤
      ∑ a, p a * Real.log (p a / q a) := by
    have hsplit := Finset.sum_add_sum_compl A (fun a => p a * Real.log (p a / q a))
    linarith
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun a _ => hq a)
  have hQP : Q ≤ P :=
    Finset.sum_le_sum (fun a ha => (Finset.mem_filter.mp ha).2)
  have hP1 : P ≤ 1 := by
    have hAc_nonneg : 0 ≤ ∑ a ∈ Aᶜ, p a := Finset.sum_nonneg (fun a _ => hp a)
    linarith [hP_compl]
  have hQ0P0 : Q = 0 → P = 0 := by
    intro hQ_zero
    have hq_zero : ∀ a ∈ A, q a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hq a)).mp hQ_zero
    exact Finset.sum_eq_zero (fun a ha => hac a (hq_zero a ha))
  have hmul_log_self : ∀ x : ℝ, x * Real.log (x / x) = 0 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [div_self hx]
  have hbin : 2 * (P - Q) ^ 2 ≤
      P * Real.log (P / Q) + (1 - P) * Real.log ((1 - P) / (1 - Q)) := by
    rcases eq_or_lt_of_le hQ0 with hQ_eq0 | hQ_pos
    · have hP_eq0 : P = 0 := hQ0P0 hQ_eq0.symm
      rw [← hQ_eq0, hP_eq0]
      simp
    · rcases eq_or_lt_of_le hQP with hQ_eqP | hQ_ltP
      · rw [hQ_eqP, hmul_log_self P, hmul_log_self (1 - P)]
        norm_num
      · rcases eq_or_lt_of_le hP1 with hP_eq1 | hP_lt1
        · rw [hP_eq1]
          have hgoal_simp : 1 * Real.log (1 / Q) + (1 - 1) * Real.log ((1 - 1) / (1 - Q)) =
              -Real.log Q := by
            simp [one_div, Real.log_inv]
          rw [hgoal_simp]
          let f : ℝ → ℝ := fun x => -Real.log x - 2 * (1 - x) ^ 2
          let f' : ℝ → ℝ := fun x => -x⁻¹ + 4 * (1 - x)
          have hderiv : ∀ x ∈ Set.Icc Q 1, HasDerivAt f (f' x) x := by
            intro x hx
            have hx_pos : 0 < x := lt_of_lt_of_le hQ_pos hx.1
            have hx_ne : x ≠ 0 := ne_of_gt hx_pos
            have hd1 : HasDerivAt (fun y => -Real.log y) (-x⁻¹) x :=
              (Real.hasDerivAt_log hx_ne).neg
            have hd2 : HasDerivAt (fun y => 2 * (1 - y) ^ 2)
                (2 * (2 * (1 - x) ^ 1 * (0 - 1))) x :=
              (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow 2).const_mul 2
            convert hd1.sub hd2 using 1
            ring
          have hcont : ContinuousOn f (Set.Icc Q 1) :=
            fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
          have hnonpos : ∀ x ∈ Set.Icc Q 1, f' x ≤ 0 := by
            intro x hx
            have hx_pos : 0 < x := lt_of_lt_of_le hQ_pos hx.1
            have hx_ne : x ≠ 0 := ne_of_gt hx_pos
            have hfac : f' x = -((2 * x - 1) ^ 2) / x := by
              dsimp [f']
              field_simp [hx_ne]
              try ring
            rw [hfac]
            exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (le_of_lt hx_pos)
          have hanti : AntitoneOn f (Set.Icc Q 1) :=
            antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc Q 1) hcont
              (fun x hx => (hderiv x (interior_subset hx)).hasDerivWithinAt)
              (fun x hx => hnonpos x (interior_subset hx))
          have hQ1 : Q ≤ 1 := by linarith
          have hf_le : f 1 ≤ f Q :=
            hanti ⟨le_rfl, hQ1⟩ ⟨hQ1, le_rfl⟩ hQ1
          have hf1 : f 1 = 0 := by simp [f]
          dsimp [f] at hf_le
          linarith
        · let g : ℝ → ℝ := fun x =>
            P * Real.log P + (1 - P) * Real.log (1 - P) -
              P * Real.log x - (1 - P) * Real.log (1 - x) - 2 * (P - x) ^ 2
          let g' : ℝ → ℝ := fun x => -P * x⁻¹ + (1 - P) * (1 - x)⁻¹ + 4 * (P - x)
          have hderiv : ∀ x ∈ Set.Icc Q P, HasDerivAt g (g' x) x := by
            intro x hx
            have hx_pos : 0 < x := lt_of_lt_of_le hQ_pos hx.1
            have hx_ne : x ≠ 0 := ne_of_gt hx_pos
            have h1x_pos : 0 < 1 - x := by linarith [hx.2]
            have h1x_ne : 1 - x ≠ 0 := ne_of_gt h1x_pos
            have hd0 : HasDerivAt (fun _ : ℝ => P * Real.log P + (1 - P) * Real.log (1 - P)) 0 x :=
              hasDerivAt_const x _
            have hd1 : HasDerivAt (fun y => P * Real.log y) (P * x⁻¹) x :=
              (Real.hasDerivAt_log hx_ne).const_mul P
            have hd2 : HasDerivAt (fun y => (1 - P) * Real.log (1 - y))
                ((1 - P) * ((0 - 1) / (1 - x))) x :=
              (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log h1x_ne).const_mul (1 - P)
            have hd3 : HasDerivAt (fun y => 2 * (P - y) ^ 2)
                (2 * (2 * (P - x) ^ 1 * (0 - 1))) x :=
              (((hasDerivAt_const x P).sub (hasDerivAt_id x)).pow 2).const_mul 2
            convert ((hd0.sub hd1).sub hd2).sub hd3 using 1
            dsimp [g']
            field_simp [hx_ne, h1x_ne]
            try ring
          have hcont : ContinuousOn g (Set.Icc Q P) :=
            fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
          have hnonpos : ∀ x ∈ Set.Icc Q P, g' x ≤ 0 := by
            intro x hx
            have hx_pos : 0 < x := lt_of_lt_of_le hQ_pos hx.1
            have hx_ne : x ≠ 0 := ne_of_gt hx_pos
            have h1x_pos : 0 < 1 - x := by linarith [hx.2]
            have h1x_ne : 1 - x ≠ 0 := ne_of_gt h1x_pos
            have hPx_nonneg : 0 ≤ P - x := sub_nonneg.mpr hx.2
            have hfac : g' x = -((P - x) * (2 * x - 1) ^ 2) / (x * (1 - x)) := by
              dsimp [g']
              field_simp [hx_ne, h1x_ne]
              try ring
            rw [hfac]
            exact div_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr (mul_nonneg hPx_nonneg (sq_nonneg _)))
              (mul_nonneg (le_of_lt hx_pos) (le_of_lt h1x_pos))
          have hanti : AntitoneOn g (Set.Icc Q P) :=
            antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc Q P) hcont
              (fun x hx => (hderiv x (interior_subset hx)).hasDerivWithinAt)
              (fun x hx => hnonpos x (interior_subset hx))
          have hg_le : g P ≤ g Q :=
            hanti ⟨le_rfl, hQP⟩ ⟨hQP, le_rfl⟩ hQP
          have hgP : g P = 0 := by
            dsimp [g]
            ring
          have hP_pos : 0 < P := lt_trans hQ_pos hQ_ltP
          have h1P_pos : 0 < 1 - P := sub_pos.mpr hP_lt1
          have h1Q_pos : 0 < 1 - Q := by linarith
          have hgQ : g Q = P * Real.log (P / Q) + (1 - P) * Real.log ((1 - P) / (1 - Q)) -
              2 * (P - Q) ^ 2 := by
            dsimp [g]
            rw [Real.log_div (ne_of_gt hP_pos) (ne_of_gt hQ_pos),
              Real.log_div (ne_of_gt h1P_pos) (ne_of_gt h1Q_pos)]
            ring
          linarith
  linarith [hlhs, hbin, hkl_coarse]

end Leap
