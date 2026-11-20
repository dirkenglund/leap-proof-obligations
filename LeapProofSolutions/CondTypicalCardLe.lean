import LeapProofObligations.Definitions

open scoped BigOperators

namespace Leap

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Wilde Property 15.2.7: size of the conditionally typical set. -/
theorem condTypical_card_le (W : α → β → ℝ) (hW : ∀ a b, 0 ≤ W a b) (hW1 : ∀ a, ∑ b, W a b = 1) :
    ∃ c : ℝ, ∀ δ > 0, ∀ (k : ℕ) (x : Fin k → α),
      ((condTypical W δ x).card : ℝ) ≤
        Real.exp (k * (∑ a, (count x a : ℝ) / k * entropy (W a) + c * δ)) := by
  refine ⟨-∑ a : α, ∑ b : β, Real.log (W a b), fun δ _hδ k x => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hcard_nat : (condTypical W δ x).card ≤ 1 := by
      calc (condTypical W δ x).card
        _ ≤ Fintype.card (Fin 0 → β) := Finset.card_le_univ _
        _ = (Fintype.card β) ^ (Fintype.card (Fin 0)) := Fintype.card_fun
        _ = (Fintype.card β) ^ 0 := by simp
        _ = 1 := pow_zero _
    have hcard : ((condTypical W δ x).card : ℝ) ≤ 1 := by exact_mod_cast hcard_nat
    simpa using hcard
  · let c : ℝ := -∑ a : α, ∑ b : β, Real.log (W a b)
    let E : ℝ := (k : ℝ) * (∑ a : α, (count x a : ℝ) / k * entropy (W a) + c * δ)
    let T : Finset (Fin k → β) := condTypical W δ x
    change (T.card : ℝ) ≤ Real.exp E
    have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
    have hprob_le_one : ∑ y ∈ T, (∏ i : Fin k, W (x i) (y i)) ≤ 1 := by
      calc ∑ y ∈ T, (∏ i : Fin k, W (x i) (y i))
        _ ≤ ∑ y : Fin k → β, (∏ i : Fin k, W (x i) (y i)) := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro y
          exact Finset.prod_nonneg (fun i _ => hW (x i) (y i))
        _ = ∏ i : Fin k, ∑ b : β, W (x i) b := by
          exact (Fintype.prod_sum (fun (i : Fin k) (b : β) => W (x i) b)).symm
        _ = ∏ _i : Fin k, (1 : ℝ) := by
          refine Finset.prod_congr rfl (fun i _ => hW1 (x i))
        _ = 1 := Finset.prod_const_one
    have hpointwise : ∀ y ∈ T, Real.exp (-E) ≤ ∏ i : Fin k, W (x i) (y i) := by
      intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      have hdev : ∀ a b, |(pairCount x y a b : ℝ) / k - W a b * (count x a : ℝ) / k| ≤ δ :=
        fun a b => (hy' a b).1
      have hy0 : ∀ a b, W a b = 0 → pairCount x y a b = 0 :=
        fun a b => (hy' a b).2
      have hprod_eq : (∏ i : Fin k, W (x i) (y i)) =
          Real.exp (∑ a : α, ∑ b : β, (pairCount x y a b : ℝ) * Real.log (W a b)) := by
        have hfib := (Finset.prod_fiberwise' (Finset.univ : Finset (Fin k))
          (fun i : Fin k => (x i, y i)) (fun p : α × β => W p.1 p.2)).symm
        rw [hfib, Fintype.prod_prod_type]
        have hinner : ∀ (a : α) (b : β),
            (∏ i ∈ Finset.univ.filter (fun i : Fin k => (x i, y i) = (a, b)), W a b) =
              Real.exp ((pairCount x y a b : ℝ) * Real.log (W a b)) := by
          intro a b
          have hfilt : Finset.univ.filter (fun i : Fin k => (x i, y i) = (a, b)) =
              Finset.univ.filter (fun i : Fin k => x i = a ∧ y i = b) := by
            ext i
            simp [Prod.mk.injEq]
          rw [hfilt, Finset.prod_const]
          change (W a b) ^ (pairCount x y a b) = Real.exp ((pairCount x y a b : ℝ) * Real.log (W a b))
          by_cases hw0 : W a b = 0
          · have hpc0 : pairCount x y a b = 0 := hy0 a b hw0
            simp [hw0, hpc0]
          · have hw_pos : 0 < W a b := lt_of_le_of_ne (hW a b) (Ne.symm hw0)
            rw [Real.exp_nat_mul, Real.exp_log hw_pos]
        simp_rw [hinner]
        simp_rw [← Real.exp_sum]
      have hlog_ge : -E ≤ ∑ a : α, ∑ b : β, (pairCount x y a b : ℝ) * Real.log (W a b) := by
        have hterm_le : ∀ (a : α) (b : β),
            (W a b * (count x a : ℝ) + (k : ℝ) * δ) * Real.log (W a b) ≤
              (pairCount x y a b : ℝ) * Real.log (W a b) := by
          intro a b
          have hw_le_one : W a b ≤ 1 := by
            calc W a b
              _ ≤ ∑ b' : β, W a b' :=
                Finset.single_le_sum (fun b' _ => hW a b') (Finset.mem_univ b)
              _ = 1 := hW1 a
          have hlog_nonpos : Real.log (W a b) ≤ 0 := Real.log_nonpos (hW a b) hw_le_one
          have hdev_upper : (pairCount x y a b : ℝ) / k - W a b * (count x a : ℝ) / k ≤ δ :=
            (abs_le.mp (hdev a b)).2
          have hpc_le : (pairCount x y a b : ℝ) ≤ W a b * (count x a : ℝ) + (k : ℝ) * δ := by
            rw [← sub_div, div_le_iff₀ hk_pos] at hdev_upper
            linarith
          exact mul_le_mul_of_nonpos_right hpc_le hlog_nonpos
        have hsum_le :
            ∑ a : α, ∑ b : β, (W a b * (count x a : ℝ) + (k : ℝ) * δ) * Real.log (W a b) ≤
              ∑ a : α, ∑ b : β, (pairCount x y a b : ℝ) * Real.log (W a b) := by
          refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hterm_le a b))
        have hE_eq : -E =
            ∑ a : α, ∑ b : β, (W a b * (count x a : ℝ) + (k : ℝ) * δ) * Real.log (W a b) := by
          have hpart1 : -(k : ℝ) * (∑ a : α, (count x a : ℝ) / k * entropy (W a)) =
              ∑ a : α, ∑ b : β, (count x a : ℝ) * (W a b * Real.log (W a b)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            dsimp [entropy]
            have hcancel : -(k : ℝ) * ((count x a : ℝ) / k * -∑ b : β, W a b * Real.log (W a b)) =
                (count x a : ℝ) * ∑ b : β, W a b * Real.log (W a b) := by
              field_simp [hk_ne]
            rw [hcancel, Finset.mul_sum]
          have hpart2 : -(k : ℝ) * (c * δ) =
              ∑ a : α, ∑ b : β, ((k : ℝ) * δ) * Real.log (W a b) := by
            dsimp [c]
            have hscalar : -(k : ℝ) * ((-∑ a : α, ∑ b : β, Real.log (W a b)) * δ) =
                ((k : ℝ) * δ) * ∑ a : α, ∑ b : β, Real.log (W a b) := by ring
            rw [hscalar, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Finset.mul_sum]
          have hsplit : -E =
              -(k : ℝ) * (∑ a : α, (count x a : ℝ) / k * entropy (W a)) + -(k : ℝ) * (c * δ) := by
            dsimp [E]
            ring
          rw [hsplit, hpart1, hpart2, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          ring
        linarith [hsum_le, hE_eq]
      rw [hprod_eq]
      exact Real.exp_le_exp.mpr hlog_ge
    have hcard_mul : (T.card : ℝ) * Real.exp (-E) ≤ 1 := by
      calc (T.card : ℝ) * Real.exp (-E)
        _ = ∑ _y ∈ T, Real.exp (-E) := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ y ∈ T, (∏ i : Fin k, W (x i) (y i)) := Finset.sum_le_sum hpointwise
        _ ≤ 1 := hprob_le_one
    calc (T.card : ℝ)
      _ = (T.card : ℝ) * (Real.exp (-E) * Real.exp E) := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ = ((T.card : ℝ) * Real.exp (-E)) * Real.exp E := (mul_assoc _ _ _).symm
      _ ≤ 1 * Real.exp E :=
        mul_le_mul_of_nonneg_right hcard_mul (Real.exp_pos E).le
      _ = Real.exp E := one_mul _

end Leap
