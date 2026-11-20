import LeapProofObligations.Definitions

open scoped BigOperators
open Filter Topology

namespace Leap

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Wilde Def 15.2.3: strong typicality concentrates. -/
theorem strongTypical_prob_tendsto_one (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => iidProb p (strongTypical p δ k)) atTop (𝓝 1) := by
  have hw_nonneg : ∀ (k : ℕ) (x : Fin k → α), 0 ≤ ∏ i : Fin k, p (x i) := by
    intro k x
    exact Finset.prod_nonneg (fun i _ => hp (x i))
  have hw_sum : ∀ (k : ℕ), (∑ x : Fin k → α, ∏ i : Fin k, p (x i)) = 1 := by
    intro k
    rw [← Fintype.sum_pow p k, hs, one_pow]
  have h_upper : ∀ (k : ℕ), iidProb p (strongTypical p δ k) ≤ 1 := by
    intro k
    unfold iidProb
    calc
      (∑ x ∈ strongTypical p δ k, ∏ i : Fin k, p (x i))
          ≤ ∑ x : Fin k → α, ∏ i : Fin k, p (x i) :=
        Finset.sum_le_univ_sum_of_nonneg (hw_nonneg k)
      _ = 1 := hw_sum k
  have h_union : ∀ (k : ℕ),
      1 - iidProb p (strongTypical p δ k) ≤
        ∑ a : α, iidProb p {x : Fin k → α | δ < |(count x a : ℝ) / (k : ℝ) - p a|} := by
    intro k
    have h_lhs : 1 - iidProb p (strongTypical p δ k) =
        ∑ x : Fin k → α, (if x ∈ strongTypical p δ k then (0 : ℝ) else ∏ i : Fin k, p (x i)) := by
      rw [← hw_sum k]
      unfold iidProb
      have h_mem : (∑ x ∈ strongTypical p δ k, ∏ i : Fin k, p (x i)) =
          ∑ x : Fin k → α, (if x ∈ strongTypical p δ k then ∏ i : Fin k, p (x i) else 0) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [h_mem, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      split_ifs <;> ring
    have h_rhs : (∑ a : α, iidProb p {x : Fin k → α | δ < |(count x a : ℝ) / (k : ℝ) - p a|}) =
        ∑ x : Fin k → α, ∑ a : α,
          (if δ < |(count x a : ℝ) / (k : ℝ) - p a| then ∏ i : Fin k, p (x i) else 0) := by
      unfold iidProb
      simp_rw [Finset.sum_filter]
      exact Finset.sum_comm
    rw [h_lhs, h_rhs]
    refine Finset.sum_le_sum (fun x _ => ?_)
    have h_term_nonneg : ∀ a : α,
        0 ≤ (if δ < |(count x a : ℝ) / (k : ℝ) - p a| then ∏ i : Fin k, p (x i) else 0) := by
      intro a
      split_ifs
      · exact hw_nonneg k x
      · exact le_rfl
    by_cases hx : x ∈ strongTypical p δ k
    · rw [ite_eq_left hx]
      exact Finset.sum_nonneg (fun a _ => h_term_nonneg a)
    · rw [ite_eq_right hx]
      by_cases hw0 : (∏ i : Fin k, p (x i)) = 0
      · rw [hw0]
        exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> exact le_rfl)
      · have h_supp : ∀ a : α, p a = 0 → count x a = 0 := by
          intro a hpa
          by_contra hcnt
          unfold count at hcnt
          obtain ⟨i₀, hi₀⟩ := Finset.card_ne_zero.mp hcnt
          have hxi₀ : x i₀ = a := (Finset.mem_filter.mp hi₀).2
          have hprod0 : (∏ i : Fin k, p (x i)) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hxi₀, hpa])
          exact hw0 hprod0
        have hx' : ¬ ∀ a : α, |(count x a : ℝ) / (k : ℝ) - p a| ≤ δ ∧ (p a = 0 → count x a = 0) := by
          intro hall
          apply hx
          unfold strongTypical
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hall⟩
        obtain ⟨a₀, ha₀⟩ := not_forall.mp hx'
        have hdev : δ < |(count x a₀ : ℝ) / (k : ℝ) - p a₀| := by
          by_contra hle
          exact ha₀ ⟨not_lt.mp hle, h_supp a₀⟩
        calc
          (∏ i : Fin k, p (x i))
              = (if δ < |(count x a₀ : ℝ) / (k : ℝ) - p a₀| then ∏ i : Fin k, p (x i) else 0) := by
                rw [ite_eq_left hdev]
          _ ≤ ∑ a : α, (if δ < |(count x a : ℝ) / (k : ℝ) - p a| then ∏ i : Fin k, p (x i) else 0) :=
                Finset.single_le_sum (fun a _ => h_term_nonneg a) (Finset.mem_univ a₀)
  have h_cheb : ∀ {k : ℕ} (hk : 0 < k) (a : α),
      iidProb p {x : Fin k → α | δ < |(count x a : ℝ) / (k : ℝ) - p a|} * ((k : ℝ) * δ) ^ 2 ≤
        ∑ x : Fin k → α, (∏ i : Fin k, p (x i)) * ((count x a : ℝ) - (k : ℝ) * p a) ^ 2 := by
    intro k hk a
    have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
    have hkδ_nonneg : 0 ≤ (k : ℝ) * δ := mul_nonneg hkR.le hδ.le
    unfold iidProb
    rw [Finset.sum_mul]
    calc
      (∑ x ∈ {x : Fin k → α | δ < |(count x a : ℝ) / (k : ℝ) - p a|},
          (∏ i : Fin k, p (x i)) * ((k : ℝ) * δ) ^ 2)
          ≤ ∑ x ∈ {x : Fin k → α | δ < |(count x a : ℝ) / (k : ℝ) - p a|},
              (∏ i : Fin k, p (x i)) * ((count x a : ℝ) - (k : ℝ) * p a) ^ 2 := by
            refine Finset.sum_le_sum (fun x hx => ?_)
            have hdev : δ < |(count x a : ℝ) / (k : ℝ) - p a| := (Finset.mem_filter.mp hx).2
            have hfrac : (count x a : ℝ) / (k : ℝ) - p a =
                ((count x a : ℝ) - (k : ℝ) * p a) / (k : ℝ) := by
              field_simp [hk0]
            rw [hfrac, abs_div, abs_of_pos hkR, lt_div_iff₀ hkR, mul_comm δ (k : ℝ)] at hdev
            have hsq : ((k : ℝ) * δ) ^ 2 ≤ ((count x a : ℝ) - (k : ℝ) * p a) ^ 2 := by
              calc
                ((k : ℝ) * δ) ^ 2 = ((k : ℝ) * δ) * ((k : ℝ) * δ) := sq _
                _ ≤ |(count x a : ℝ) - (k : ℝ) * p a| * |(count x a : ℝ) - (k : ℝ) * p a| :=
                      mul_self_le_mul_self hkδ_nonneg hdev.le
                _ = |(count x a : ℝ) - (k : ℝ) * p a| ^ 2 := (sq _).symm
                _ = ((count x a : ℝ) - (k : ℝ) * p a) ^ 2 := sq_abs _
            exact mul_le_mul_of_nonneg_left hsq (hw_nonneg k x)
      _ ≤ ∑ x : Fin k → α, (∏ i : Fin k, p (x i)) * ((count x a : ℝ) - (k : ℝ) * p a) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg (fun x => mul_nonneg (hw_nonneg k x) (sq_nonneg _))
  have h_moment : ∀ (k : ℕ) (a : α),
      (∑ x : Fin k → α, (∏ i : Fin k, p (x i)) * ((count x a : ℝ) - (k : ℝ) * p a) ^ 2) =
        (k : ℝ) * p a * (1 - p a) := by
    intro k a
    let φ : α → ℝ := fun b => (if b = a then (1 : ℝ) else 0) - p a
    have h_m1 : (∑ b : α, p b * φ b) = 0 := by
      have h_pt : ∀ b : α, p b * φ b = (if b = a then p b else 0) - p b * p a := by
        intro b
        dsimp only [φ]
        split_ifs <;> ring
      simp_rw [h_pt]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ a p,
        ite_eq_left (Finset.mem_univ a), ← Finset.sum_mul, hs, one_mul, sub_self]
    have h_m2 : (∑ b : α, p b * φ b ^ 2) = p a * (1 - p a) := by
      have h_pt : ∀ b : α,
          p b * φ b ^ 2 = (if b = a then p b else 0) * (1 - 2 * p a) + p b * p a ^ 2 := by
        intro b
        dsimp only [φ]
        split_ifs <;> ring
      simp_rw [h_pt]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        Finset.sum_ite_eq' Finset.univ a p, ite_eq_left (Finset.mem_univ a), hs]
      ring
    have h_cnt : ∀ x : Fin k → α, (count x a : ℝ) - (k : ℝ) * p a = ∑ i : Fin k, φ (x i) := by
      intro x
      have hc : (count x a : ℝ) = ∑ i : Fin k, (if x i = a then (1 : ℝ) else 0) := by
        unfold count
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        split_ifs <;> norm_num
      have hk_pa : (k : ℝ) * p a = ∑ _i : Fin k, p a := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hc, hk_pa, ← Finset.sum_sub_distrib]
    simp_rw [h_cnt, sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    have h_pair : ∀ (i j : Fin k),
        (∑ x : Fin k → α, (∏ m : Fin k, p (x m)) * (φ (x i) * φ (x j))) =
          if j = i then p a * (1 - p a) else 0 := by
      intro i j
      let g : Fin k → α → ℝ := fun m b =>
        p b * (if m = i then φ b else 1) * (if m = j then φ b else 1)
      have h_prod_g : ∀ x : Fin k → α,
          (∏ m : Fin k, p (x m)) * (φ (x i) * φ (x j)) = ∏ m : Fin k, g m (x m) := by
        intro x
        dsimp only [g]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_ite_eq' Finset.univ i (fun m => φ (x m)), ite_eq_left (Finset.mem_univ i),
          Finset.prod_ite_eq' Finset.univ j (fun m => φ (x m)), ite_eq_left (Finset.mem_univ j)]
        ring
      simp_rw [h_prod_g]
      rw [← Fintype.prod_sum g]
      by_cases hij : j = i
      · rw [ite_eq_left hij]
        have h_inner : ∀ m : Fin k,
            (∑ b : α, g m b) = if m = i then p a * (1 - p a) else 1 := by
          intro m
          dsimp only [g]
          by_cases hmi : m = i
          · rw [ite_eq_left hmi]
            have h_sq : ∀ b : α,
                p b * (if m = i then φ b else 1) * (if m = j then φ b else 1) = p b * φ b ^ 2 := by
              intro b
              rw [ite_eq_left hmi, hij, ite_eq_left hmi]
              ring
            simp_rw [h_sq]
            exact h_m2
          · rw [ite_eq_right hmi]
            have h_neq : ∀ b : α,
                p b * (if m = i then φ b else 1) * (if m = j then φ b else 1) = p b := by
              intro b
              rw [ite_eq_right hmi, hij, ite_eq_right hmi]
              ring
            simp_rw [h_neq]
            exact hs
        simp_rw [h_inner]
        rw [Finset.prod_ite_eq' Finset.univ i (fun _ => p a * (1 - p a)),
          ite_eq_left (Finset.mem_univ i)]
      · rw [ite_eq_right hij]
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        have h_gi : ∀ b : α, g i b = p b * φ b := by
          intro b
          dsimp only [g]
          rw [ite_eq_left rfl, ite_eq_right (Ne.symm hij), mul_one]
        simp_rw [h_gi]
        exact h_m1
    simp_rw [h_pair]
    have h_diag : ∀ i : Fin k,
        (∑ j : Fin k, if j = i then p a * (1 - p a) else 0) = p a * (1 - p a) := by
      intro i
      rw [Finset.sum_ite_eq' Finset.univ i (fun _ => p a * (1 - p a)),
        ite_eq_left (Finset.mem_univ i)]
    simp_rw [h_diag]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
  have h_lower : ∀ (k : ℕ), 1 ≤ k →
      1 - (1 / δ ^ 2) / (k : ℝ) ≤ iidProb p (strongTypical p δ k) := by
    intro k hk
    have hk_pos : 0 < k := Nat.succ_le_iff.mp hk
    have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
    have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
    have hδ0 : δ ≠ 0 := hδ.ne'
    have hkδ_pos : 0 < ((k : ℝ) * δ) ^ 2 := sq_pos_of_pos (mul_pos hkR hδ)
    have h_sym : ∀ a : α,
        iidProb p {x : Fin k → α | δ < |(count x a : ℝ) / (k : ℝ) - p a|} * ((k : ℝ) * δ) ^ 2 ≤
          (k : ℝ) * p a := by
      intro a
      calc
        iidProb p {x : Fin k → α | δ < |(count x a : ℝ) / (k : ℝ) - p a|} * ((k : ℝ) * δ) ^ 2
            ≤ ∑ x : Fin k → α, (∏ i : Fin k, p (x i)) * ((count x a : ℝ) - (k : ℝ) * p a) ^ 2 :=
              h_cheb hk_pos a
        _ = (k : ℝ) * p a * (1 - p a) := h_moment k a
        _ ≤ (k : ℝ) * p a := by nlinarith [sq_nonneg (p a), hkR]
    have h_sum_sym :
        (∑ a : α, iidProb p {x : Fin k → α | δ < |(count x a : ℝ) / (k : ℝ) - p a|}) *
          ((k : ℝ) * δ) ^ 2 ≤ (k : ℝ) := by
      rw [Finset.sum_mul]
      calc
        (∑ a : α, iidProb p {x : Fin k → α | δ < |(count x a : ℝ) / (k : ℝ) - p a|} *
            ((k : ℝ) * δ) ^ 2)
            ≤ ∑ a : α, (k : ℝ) * p a := Finset.sum_le_sum (fun a _ => h_sym a)
        _ = (k : ℝ) * ∑ a : α, p a := (Finset.mul_sum Finset.univ p (k : ℝ)).symm
        _ = (k : ℝ) := by rw [hs, mul_one]
    have h_mult :
        (1 - iidProb p (strongTypical p δ k)) * ((k : ℝ) * δ) ^ 2 ≤ (k : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right (h_union k) hkδ_pos.le) h_sum_sym
    have h_div : 1 - iidProb p (strongTypical p δ k) ≤ (1 / δ ^ 2) / (k : ℝ) := by
      have h_div' : 1 - iidProb p (strongTypical p δ k) ≤ (k : ℝ) / ((k : ℝ) * δ) ^ 2 :=
        (le_div_iff₀ hkδ_pos).mpr h_mult
      have h_eq : (k : ℝ) / ((k : ℝ) * δ) ^ 2 = (1 / δ ^ 2) / (k : ℝ) := by
        field_simp [hk0, hδ0]
      rwa [h_eq] at h_div'
    linarith
  have hg_tendsto : Tendsto (fun k : ℕ => 1 - (1 / δ ^ 2) / (k : ℝ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h2 : Tendsto (fun k : ℕ => (1 / δ ^ 2) / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (1 / δ ^ 2)
    simpa only [sub_zero] using h1.sub h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hg_tendsto
    tendsto_const_nhds
    (Filter.eventually_atTop.mpr ⟨1, h_lower⟩)
    (Filter.Eventually.of_forall h_upper)

end Leap
