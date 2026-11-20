import LeapProofObligations.Definitions

open scoped BigOperators

namespace Leap

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Wilde Def 15.2.4 / Property 15.2.5: uniform conditional typicality. -/
theorem condTypical_prob (W : α → β → ℝ) (hW : ∀ a b, 0 ≤ W a b) (hW1 : ∀ a, ∑ b, W a b = 1)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ x : Fin k → α, 1 - ε ≤ condProb W x (condTypical W δ x) := by
  use ⌈1 / (ε * δ ^ 2)⌉₊ + 1
  intro k hk x
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := le_of_lt hk_pos
  have hkδ_pos : 0 < (k : ℝ) * δ := mul_pos hk_pos hδ
  have hkδ_sq_pos : 0 < ((k : ℝ) * δ) ^ 2 := pow_pos hkδ_pos 2
  have hP_nonneg : ∀ y : Fin k → β, 0 ≤ ∏ i, W (x i) (y i) := by
    intro y
    exact Finset.prod_nonneg (fun i _ => hW (x i) (y i))
  have hP_sum : (∑ y : Fin k → β, ∏ i, W (x i) (y i)) = 1 := by
    calc (∑ y : Fin k → β, ∏ i, W (x i) (y i))
      _ = ∏ i : Fin k, ∑ b : β, W (x i) b :=
          (Fintype.prod_sum (fun (i : Fin k) (b : β) => W (x i) b)).symm
      _ = ∏ _i : Fin k, (1 : ℝ) := Finset.prod_congr rfl (fun i _ => hW1 (x i))
      _ = 1 := Finset.prod_const_one
  have h_compl_prob : 1 - condProb W x (condTypical W δ x) =
      ∑ y ∈ (condTypical W δ x)ᶜ, ∏ i, W (x i) (y i) := by
    have hsplit : (∑ y ∈ condTypical W δ x, ∏ i, W (x i) (y i)) +
        (∑ y ∈ (condTypical W δ x)ᶜ, ∏ i, W (x i) (y i)) = 1 := by
      rw [Finset.sum_add_sum_compl, hP_sum]
    unfold condProb
    linarith
  have h_pointwise : ∀ y ∈ (condTypical W δ x)ᶜ,
      ((k : ℝ) * δ) ^ 2 * (∏ i, W (x i) (y i)) ≤
        (∏ i, W (x i) (y i)) *
          ∑ a, ∑ b, ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2 := by
    intro y hy
    rw [Finset.mem_compl] at hy
    by_cases hzero : ∃ i : Fin k, W (x i) (y i) = 0
    · obtain ⟨i₀, hi₀⟩ := hzero
      have hprod0 : (∏ i, W (x i) (y i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) hi₀
      rw [hprod0]
      simp
    · push Not at hzero
      have hsupp : ∀ a b, W a b = 0 → pairCount x y a b = 0 := by
        intro a b hW0
        by_contra hpc
        unfold pairCount at hpc
        obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hpc)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₀
        exact hzero i₀ (by rw [hi₀.1, hi₀.2, hW0])
      have hex : ∃ (a₀ : α) (b₀ : β),
          δ < |(pairCount x y a₀ b₀ : ℝ) / (k : ℝ) - W a₀ b₀ * (count x a₀ : ℝ) / (k : ℝ)| := by
        by_contra hno
        push Not at hno
        apply hy
        unfold condTypical
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro a b
        exact ⟨hno a b, hsupp a b⟩
      obtain ⟨a₀, b₀, hab₀⟩ := hex
      set Δ₀ : ℝ := (pairCount x y a₀ b₀ : ℝ) - W a₀ b₀ * (count x a₀ : ℝ)
      have hdiv : (pairCount x y a₀ b₀ : ℝ) / (k : ℝ) - W a₀ b₀ * (count x a₀ : ℝ) / (k : ℝ) =
          Δ₀ / (k : ℝ) := by
        dsimp [Δ₀]
        ring
      rw [hdiv, abs_div, abs_of_pos hk_pos] at hab₀
      have hkδ_lt : (k : ℝ) * δ < |Δ₀| := by
        have hmul := mul_lt_mul_of_pos_left hab₀ hk_pos
        have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
        calc (k : ℝ) * δ < (k : ℝ) * (|Δ₀| / (k : ℝ)) := hmul
          _ = |Δ₀| := mul_div_cancel₀ |Δ₀| hk_ne
      have hsq : ((k : ℝ) * δ) ^ 2 ≤ Δ₀ ^ 2 := by
        nlinarith [sq_abs Δ₀, hkδ_pos, hkδ_lt]
      have hb₀ : Δ₀ ^ 2 ≤ ∑ b : β, ((pairCount x y a₀ b : ℝ) - W a₀ b * (count x a₀ : ℝ)) ^ 2 := by
        dsimp only [Δ₀]
        exact Finset.single_le_sum
          (f := fun b => ((pairCount x y a₀ b : ℝ) - W a₀ b * (count x a₀ : ℝ)) ^ 2)
          (fun b _ => sq_nonneg _) (Finset.mem_univ b₀)
      have ha₀ : (∑ b : β, ((pairCount x y a₀ b : ℝ) - W a₀ b * (count x a₀ : ℝ)) ^ 2) ≤
          ∑ a : α, ∑ b : β, ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2 :=
        Finset.single_le_sum
          (f := fun a => ∑ b : β, ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2)
          (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))
          (Finset.mem_univ a₀)
      have hsum_ge : ((k : ℝ) * δ) ^ 2 ≤
          ∑ a : α, ∑ b : β, ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2 :=
        le_trans hsq (le_trans hb₀ ha₀)
      calc ((k : ℝ) * δ) ^ 2 * (∏ i, W (x i) (y i))
        _ = (∏ i, W (x i) (y i)) * ((k : ℝ) * δ) ^ 2 := mul_comm _ _
        _ ≤ (∏ i, W (x i) (y i)) *
              ∑ a, ∑ b, ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsum_ge (hP_nonneg y)
  have h_second_moment : ∀ (a : α) (b : β),
      (∑ y : Fin k → β, (∏ i, W (x i) (y i)) *
        ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2) =
        (count x a : ℝ) * W a b * (1 - W a b) := by
    intro a b
    let z : Fin k → β → ℝ := fun i c =>
      if x i = a then ((if c = b then (1 : ℝ) else 0) - W a b) else 0
    have hz_sum : ∀ y : Fin k → β,
        (pairCount x y a b : ℝ) - W a b * (count x a : ℝ) = ∑ i : Fin k, z i (y i) := by
      intro y
      unfold pairCount count
      rw [Finset.natCast_card_filter, Finset.natCast_card_filter, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      dsimp [z]
      split_ifs <;> simp_all
    have hz_mean : ∀ i : Fin k, ∑ c : β, W (x i) c * z i c = 0 := by
      intro i
      dsimp [z]
      by_cases hxi : x i = a
      · rw [hxi]
        simp only [↓reduceIte]
        have hcongr : ∀ c : β,
            W a c * ((if c = b then (1 : ℝ) else 0) - W a b) =
              (if c = b then W a c else 0) - W a c * W a b := by
          intro c
          split_ifs <;> ring
        simp_rw [hcongr]
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ b, ← Finset.sum_mul, hW1 a]
        simp
      · simp [hxi]
    have hz_var : ∀ i : Fin k,
        ∑ c : β, W (x i) c * (z i c * z i c) =
          if x i = a then W a b * (1 - W a b) else 0 := by
      intro i
      dsimp [z]
      by_cases hxi : x i = a
      · rw [hxi]
        simp only [↓reduceIte]
        have hcongr : ∀ c : β,
            W a c * (((if c = b then (1 : ℝ) else 0) - W a b) *
              ((if c = b then (1 : ℝ) else 0) - W a b)) =
              (if c = b then W a c * (1 - 2 * W a b) else 0) + W a c * (W a b) ^ 2 := by
          intro c
          split_ifs <;> ring
        simp_rw [hcongr]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ b, ← Finset.sum_mul, hW1 a]
        simp only [Finset.mem_univ, ↓reduceIte]
        ring
      · simp [hxi]
    have h_pair : ∀ (i j : Fin k),
        (∑ y : Fin k → β, (∏ m, W (x m) (y m)) * (z i (y i) * z j (y j))) =
          if j = i then (if x i = a then W a b * (1 - W a b) else 0) else 0 := by
      intro i j
      let F : Fin k → β → ℝ := fun m c =>
        W (x m) c * ((if m = i then z i c else 1) * (if m = j then z j c else 1))
      have hF_prod : ∀ y : Fin k → β,
          (∏ m, W (x m) (y m)) * (z i (y i) * z j (y j)) = ∏ m, F m (y m) := by
        intro y
        dsimp [F]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_ite_eq' Finset.univ i, Finset.prod_ite_eq' Finset.univ j]
        simp
      simp_rw [hF_prod]
      rw [← Fintype.prod_sum F]
      dsimp only [F]
      by_cases hji : j = i
      · rw [hji]
        simp only [↓reduceIte]
        have hF_diag : ∀ m : Fin k,
            (∑ c : β, W (x m) c * ((if m = i then z i c else 1) * (if m = i then z i c else 1))) =
              if m = i then (if x i = a then W a b * (1 - W a b) else 0) else 1 := by
          intro m
          by_cases hmi : m = i
          · rw [hmi]
            simp only [↓reduceIte]
            exact hz_var i
          · simp only [hmi, ↓reduceIte, mul_one]
            exact hW1 (x m)
        simp_rw [hF_diag]
        rw [Finset.prod_ite_eq' Finset.univ i]
        simp
      · simp only [hji, ↓reduceIte]
        have hij : i ≠ j := Ne.symm hji
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        simp only [hij, ↓reduceIte, mul_one]
        exact hz_mean i
    have hexpand : ∀ y : Fin k → β,
        (∏ i, W (x i) (y i)) * ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2 =
          ∑ i : Fin k, ∑ j : Fin k, (∏ m, W (x m) (y m)) * (z i (y i) * z j (y j)) := by
      intro y
      rw [hz_sum y, sq, Fintype.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    simp_rw [h_pair]
    have hcollapse_j : ∀ i : Fin k,
        (∑ j : Fin k, if j = i then (if x i = a then W a b * (1 - W a b) else 0) else 0) =
          if x i = a then W a b * (1 - W a b) else 0 := by
      intro i
      rw [Finset.sum_ite_eq' Finset.univ i]
      simp
    simp_rw [hcollapse_j]
    unfold count
    rw [Finset.natCast_card_filter, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> ring
  have h_var_le : (∑ a : α, ∑ b : β, (count x a : ℝ) * W a b * (1 - W a b)) ≤ (k : ℝ) := by
    have h_row : ∀ a : α,
        (∑ b : β, (count x a : ℝ) * W a b * (1 - W a b)) ≤ (count x a : ℝ) := by
      intro a
      calc (∑ b : β, (count x a : ℝ) * W a b * (1 - W a b))
        _ ≤ ∑ b : β, (count x a : ℝ) * W a b := by
            refine Finset.sum_le_sum (fun b _ => ?_)
            have hcW : 0 ≤ (count x a : ℝ) * W a b :=
              mul_nonneg (Nat.cast_nonneg _) (hW a b)
            have hprod_nonneg : 0 ≤ ((count x a : ℝ) * W a b) * W a b :=
              mul_nonneg hcW (hW a b)
            linarith
        _ = (count x a : ℝ) * ∑ b : β, W a b := (Finset.mul_sum _ _ _).symm
        _ = (count x a : ℝ) * 1 := by rw [hW1 a]
        _ = (count x a : ℝ) := mul_one _
    have h_count_sum : (∑ a : α, (count x a : ℝ)) = (k : ℝ) := by
      unfold count
      simp_rw [Finset.natCast_card_filter]
      rw [Finset.sum_comm]
      have h1 : ∀ i : Fin k, (∑ a : α, if x i = a then (1 : ℝ) else 0) = 1 := by
        intro i
        rw [Finset.sum_ite_eq Finset.univ (x i)]
        simp
      simp_rw [h1]
      simp
    calc (∑ a : α, ∑ b : β, (count x a : ℝ) * W a b * (1 - W a b))
      _ ≤ ∑ a : α, (count x a : ℝ) := Finset.sum_le_sum (fun a _ => h_row a)
      _ = (k : ℝ) := h_count_sum
  have h_chebyshev : ((k : ℝ) * δ) ^ 2 * (1 - condProb W x (condTypical W δ x)) ≤ (k : ℝ) := by
    calc ((k : ℝ) * δ) ^ 2 * (1 - condProb W x (condTypical W δ x))
      _ = ((k : ℝ) * δ) ^ 2 * ∑ y ∈ (condTypical W δ x)ᶜ, ∏ i, W (x i) (y i) := by
          rw [h_compl_prob]
      _ = ∑ y ∈ (condTypical W δ x)ᶜ, ((k : ℝ) * δ) ^ 2 * ∏ i, W (x i) (y i) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ y ∈ (condTypical W δ x)ᶜ,
            (∏ i, W (x i) (y i)) *
              ∑ a, ∑ b, ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2 :=
          Finset.sum_le_sum h_pointwise
      _ ≤ ∑ y : Fin k → β,
            (∏ i, W (x i) (y i)) *
              ∑ a, ∑ b, ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2 := by
          refine Finset.sum_le_univ_sum_of_nonneg (fun y => ?_)
          exact mul_nonneg (hP_nonneg y)
            (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _)))
      _ = ∑ a : α, ∑ b : β, ∑ y : Fin k → β,
            (∏ i, W (x i) (y i)) *
              ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2 := by
          have hdist : ∀ y : Fin k → β,
              (∏ i, W (x i) (y i)) *
                (∑ a, ∑ b, ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2) =
                ∑ a, ∑ b, (∏ i, W (x i) (y i)) *
                  ((pairCount x y a b : ℝ) - W a b * (count x a : ℝ)) ^ 2 := by
            intro y
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Finset.mul_sum]
          simp_rw [hdist]
          rw [Finset.sum_comm]
          conv_lhs =>
            arg 2
            ext a
            rw [Finset.sum_comm]
      _ = ∑ a : α, ∑ b : β, (count x a : ℝ) * W a b * (1 - W a b) := by
          simp_rw [h_second_moment]
      _ ≤ (k : ℝ) := h_var_le
  have hεδ_pos : 0 < ε * δ ^ 2 := mul_pos hε (pow_pos hδ 2)
  have hk_ge_inv : 1 / (ε * δ ^ 2) ≤ (k : ℝ) := by
    have hceil : 1 / (ε * δ ^ 2) ≤ (⌈1 / (ε * δ ^ 2)⌉₊ : ℝ) := Nat.le_ceil _
    have hk_cast : ((⌈1 / (ε * δ ^ 2)⌉₊ + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    push_cast at hk_cast
    linarith
  have h1_le : 1 ≤ (k : ℝ) * (ε * δ ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hk_ge_inv (le_of_lt hεδ_pos)
    have hne : ε * δ ^ 2 ≠ 0 := ne_of_gt hεδ_pos
    have hcancel : 1 / (ε * δ ^ 2) * (ε * δ ^ 2) = 1 := one_div_mul_cancel hne
    linarith
  have hk_le_sq : (k : ℝ) ≤ ((k : ℝ) * δ) ^ 2 * ε := by
    have hmul := mul_le_mul_of_nonneg_left h1_le hk_nonneg
    nlinarith
  have h_final_mul : ((k : ℝ) * δ) ^ 2 * (1 - condProb W x (condTypical W δ x)) ≤
      ((k : ℝ) * δ) ^ 2 * ε :=
    le_trans h_chebyshev hk_le_sq
  have h_one_sub : 1 - condProb W x (condTypical W δ x) ≤ ε :=
    le_of_mul_le_mul_left h_final_mul hkδ_sq_pos
  linarith

end Leap
