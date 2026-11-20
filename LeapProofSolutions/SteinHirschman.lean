import LeapProofObligations.Definitions

open Complex Complex.HadamardThreeLines MeasureTheory
open scoped Real

namespace Leap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

/-- Wilde Thm 12.2.3: operator Stein–Hirschman interpolation, general exponents. -/
theorem stein_hirschman (G : ℂ → H →L[ℂ] K) (hd : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hb : BddAbove ((norm ∘ G) '' verticalClosedStrip 0 1)) {θ p₀ p₁ pθ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hpθ : 1 / pθ = (1 - θ) / p₀ + θ / p₁) (hGθ : schattenNorm pθ (G θ) ≠ 0)
    (hα : Integrable fun t : ℝ =>
      hirschmanAlpha θ t * Real.log (schattenNorm p₀ (G (I * t)) ^ (1 - θ)))
    (hβ : Integrable fun t : ℝ =>
      hirschmanBeta θ t * Real.log (schattenNorm p₁ (G (1 + I * t)) ^ θ)) :
    Real.log (schattenNorm pθ (G θ)) ≤
      ∫ t : ℝ, (hirschmanAlpha θ t * Real.log (schattenNorm p₀ (G (I * t)) ^ (1 - θ))
        + hirschmanBeta θ t * Real.log (schattenNorm p₁ (G (1 + I * t)) ^ θ)) := by
  
  have hs1 : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip 0 1) ∧
      ContinuousOn g (verticalClosedStrip 0 1) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ verticalClosedStrip 0 1, ‖g z‖ ≤ M) ∧
      0 < schattenNorm pθ (G θ) ∧ ‖g θ‖ = schattenNorm pθ (G θ) ∧
      (∀ t : ℝ, ‖g (I * t)‖ ≤ schattenNorm p₀ (G (I * t))) ∧
      (∀ t : ℝ, ‖g (1 + I * t)‖ ≤ schattenNorm p₁ (G (1 + I * t))) := by
    clear hα hβ
    have hθ0 : 0 < θ := hθ.1
    have hθ1 : θ < 1 := hθ.2
    have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
    have hp₀_pos : 0 < p₀ := lt_of_lt_of_le zero_lt_one hp₀
    have hp₁_pos : 0 < p₁ := lt_of_lt_of_le zero_lt_one hp₁
    have hinv_pθ_pos : 0 < 1 / pθ := by
      rw [hpθ]
      positivity
    have hpθ_pos : 0 < pθ := one_div_pos.mp hinv_pθ_pos
    have hsing_nn : ∀ (T : H →L[ℂ] K) i, 0 ≤ singularValues T i :=
      fun T i => Real.sqrt_nonneg _
    have hschatten_nn : ∀ (p : ℝ) (T : H →L[ℂ] K), 0 ≤ schattenNorm p T := by
      intro p T
      unfold schattenNorm
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hsing_nn T i) p) _
    let c : ℝ := schattenNorm pθ (G θ)
    have hc_pos : 0 < c := lt_of_le_of_ne (hschatten_nn pθ (G θ)) (Ne.symm hGθ)
    have hspec : ∀ (T : H →L[ℂ] K),
        let b := (isSymmetric_adjoint_comp_self T).eigenvectorBasis rfl
        (∀ i, ‖T (b i)‖ = singularValues T i) ∧
        (∀ i j, i ≠ j → inner ℂ (T (b i)) (T (b j)) = 0) := by
      intro T
      let hsym := isSymmetric_adjoint_comp_self T
      let b := hsym.eigenvectorBasis rfl
      let lam := hsym.eigenvalues rfl
      have hinner_T : ∀ i j, inner ℂ (T (b i)) (T (b j)) = (lam j : ℂ) * inner ℂ (b i) (b j) := by
        intro i j
        rw [← ContinuousLinearMap.adjoint_inner_right T (b i) (T (b j))]
        have happ : (ContinuousLinearMap.adjoint T) (T (b j)) = (lam j : ℂ) • b j :=
          hsym.apply_eigenvectorBasis rfl j
        rw [happ, inner_smul_right]
      refine ⟨?_, ?_⟩
      · intro j
        have hre := congrArg Complex.re (hinner_T j j)
        have hbj_norm : ‖b j‖ = 1 := b.orthonormal.1 j
        have hlhs : (inner ℂ (T (b j)) (T (b j))).re = ‖T (b j)‖ ^ 2 := by
          simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) (T (b j))).symm
        have hrhs : ((lam j : ℂ) * inner ℂ (b j) (b j)).re = lam j := by
          have hbb : inner ℂ (b j) (b j) = 1 := by
            rw [inner_self_eq_norm_sq_to_K, hbj_norm]
            norm_num
          rw [hbb, mul_one, ofReal_re]
        have hlam_eq : lam j = ‖T (b j)‖ ^ 2 := by linarith
        change ‖T (b j)‖ = √(lam j)
        rw [hlam_eq, Real.sqrt_sq (norm_nonneg _)]
      · intro i j hij
        rw [hinner_T i j, b.orthonormal.2 hij, mul_zero]
    have hduality : ∀ {ι : Type} [Fintype ι] {e : ι → H} {f : ι → K} {w : ι → ℝ}
        (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f)
        (hw_pos : ∀ i, 0 < w i) (hw_sum : ∑ i : ι, w i = 1)
        {p : ℝ} (hp : 1 ≤ p) (T : H →L[ℂ] K),
        ∑ i : ι, (w i) ^ (1 - p⁻¹) * ‖inner ℂ (f i) (T (e i))‖ ≤ schattenNorm p T := by
      intro ι _ e f w he hf hw_pos hw_sum p hp T
      have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
      have h1p_nn : 0 ≤ 1 - p⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hp)
      let b := (isSymmetric_adjoint_comp_self T).eigenvectorBasis rfl
      have hb_norm : ∀ j, ‖T (b j)‖ = singularValues T j := (hspec T).1
      have hb_orth : ∀ i j, i ≠ j → inner ℂ (T (b i)) (T (b j)) = 0 := (hspec T).2
      let σ : Fin (Module.finrank ℂ H) → ℝ := singularValues T
      let u_tilde : Fin (Module.finrank ℂ H) → K :=
        fun j => if σ j = 0 then 0 else ((σ j : ℂ)⁻¹) • T (b j)
      have hT_eq : ∀ j, T (b j) = (σ j : ℂ) • u_tilde j := by
        intro j
        dsimp only [u_tilde]
        split_ifs with h0
        · have hnorm0 : ‖T (b j)‖ = 0 := by rw [hb_norm j]; exact h0
          rw [norm_eq_zero.mp hnorm0, h0, ofReal_zero, zero_smul]
        · rw [smul_smul, mul_inv_cancel₀ (ofReal_ne_zero.mpr h0), one_smul]
      have hu_norm_le : ∀ j, ‖u_tilde j‖ ≤ 1 := by
        intro j
        dsimp only [u_tilde]
        split_ifs with h0
        · simp
        · have hσ_pos : 0 < σ j := lt_of_le_of_ne (hsing_nn T j) (Ne.symm h0)
          rw [norm_smul, norm_inv, Complex.norm_of_nonneg hσ_pos.le, hb_norm j,
            inv_mul_cancel₀ h0]
      let S_pos : Finset (Fin (Module.finrank ℂ H)) := Finset.univ.filter (fun j => 0 < σ j)
      have hu_orth : Orthonormal ℂ (fun j : S_pos => u_tilde j.1) := by
        refine ⟨?_, ?_⟩
        · intro j
          have hj_pos : 0 < σ j.1 := (Finset.mem_filter.mp j.2).2
          have h0 : σ j.1 ≠ 0 := hj_pos.ne'
          dsimp only [u_tilde]
          rw [if_neg h0, norm_smul, norm_inv, Complex.norm_of_nonneg hj_pos.le, hb_norm j.1,
            inv_mul_cancel₀ h0]
        · intro i j hij
          have hij1 : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
          have hi0 : σ i.1 ≠ 0 := ((Finset.mem_filter.mp i.2).2).ne'
          have hj0 : σ j.1 ≠ 0 := ((Finset.mem_filter.mp j.2).2).ne'
          dsimp only [u_tilde]
          rw [if_neg hi0, if_neg hj0, inner_smul_left, inner_smul_right,
            hb_orth i.1 j.1 hij1, mul_zero, mul_zero]
      let M : ι → Fin (Module.finrank ℂ H) → ℝ :=
        fun i j => ‖inner ℂ (b j) (e i)‖ * ‖inner ℂ (f i) (u_tilde j)‖
      have hM_nn : ∀ i j, 0 ≤ M i j := fun i j => mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hterm_bound : ∀ i : ι, ‖inner ℂ (f i) (T (e i))‖ ≤ ∑ j, σ j * M i j := by
        intro i
        have hrepr : ∑ j, inner ℂ (b j) (e i) • b j = e i := by
          simpa [OrthonormalBasis.repr_apply_apply] using b.sum_repr (e i)
        have hTe : T (e i) = ∑ j, (inner ℂ (b j) (e i) * (σ j : ℂ)) • u_tilde j := by
          conv_lhs => rw [← hrepr]
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [T.map_smul, hT_eq j, smul_smul]
        rw [hTe, inner_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [inner_smul_right, norm_mul, norm_mul, Complex.norm_of_nonneg (hsing_nn T j)]
        dsimp only [M, σ]
        exact le_of_eq (by ring)
      have hM_row : ∀ i : ι, ∑ j, M i j ≤ 1 := by
        intro i
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun j => ‖inner ℂ (b j) (e i)‖) (fun j => ‖inner ℂ (f i) (u_tilde j)‖)
        have h1 : ∑ j, ‖inner ℂ (b j) (e i)‖ ^ 2 = 1 := by
          rw [b.sum_sq_norm_inner_right (e i), he.1 i, one_pow]
        have h2 : ∑ j, ‖inner ℂ (f i) (u_tilde j)‖ ^ 2 ≤ 1 := by
          have hsum_eq : ∑ j : Fin (Module.finrank ℂ H), ‖inner ℂ (f i) (u_tilde j)‖ ^ 2 =
              ∑ j ∈ S_pos, ‖inner ℂ (u_tilde j) (f i)‖ ^ 2 := by
            rw [← Finset.sum_subset (Finset.subset_univ S_pos)]
            · refine Finset.sum_congr rfl fun j _ => by rw [norm_inner_symm]
            · intro j _ hj_not
              have hnot_pos : ¬ 0 < σ j := fun hpos =>
                hj_not (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hpos⟩)
              have h0 : σ j = 0 := le_antisymm (not_lt.mp hnot_pos) (hsing_nn T j)
              dsimp only [u_tilde]
              rw [if_pos h0, inner_zero_right, norm_zero, sq, mul_zero]
          rw [hsum_eq, ← Finset.sum_coe_sort S_pos (fun j => ‖inner ℂ (u_tilde j) (f i)‖ ^ 2)]
          exact (hu_orth.sum_inner_products_le (s := Finset.univ) (f i)).trans_eq
            (by rw [hf.1 i, one_pow])
        have hsum_nn : 0 ≤ ∑ j, M i j := Finset.sum_nonneg fun j _ => hM_nn i j
        rw [h1, one_mul] at hcs
        have hsq_le : (∑ j, M i j) ^ 2 ≤ 1 := hcs.trans h2
        nlinarith
      have hM_col : ∀ j : Fin (Module.finrank ℂ H), ∑ i : ι, M i j ≤ 1 := by
        intro j
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun i : ι => ‖inner ℂ (b j) (e i)‖) (fun i : ι => ‖inner ℂ (f i) (u_tilde j)‖)
        have h1 : ∑ i : ι, ‖inner ℂ (b j) (e i)‖ ^ 2 ≤ 1 := by
          have hsymm : ∑ i : ι, ‖inner ℂ (b j) (e i)‖ ^ 2 = ∑ i : ι, ‖inner ℂ (e i) (b j)‖ ^ 2 :=
            Finset.sum_congr rfl fun i _ => by rw [norm_inner_symm]
          rw [hsymm]
          exact (he.sum_inner_products_le (s := Finset.univ) (b j)).trans_eq
            (by rw [b.orthonormal.1 j, one_pow])
        have h2 : ∑ i : ι, ‖inner ℂ (f i) (u_tilde j)‖ ^ 2 ≤ 1 := by
          have hnu : ‖u_tilde j‖ ^ 2 ≤ 1 := by
            have := hu_norm_le j
            have := norm_nonneg (u_tilde j)
            nlinarith
          exact (hf.sum_inner_products_le (s := Finset.univ) (u_tilde j)).trans hnu
        have hsum_nn : 0 ≤ ∑ i : ι, M i j := Finset.sum_nonneg fun i _ => hM_nn i j
        have hprod_le : (∑ i : ι, ‖inner ℂ (b j) (e i)‖ ^ 2) *
            (∑ i : ι, ‖inner ℂ (f i) (u_tilde j)‖ ^ 2) ≤ 1 := by
          have h1_nn : 0 ≤ ∑ i : ι, ‖inner ℂ (b j) (e i)‖ ^ 2 :=
            Finset.sum_nonneg fun i _ => sq_nonneg _
          have h2_nn : 0 ≤ ∑ i : ι, ‖inner ℂ (f i) (u_tilde j)‖ ^ 2 :=
            Finset.sum_nonneg fun i _ => sq_nonneg _
          nlinarith
        have hsq_le : (∑ i : ι, M i j) ^ 2 ≤ 1 := hcs.trans hprod_le
        nlinarith
      let W : ι × Fin (Module.finrank ℂ H) → ℝ := fun x => M x.1 x.2 * w x.1
      let F : ι × Fin (Module.finrank ℂ H) → ℝ := fun x => (w x.1) ^ (-p⁻¹) * σ x.2
      have hW_nn : ∀ x, 0 ≤ W x := fun x => mul_nonneg (hM_nn x.1 x.2) (hw_pos x.1).le
      have hF_nn : ∀ x, 0 ≤ F x := fun x =>
        mul_nonneg (Real.rpow_nonneg (hw_pos x.1).le _) (hsing_nn T x.2)
      have hholder := Real.inner_le_weight_mul_Lp_of_nonneg
        (Finset.univ : Finset (ι × Fin (Module.finrank ℂ H))) hp W F hW_nn hF_nn
      have hlhs_le : ∑ i : ι, (w i) ^ (1 - p⁻¹) * ‖inner ℂ (f i) (T (e i))‖ ≤
          ∑ x : ι × Fin (Module.finrank ℂ H), W x * F x := by
        calc ∑ i : ι, (w i) ^ (1 - p⁻¹) * ‖inner ℂ (f i) (T (e i))‖
            ≤ ∑ i : ι, (w i) ^ (1 - p⁻¹) * ∑ j, σ j * M i j :=
              Finset.sum_le_sum fun i _ =>
                mul_le_mul_of_nonneg_left (hterm_bound i) (Real.rpow_nonneg (hw_pos i).le _)
          _ = ∑ i : ι, ∑ j, W (i, j) * F (i, j) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              dsimp only [W, F]
              have hw_rpow : w i * (w i) ^ (-p⁻¹) = (w i) ^ (1 - p⁻¹) := by
                rw [sub_eq_add_neg, Real.rpow_add (hw_pos i), Real.rpow_one]
              calc (w i) ^ (1 - p⁻¹) * (σ j * M i j)
                  = M i j * (w i) ^ (1 - p⁻¹) * σ j := by ring
                _ = M i j * (w i * (w i) ^ (-p⁻¹)) * σ j := by rw [hw_rpow]
                _ = (M i j * w i) * ((w i) ^ (-p⁻¹) * σ j) := by ring
          _ = ∑ x : ι × Fin (Module.finrank ℂ H), W x * F x :=
              (Fintype.sum_prod_type (fun x : ι × Fin (Module.finrank ℂ H) => W x * F x)).symm
      have hW_sum_le : ∑ x : ι × Fin (Module.finrank ℂ H), W x ≤ 1 := by
        rw [Fintype.sum_prod_type]
        calc ∑ i : ι, ∑ j, M i j * w i
            = ∑ i : ι, (∑ j, M i j) * w i :=
              Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
          _ ≤ ∑ i : ι, 1 * w i :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hM_row i) (hw_pos i).le
          _ = 1 := by simp [hw_sum]
      have hW_rpow_le : (∑ x : ι × Fin (Module.finrank ℂ H), W x) ^ (1 - p⁻¹) ≤ 1 := by
        have hW_sum_nn : 0 ≤ ∑ x : ι × Fin (Module.finrank ℂ H), W x :=
          Finset.sum_nonneg fun x _ => hW_nn x
        exact (Real.rpow_le_rpow hW_sum_nn hW_sum_le h1p_nn).trans_eq (Real.one_rpow _)
      have hWFp_le : ∑ x : ι × Fin (Module.finrank ℂ H), W x * (F x) ^ p ≤ ∑ j, (σ j) ^ p := by
        have hterm_eq : ∀ i j, W (i, j) * (F (i, j)) ^ p = M i j * (σ j) ^ p := by
          intro i j
          dsimp only [W, F, σ]
          rw [Real.mul_rpow (Real.rpow_nonneg (hw_pos i).le _) (hsing_nn T j),
            ← Real.rpow_mul (hw_pos i).le, neg_mul, inv_mul_cancel₀ hp_pos.ne',
            Real.rpow_neg_one]
          have hwi_ne : w i ≠ 0 := (hw_pos i).ne'
          field_simp
        rw [Fintype.sum_prod_type_right]
        calc ∑ j, ∑ i : ι, W (i, j) * (F (i, j)) ^ p
            = ∑ j, ∑ i : ι, M i j * (σ j) ^ p :=
              Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hterm_eq i j
          _ = ∑ j, (∑ i : ι, M i j) * (σ j) ^ p :=
              Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
          _ ≤ ∑ j, 1 * (σ j) ^ p :=
              Finset.sum_le_sum fun j _ =>
                mul_le_mul_of_nonneg_right (hM_col j) (Real.rpow_nonneg (hsing_nn T j) p)
          _ = ∑ j, (σ j) ^ p := by simp
      have hWFp_rpow_le :
          (∑ x : ι × Fin (Module.finrank ℂ H), W x * (F x) ^ p) ^ p⁻¹ ≤ schattenNorm p T := by
        unfold schattenNorm
        rw [one_div]
        have hWFp_nn : 0 ≤ ∑ x : ι × Fin (Module.finrank ℂ H), W x * (F x) ^ p :=
          Finset.sum_nonneg fun x _ => mul_nonneg (hW_nn x) (Real.rpow_nonneg (hF_nn x) p)
        exact Real.rpow_le_rpow hWFp_nn hWFp_le (inv_nonneg.mpr hp_pos.le)
      have hrhs_le :
          (∑ x : ι × Fin (Module.finrank ℂ H), W x) ^ (1 - p⁻¹) *
            (∑ x : ι × Fin (Module.finrank ℂ H), W x * (F x) ^ p) ^ p⁻¹ ≤ schattenNorm p T := by
        have h2_nn : 0 ≤ (∑ x : ι × Fin (Module.finrank ℂ H), W x * (F x) ^ p) ^ p⁻¹ :=
          Real.rpow_nonneg
            (Finset.sum_nonneg fun x _ => mul_nonneg (hW_nn x) (Real.rpow_nonneg (hF_nn x) p)) _
        calc (∑ x, W x) ^ (1 - p⁻¹) * (∑ x, W x * (F x) ^ p) ^ p⁻¹
            ≤ 1 * (∑ x, W x * (F x) ^ p) ^ p⁻¹ := mul_le_mul_of_nonneg_right hW_rpow_le h2_nn
          _ = (∑ x, W x * (F x) ^ p) ^ p⁻¹ := one_mul _
          _ ≤ schattenNorm p T := hWFp_rpow_le
      exact hlhs_le.trans (hholder.trans hrhs_le)
    let b₀ := (isSymmetric_adjoint_comp_self (G θ)).eigenvectorBasis rfl
    let s : Fin (Module.finrank ℂ H) → ℝ := singularValues (G θ)
    have hb₀_norm : ∀ i, ‖G θ (b₀ i)‖ = s i := (hspec (G θ)).1
    have hb₀_orth : ∀ i j, i ≠ j → inner ℂ (G θ (b₀ i)) (G θ (b₀ j)) = 0 := (hspec (G θ)).2
    let S₀ : Finset (Fin (Module.finrank ℂ H)) := Finset.univ.filter (fun i => 0 < s i)
    let e : S₀ → H := fun i => b₀ i.1
    let f : S₀ → K := fun i => ((s i.1 : ℂ)⁻¹) • G θ (b₀ i.1)
    let w : S₀ → ℝ := fun i => (s i.1 / c) ^ pθ
    have he_orth : Orthonormal ℂ e := b₀.orthonormal.comp _ Subtype.val_injective
    have hf_orth : Orthonormal ℂ f := by
      refine ⟨?_, ?_⟩
      · intro i
        have hi_pos : 0 < s i.1 := (Finset.mem_filter.mp i.2).2
        dsimp only [f]
        rw [norm_smul, norm_inv, Complex.norm_of_nonneg hi_pos.le, hb₀_norm i.1,
          inv_mul_cancel₀ hi_pos.ne']
      · intro i j hij
        have hij1 : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
        dsimp only [f]
        rw [inner_smul_left, inner_smul_right, hb₀_orth i.1 j.1 hij1, mul_zero, mul_zero]
    have hw_pos : ∀ i : S₀, 0 < w i := fun i =>
      Real.rpow_pos_of_pos (div_pos ((Finset.mem_filter.mp i.2).2) hc_pos) pθ
    have hw_sum : ∑ i : S₀, w i = 1 := by
      have hsum_s : ∑ j : Fin (Module.finrank ℂ H), (s j) ^ pθ = c ^ pθ := by
        have hc_def : c = (∑ j, (s j) ^ pθ) ^ (1 / pθ) := rfl
        have hsum_nn : 0 ≤ ∑ j, (s j) ^ pθ :=
          Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hsing_nn (G θ) j) pθ
        rw [hc_def, ← Real.rpow_mul hsum_nn, one_div_mul_cancel hpθ_pos.ne', Real.rpow_one]
      have hsub_s : ∑ j ∈ S₀, (s j) ^ pθ = ∑ j, (s j) ^ pθ := by
        refine Finset.sum_subset (Finset.subset_univ S₀) fun j _ hj_not => ?_
        have hnot_pos : ¬ 0 < s j := fun hpos =>
          hj_not (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hpos⟩)
        have h0 : s j = 0 := le_antisymm (not_lt.mp hnot_pos) (hsing_nn (G θ) j)
        rw [h0, Real.zero_rpow hpθ_pos.ne']
      have hc_pθ_ne : c ^ pθ ≠ 0 := (Real.rpow_pos_of_pos hc_pos pθ).ne'
      calc ∑ i : S₀, w i
          = ∑ j ∈ S₀, (s j / c) ^ pθ := Finset.sum_coe_sort S₀ (fun j => (s j / c) ^ pθ)
        _ = ∑ j ∈ S₀, (s j) ^ pθ / c ^ pθ :=
            Finset.sum_congr rfl fun j _ => Real.div_rpow (hsing_nn (G θ) j) hc_pos.le pθ
        _ = (∑ j ∈ S₀, (s j) ^ pθ) / c ^ pθ := (Finset.sum_div _ _ _).symm
        _ = c ^ pθ / c ^ pθ := by rw [hsub_s, hsum_s]
        _ = 1 := div_self hc_pθ_ne
    have hw_le1 : ∀ i : S₀, w i ≤ 1 := fun i => by
      rw [← hw_sum]
      exact Finset.single_le_sum (fun j _ => (hw_pos j).le) (Finset.mem_univ i)
    let γ : ℂ → ℂ := fun z =>
      (1 - z) * ((1 - p₀⁻¹ : ℝ) : ℂ) + z * ((1 - p₁⁻¹ : ℝ) : ℂ)
    let g : ℂ → ℂ := fun z =>
      ∑ i : S₀, ((w i : ℂ) ^ (γ z)) * inner ℂ (f i) (G z (e i))
    have hstrip_sub : verticalClosedStrip 0 1 ⊆ closure (verticalStrip 0 1) := by
      intro z hz
      have hz0 : 0 ≤ z.re := hz.1
      have hz1 : z.re ≤ 1 := hz.2
      rw [Metric.mem_closure_iff]
      intro δ hδ
      let D : ℝ := ‖z - (2⁻¹ : ℂ)‖ + 1
      have hD_pos : 0 < D := by positivity
      let t : ℝ := min (2⁻¹) (δ / (2 * D))
      have ht_pos : 0 < t := lt_min (by norm_num) (by positivity)
      have ht_lt1 : t < 1 := (min_le_left _ _).trans_lt (by norm_num)
      let u : ℂ := ((1 - t : ℝ) : ℂ) * z + (t : ℂ) * (2⁻¹ : ℂ)
      refine ⟨u, ?_, ?_⟩
      · have hure : u.re = (1 - t) * z.re + t * 2⁻¹ := by
          dsimp only [u]
          simp [mul_re, ofReal_re, ofReal_im]
        change 0 < u.re ∧ u.re < 1
        rw [hure]
        constructor <;> nlinarith
      · have hzu : z - u = (t : ℂ) * (z - (2⁻¹ : ℂ)) := by
          dsimp only [u]
          push_cast
          ring
        rw [dist_eq_norm, hzu, norm_mul, Complex.norm_of_nonneg ht_pos.le]
        have ht_le : t ≤ δ / (2 * D) := min_le_right _ _
        have hnorm_lt : ‖z - (2⁻¹ : ℂ)‖ < D := lt_add_one _
        calc t * ‖z - (2⁻¹ : ℂ)‖
            ≤ (δ / (2 * D)) * D :=
              mul_le_mul ht_le hnorm_lt.le (norm_nonneg _) (by positivity)
          _ = δ / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hD_pos.ne']
          _ < δ := half_lt_self hδ
    have hG_cont : ContinuousOn G (verticalClosedStrip 0 1) := hd.continuousOn.mono hstrip_sub
    have hγ_diff : Differentiable ℂ γ := by
      dsimp only [γ]
      exact ((differentiable_const _).sub differentiable_id).mul_const _ |>.add
        (differentiable_id.mul_const _)
    have hw_pow_diff : ∀ i : S₀, Differentiable ℂ (fun z => (w i : ℂ) ^ (γ z)) := by
      intro i
      have hwi_ne : (w i : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hw_pos i).ne'
      have heq : (fun z => (w i : ℂ) ^ (γ z)) =
          fun z => Complex.exp (Complex.log (w i : ℂ) * γ z) := by
        ext z
        exact cpow_def_of_ne_zero hwi_ne (γ z)
      rw [heq]
      exact Complex.differentiable_exp.comp ((differentiable_const _).mul hγ_diff)
    have hg_diff : DifferentiableOn ℂ g (verticalStrip 0 1) := by
      have hsum_diff : ∀ s_fin : Finset S₀,
          DifferentiableOn ℂ (fun z => ∑ i ∈ s_fin, ((w i : ℂ) ^ (γ z)) * inner ℂ (f i) (G z (e i)))
            (verticalStrip 0 1) := by
        intro s_fin
        induction s_fin using Finset.cons_induction with
        | empty => simpa using differentiableOn_const (0 : ℂ)
        | cons i s_rem hi ih =>
            simp only [Finset.sum_cons]
            let L : (H →L[ℂ] K) →L[ℂ] ℂ :=
              (innerSL ℂ (f i)).comp (ContinuousLinearMap.apply ℂ K (e i))
            exact ((hw_pow_diff i).differentiableOn.mul
              (L.differentiable.comp_differentiableOn hd.differentiableOn)).add ih
      exact hsum_diff Finset.univ
    have hg_cont : ContinuousOn g (verticalClosedStrip 0 1) := by
      refine continuousOn_finset_sum Finset.univ fun i _ => ?_
      let L : (H →L[ℂ] K) →L[ℂ] ℂ :=
        (innerSL ℂ (f i)).comp (ContinuousLinearMap.apply ℂ K (e i))
      exact (hw_pow_diff i).continuous.continuousOn.mul (L.continuous.comp_continuousOn hG_cont)
    have hγ_re : ∀ z : ℂ, (γ z).re = (1 - z.re) * (1 - p₀⁻¹) + z.re * (1 - p₁⁻¹) := by
      intro z
      dsimp only [γ]
      simp [mul_re, ofReal_re, ofReal_im]
    rcases hb with ⟨B₀, hB₀⟩
    let B : ℝ := max 0 B₀
    have hB_nn : 0 ≤ B := le_max_left 0 B₀
    let M_g : ℝ := (Fintype.card S₀ : ℝ) * B
    have hg_bdd : ∀ z ∈ verticalClosedStrip 0 1, ‖g z‖ ≤ M_g := by
      intro z hz
      have hGz_le : ‖G z‖ ≤ B :=
        (hB₀ ⟨z, hz, rfl⟩).trans (le_max_right 0 B₀)
      have hγ_re_nn : 0 ≤ (γ z).re := by
        rw [hγ_re z]
        have h1p0 : 0 ≤ 1 - p₀⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hp₀)
        have h1p1 : 0 ≤ 1 - p₁⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hp₁)
        have hz0 : 0 ≤ 1 - z.re := sub_nonneg.mpr hz.2
        exact add_nonneg (mul_nonneg hz0 h1p0) (mul_nonneg hz.1 h1p1)
      dsimp only [g, M_g]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i : S₀, ‖((w i : ℂ) ^ (γ z)) * inner ℂ (f i) (G z (e i))‖
          ≤ ∑ _i : S₀, B := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hw_pos i)]
            have hw_rpow_le1 : (w i) ^ (γ z).re ≤ 1 :=
              (Real.rpow_le_rpow (hw_pos i).le (hw_le1 i) hγ_re_nn).trans_eq (Real.one_rpow _)
            have hinner_le : ‖inner ℂ (f i) (G z (e i))‖ ≤ B := by
              calc ‖inner ℂ (f i) (G z (e i))‖
                  ≤ ‖f i‖ * ‖G z (e i)‖ := norm_inner_le_norm _ _
                _ ≤ 1 * (‖G z‖ * ‖e i‖) := by
                    rw [hf_orth.1 i]
                    exact mul_le_mul_of_nonneg_left ((G z).le_opNorm (e i)) zero_le_one
                _ = ‖G z‖ := by rw [he_orth.1 i, mul_one, one_mul]
                _ ≤ B := hGz_le
            calc (w i) ^ (γ z).re * ‖inner ℂ (f i) (G z (e i))‖
                ≤ 1 * B := mul_le_mul hw_rpow_le1 hinner_le (norm_nonneg _) zero_le_one
              _ = B := one_mul B
        _ = (Fintype.card S₀ : ℝ) * B := by simp
    have hgθ_val : ‖g θ‖ = c := by
      have hγθ : γ θ = ((1 - pθ⁻¹ : ℝ) : ℂ) := by
        dsimp only [γ]
        have hreal : (1 - θ) * (1 - p₀⁻¹) + θ * (1 - p₁⁻¹) = 1 - pθ⁻¹ := by
          have hpθ' : pθ⁻¹ = (1 - θ) * p₀⁻¹ + θ * p₁⁻¹ := by
            simpa [one_div, div_eq_mul_inv] using hpθ
          linarith
        push_cast [← hreal]
        ring
      have hgθ_eq : g θ = (c : ℂ) := by
        dsimp only [g]
        rw [hγθ]
        have hterm : ∀ i : S₀,
            ((w i : ℂ) ^ ((1 - pθ⁻¹ : ℝ) : ℂ)) * inner ℂ (f i) (G θ (e i)) =
              ((c * w i : ℝ) : ℂ) := by
          intro i
          have hi_pos : 0 < s i.1 := (Finset.mem_filter.mp i.2).2
          have hinner_i : inner ℂ (f i) (G θ (e i)) = (s i.1 : ℂ) := by
            dsimp only [f, e]
            rw [inner_smul_left, inner_self_eq_norm_sq_to_K, hb₀_norm i.1]
            simp only [map_inv₀, conj_ofReal]
            have hsi_ne : (s i.1 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hi_pos.ne'
            field_simp [hsi_ne]
            norm_cast
          rw [hinner_i, ← ofReal_cpow (hw_pos i).le, ← ofReal_mul]
          congr 1
          dsimp only [w]
          have hsc_pos : 0 < s i.1 / c := div_pos hi_pos hc_pos
          rw [← Real.rpow_mul hsc_pos.le]
          have hexp : pθ * (1 - pθ⁻¹) = pθ - 1 := by
            rw [mul_sub, mul_one, mul_inv_cancel₀ hpθ_pos.ne']
          rw [hexp]
          calc (s i.1 / c) ^ (pθ - 1) * s i.1
              = c * ((s i.1 / c) ^ (pθ - 1) * (s i.1 / c) ^ (1 : ℝ)) := by
                  rw [Real.rpow_one]; field_simp [hc_pos.ne']
            _ = c * (s i.1 / c) ^ pθ := by
                  rw [← Real.rpow_add hsc_pos, sub_add_cancel]
        simp_rw [hterm]
        rw [← ofReal_sum, ← Finset.mul_sum, hw_sum, mul_one]
      rw [hgθ_eq, Complex.norm_of_nonneg hc_pos.le]
    have hg_bd0 : ∀ t : ℝ, ‖g (I * t)‖ ≤ schattenNorm p₀ (G (I * t)) := by
      intro t
      have hre0 : (γ (I * t)).re = 1 - p₀⁻¹ := by
        rw [hγ_re (I * t)]
        simp
      refine (norm_sum_le _ _).trans ?_
      have hsum_eq : ∑ i : S₀, ‖((w i : ℂ) ^ (γ (I * t))) * inner ℂ (f i) (G (I * t) (e i))‖ =
          ∑ i : S₀, (w i) ^ (1 - p₀⁻¹) * ‖inner ℂ (f i) (G (I * t) (e i))‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hw_pos i), hre0]
      rw [hsum_eq]
      exact hduality he_orth hf_orth hw_pos hw_sum hp₀ (G (I * t))
    have hg_bd1 : ∀ t : ℝ, ‖g (1 + I * t)‖ ≤ schattenNorm p₁ (G (1 + I * t)) := by
      intro t
      have hre1 : (γ (1 + I * t)).re = 1 - p₁⁻¹ := by
        rw [hγ_re (1 + I * t)]
        simp
      refine (norm_sum_le _ _).trans ?_
      have hsum_eq : ∑ i : S₀, ‖((w i : ℂ) ^ (γ (1 + I * t))) * inner ℂ (f i) (G (1 + I * t) (e i))‖ =
          ∑ i : S₀, (w i) ^ (1 - p₁⁻¹) * ‖inner ℂ (f i) (G (1 + I * t) (e i))‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hw_pos i), hre1]
      rw [hsum_eq]
      exact hduality he_orth hf_orth hw_pos hw_sum hp₁ (G (1 + I * t))
    exact ⟨g, hg_diff, hg_cont, ⟨M_g, mul_nonneg (Nat.cast_nonneg _) hB_nn, hg_bdd⟩,
      hc_pos, hgθ_val, hg_bd0, hg_bd1⟩
  
  have hs2 : ∀ {h : ℂ → ℂ} {r ε : ℝ},
      DifferentiableOn ℂ h (Metric.ball 0 1) → h 0 ≠ 0 →
      r ∈ Set.Ioo (0 : ℝ) 1 → 0 < ε →
      Real.log ‖h 0‖ ≤
        (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi),
          Real.log (max ‖h ((r : ℂ) * Complex.exp (Complex.I * φ))‖ ε) := by
    clear hs1 G hd hb hθ hp₀ hp₁ hpθ hGθ hα hβ p₀ p₁ pθ θ
    intro h r ε hh hh0 hr hε
    have hr_pos : 0 < r := hr.1
    have hr_lt : r < 1 := hr.2
    have hr_ne : r ≠ 0 := hr_pos.ne'
    have habs_r : |r| = r := abs_of_pos hr_pos
    have hh_ana : AnalyticOnNhd ℂ h (Metric.ball 0 1) := hh.analyticOnNhd Metric.isOpen_ball
    have hsub : Metric.closedBall (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
      rw [habs_r]
      exact Metric.closedBall_subset_ball hr_lt
    have h₁h : AnalyticOnNhd ℂ h (Metric.closedBall 0 |r|) := hh_ana.mono hsub
    have hjensen := AnalyticOnNhd.circleAverage_log_norm hr_ne h₁h hh0
    have hdiv_nonneg :
        0 ≤ ∑ᶠ (u : ℂ), ↑((MeromorphicOn.divisor h (Metric.closedBall 0 |r|)) u) *
          Real.log (r * ‖(0 : ℂ) - u‖⁻¹) := by
      apply finsum_nonneg
      intro u
      have hd_nn : 0 ≤ (MeromorphicOn.divisor h (Metric.closedBall 0 |r|)) u :=
        MeromorphicOn.AnalyticOnNhd.divisor_nonneg h₁h u
      have hd_cast : (0 : ℝ) ≤ ↑((MeromorphicOn.divisor h (Metric.closedBall 0 |r|)) u) := by
        exact_mod_cast hd_nn
      by_cases hu0 : u = 0
      · subst hu0; simp
      · by_cases humem : u ∈ Metric.closedBall (0 : ℂ) |r|
        · have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
          have hu_norm_le : ‖u‖ ≤ r := by
            simpa [Metric.mem_closedBall, dist_zero_right, habs_r] using humem
          have h_one_le : 1 ≤ r * ‖(0 : ℂ) - u‖⁻¹ := by
            rw [zero_sub, norm_neg, le_mul_inv_iff₀ hu_norm_pos, one_mul]
            exact hu_norm_le
          exact mul_nonneg hd_cast (Real.log_nonneg h_one_le)
        · have hd_zero : (MeromorphicOn.divisor h (Metric.closedBall 0 |r|)) u = 0 :=
            (MeromorphicOn.divisor h (Metric.closedBall 0 |r|)).apply_eq_zero_of_notMem humem
          simp [hd_zero]
    have hlog_le_avg : Real.log ‖h 0‖ ≤ Real.circleAverage (fun x => Real.log ‖h x‖) 0 r := by
      linarith [hjensen]
    have hisol : ∀ w ∈ Metric.closedBall (0 : ℂ) |r|,
        ∃ δ > 0, ∀ z ∈ Metric.ball w δ, z ≠ w → h z ≠ 0 := by
      intro w hw
      have hnot_freq : ¬ ∃ᶠ z in nhdsWithin w {w}ᶜ, h z = 0 := by
        intro hfreq
        have heq0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
          hh_ana (convex_ball (0 : ℂ) 1).isPreconnected (hsub hw) hfreq
          (Metric.mem_ball_self zero_lt_one)
        exact hh0 heq0
      rw [Filter.not_frequently, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hnot_freq
      rcases hnot_freq with ⟨δ, hδ_pos, hδ⟩
      refine ⟨δ, hδ_pos, fun z hz hzw => hδ hz hzw⟩
    choose δ hδ_pos hδ_ne using hisol
    let U : Metric.closedBall (0 : ℂ) |r| → Set ℂ := fun w => Metric.ball (w : ℂ) (δ w.1 w.2)
    have hcover : Metric.closedBall (0 : ℂ) |r| ⊆ ⋃ w, U w := by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hδ_pos z hz)⟩
    rcases (isCompact_closedBall (0 : ℂ) |r|).elim_finite_subcover U
      (fun w => Metric.isOpen_ball) hcover with ⟨t, ht⟩
    let Z_r : Set ℂ := {w ∈ Metric.sphere (0 : ℂ) |r| | h w = 0}
    have hZ_sub : Z_r ⊆ ⋃ w ∈ t, ({(w : ℂ)} : Set ℂ) := by
      intro z hz
      have hz_cb : z ∈ Metric.closedBall (0 : ℂ) |r| := Metric.sphere_subset_closedBall hz.1
      rcases Set.mem_iUnion₂.mp (ht hz_cb) with ⟨w, hwt, hzw⟩
      refine Set.mem_iUnion₂.mpr ⟨w, hwt, ?_⟩
      by_contra hne
      exact hδ_ne w.1 w.2 z hzw hne hz.2
    have hZ_fin : Z_r.Finite :=
      (t.finite_toSet.biUnion fun w _ => Set.finite_singleton (w : ℂ)).subset hZ_sub
    have hpre_cnt : (circleMap (0 : ℂ) r ⁻¹' Z_r).Countable :=
      hZ_fin.countable.preimage_circleMap 0 hr_ne
    have hpre_null : volume (circleMap (0 : ℂ) r ⁻¹' Z_r) = 0 := hpre_cnt.measure_zero volume
    have hae_univ : ∀ᵐ φ ∂volume,
        Real.log ‖h (circleMap 0 r φ)‖ ≤ Real.log (max ‖h (circleMap 0 r φ)‖ ε) := by
      rw [ae_iff]
      refine measure_mono_null (fun φ hφ => ?_) hpre_null
      have hmem_sph : circleMap (0 : ℂ) r φ ∈ Metric.sphere (0 : ℂ) |r| :=
        circleMap_mem_sphere' 0 r φ
      by_contra hmem_Z
      have hnz : h (circleMap 0 r φ) ≠ 0 := fun hz0 => hmem_Z ⟨hmem_sph, hz0⟩
      have hpos : 0 < ‖h (circleMap 0 r φ)‖ := norm_pos_iff.mpr hnz
      exact hφ (Real.log_le_log hpos (le_max_left _ _))
    have hae_restrict :
        (fun φ => Real.log ‖h (circleMap 0 r φ)‖) ≤ᵐ[volume.restrict (Set.Icc 0 (2 * Real.pi))]
          (fun φ => Real.log (max ‖h (circleMap 0 r φ)‖ ε)) :=
      ae_restrict_of_ae hae_univ
    have hint_lhs : IntervalIntegrable (fun φ => Real.log ‖h (circleMap 0 r φ)‖)
        volume 0 (2 * Real.pi) :=
      (h₁h.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    have hcont_rhs : Continuous (fun φ : ℝ => Real.log (max ‖h (circleMap 0 r φ)‖ ε)) := by
      have hcont_cm : Continuous (circleMap (0 : ℂ) r) := continuous_circleMap 0 r
      have hcont_hcm : Continuous (fun φ : ℝ => h (circleMap 0 r φ)) :=
        h₁h.continuousOn.comp_continuous hcont_cm (fun φ =>
          Metric.sphere_subset_closedBall (circleMap_mem_sphere' 0 r φ))
      have hcont_max : Continuous (fun φ : ℝ => max ‖h (circleMap 0 r φ)‖ ε) :=
        (continuous_norm.comp hcont_hcm).max continuous_const
      exact hcont_max.log (fun φ => (lt_of_lt_of_le hε (le_max_right _ _)).ne')
    have hint_rhs : IntervalIntegrable (fun φ => Real.log (max ‖h (circleMap 0 r φ)‖ ε))
        volume 0 (2 * Real.pi) :=
      hcont_rhs.intervalIntegrable 0 (2 * Real.pi)
    have hint_le :
        (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.log ‖h (circleMap 0 r φ)‖) ≤
          ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.log (max ‖h (circleMap 0 r φ)‖ ε) :=
      intervalIntegral.integral_mono_ae_restrict (by positivity) hint_lhs hint_rhs hae_restrict
    have havg_le :
        Real.circleAverage (fun x => Real.log ‖h x‖) 0 r ≤
          (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi),
            Real.log (max ‖h ((r : ℂ) * Complex.exp (Complex.I * φ))‖ ε) := by
      rw [Real.circleAverage_def, smul_eq_mul]
      have hcm_eq : ∀ φ : ℝ, circleMap (0 : ℂ) r φ = (r : ℂ) * Complex.exp (Complex.I * φ) := by
        intro φ
        simp [circleMap, mul_comm Complex.I]
      simp_rw [← hcm_eq]
      exact mul_le_mul_of_nonneg_left hint_le (by positivity)
    exact hlog_le_avg.trans havg_le
  
  have hs3 : (∀ t : ℝ, 0 < hirschmanAlpha θ t) ∧ Integrable (hirschmanAlpha θ) ∧
      (∀ t : ℝ, 0 < hirschmanBeta θ t) ∧ Integrable (hirschmanBeta θ) ∧
      ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ (Metric.ball 0 1) ∧
        (∀ w ∈ Metric.ball (0 : ℂ) 1, Φ w ∈ verticalStrip 0 1) ∧
        Φ 0 = (θ : ℂ) ∧
        ∀ (ψ : ℂ → ℝ), ContinuousOn ψ (verticalClosedStrip 0 1) →
          (∃ C : ℝ, ∀ z ∈ verticalClosedStrip 0 1, |ψ z| ≤ C) →
          Filter.Tendsto (fun n : ℕ =>
            (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi),
              ψ (Φ (((1 - ((n : ℝ) + 2)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * φ))))
            Filter.atTop
            (nhds (∫ t : ℝ, (hirschmanAlpha θ t * ((1 - θ) * ψ (I * t)) +
              hirschmanBeta θ t * (θ * ψ (1 + I * t))))) := by
    clear hs1 hs2 G hd hb hp₀ hp₁ hpθ hGθ hα hβ p₀ p₁ pθ
    have hθ0 : 0 < θ := hθ.1
    have hθ1 : θ < 1 := hθ.2
    have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
    have hπ_pos : 0 < Real.pi := Real.pi_pos
    have hπ_ne : Real.pi ≠ 0 := hπ_pos.ne'
    have hπθ_pos : 0 < Real.pi * θ := mul_pos hπ_pos hθ0
    have hπθ_lt : Real.pi * θ < Real.pi := by nlinarith
    let s : ℝ := Real.sin (Real.pi * θ)
    let c_θ : ℝ := Real.cos (Real.pi * θ)
    have hs_pos : 0 < s := Real.sin_pos_of_pos_of_lt_pi hπθ_pos hπθ_lt
    have hs_ne : s ≠ 0 := hs_pos.ne'
    have hsc_sq : s ^ 2 + c_θ ^ 2 = 1 := Real.sin_sq_add_cos_sq (Real.pi * θ)
    have hc_lt1 : c_θ < 1 := by nlinarith
    have hc_gt_neg1 : -1 < c_θ := by nlinarith
    have hcosh_sub_pos : ∀ t : ℝ, 0 < Real.cosh (Real.pi * t) - c_θ := fun t => by
      linarith [Real.one_le_cosh (Real.pi * t)]
    have hcosh_add_pos : ∀ t : ℝ, 0 < Real.cosh (Real.pi * t) + c_θ := fun t => by
      linarith [Real.one_le_cosh (Real.pi * t)]
    have hα_pos : ∀ t : ℝ, 0 < hirschmanAlpha θ t := by
      intro t
      unfold hirschmanAlpha
      exact div_pos hs_pos (mul_pos (mul_pos two_pos h1θ) (hcosh_sub_pos t))
    have hβ_pos : ∀ t : ℝ, 0 < hirschmanBeta θ t := by
      intro t
      unfold hirschmanBeta
      exact div_pos hs_pos (mul_pos (mul_pos two_pos hθ0) (hcosh_add_pos t))
    let u₁ : ℝ → ℝ := fun t => (Real.exp (-Real.pi * t) + c_θ) / s
    let φ₁ : ℝ → ℝ := fun t => Real.pi - 2 * Real.arctan (u₁ t)
    let u₀ : ℝ → ℝ := fun t => (Real.exp (-Real.pi * t) - c_θ) / s
    let φ₀ : ℝ → ℝ := fun t => Real.pi + 2 * Real.arctan (u₀ t)
    have hexp_prod : ∀ t : ℝ, Real.exp (-(Real.pi * t)) * Real.exp (Real.pi * t) = 1 := fun t => by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hu₁_sq_id : ∀ t : ℝ,
        s ^ 2 * (1 + u₁ t ^ 2) = 2 * Real.exp (-Real.pi * t) * (Real.cosh (Real.pi * t) + c_θ) := by
      intro t
      dsimp only [u₁]
      rw [Real.cosh_eq, show (-Real.pi * t : ℝ) = -(Real.pi * t) by ring]
      field_simp [hs_ne]
      linear_combination hsc_sq - hexp_prod t
    have hu₀_sq_id : ∀ t : ℝ,
        s ^ 2 * (1 + u₀ t ^ 2) = 2 * Real.exp (-Real.pi * t) * (Real.cosh (Real.pi * t) - c_θ) := by
      intro t
      dsimp only [u₀]
      rw [Real.cosh_eq, show (-Real.pi * t : ℝ) = -(Real.pi * t) by ring]
      field_simp [hs_ne]
      linear_combination hsc_sq - hexp_prod t
    have hφ₁_deriv : ∀ t : ℝ, HasDerivAt φ₁ (2 * Real.pi * θ * hirschmanBeta θ t) t := by
      intro t
      have hd_lin : HasDerivAt (fun x : ℝ => -Real.pi * x) (-Real.pi) t := by
        simpa using (hasDerivAt_id t).const_mul (-Real.pi)
      have hd_exp : HasDerivAt (fun x : ℝ => Real.exp (-Real.pi * x))
          (Real.exp (-Real.pi * t) * (-Real.pi)) t := hd_lin.exp
      have hd_u₁ : HasDerivAt u₁ ((Real.exp (-Real.pi * t) * (-Real.pi)) / s) t :=
        (hd_exp.add_const c_θ).div_const s
      have hd_φ₁ : HasDerivAt φ₁
          (0 - 2 * ((1 / (1 + u₁ t ^ 2)) * ((Real.exp (-Real.pi * t) * (-Real.pi)) / s))) t :=
        (hasDerivAt_const t Real.pi).sub (((Real.hasDerivAt_arctan (u₁ t)).comp t hd_u₁).const_mul 2)
      refine hd_φ₁.congr_deriv ?_
      unfold hirschmanBeta
      have hθ_ne : θ ≠ 0 := hθ0.ne'
      have hden_ne : Real.cosh (Real.pi * t) + c_θ ≠ 0 := (hcosh_add_pos t).ne'
      have hexp_ne : Real.exp (-Real.pi * t) ≠ 0 := Real.exp_ne_zero _
      have hu_div : 1 + u₁ t ^ 2 =
          2 * Real.exp (-Real.pi * t) * (Real.cosh (Real.pi * t) + c_θ) / s ^ 2 := by
        rw [eq_div_iff (pow_ne_zero 2 hs_ne)]
        linarith [hu₁_sq_id t]
      change 0 - 2 * (1 / (1 + u₁ t ^ 2) * (Real.exp (-Real.pi * t) * -Real.pi / s)) =
        2 * Real.pi * θ * (s / (2 * θ * (Real.cosh (Real.pi * t) + c_θ)))
      rw [hu_div]
      field_simp [hs_ne, hθ_ne, hden_ne, hexp_ne]
      ring
    have hφ₀_deriv : ∀ t : ℝ, HasDerivAt φ₀ (-(2 * Real.pi * (1 - θ) * hirschmanAlpha θ t)) t := by
      intro t
      have hd_lin : HasDerivAt (fun x : ℝ => -Real.pi * x) (-Real.pi) t := by
        simpa using (hasDerivAt_id t).const_mul (-Real.pi)
      have hd_exp : HasDerivAt (fun x : ℝ => Real.exp (-Real.pi * x))
          (Real.exp (-Real.pi * t) * (-Real.pi)) t := hd_lin.exp
      have hd_u₀ : HasDerivAt u₀ ((Real.exp (-Real.pi * t) * (-Real.pi)) / s) t :=
        (hd_exp.sub_const c_θ).div_const s
      have hd_φ₀ : HasDerivAt φ₀
          (0 + 2 * ((1 / (1 + u₀ t ^ 2)) * ((Real.exp (-Real.pi * t) * (-Real.pi)) / s))) t :=
        (hasDerivAt_const t Real.pi).add (((Real.hasDerivAt_arctan (u₀ t)).comp t hd_u₀).const_mul 2)
      refine hd_φ₀.congr_deriv ?_
      unfold hirschmanAlpha
      have h1θ_ne : 1 - θ ≠ 0 := h1θ.ne'
      have hden_ne : Real.cosh (Real.pi * t) - c_θ ≠ 0 := (hcosh_sub_pos t).ne'
      have hexp_ne : Real.exp (-Real.pi * t) ≠ 0 := Real.exp_ne_zero _
      have hu_div : 1 + u₀ t ^ 2 =
          2 * Real.exp (-Real.pi * t) * (Real.cosh (Real.pi * t) - c_θ) / s ^ 2 := by
        rw [eq_div_iff (pow_ne_zero 2 hs_ne)]
        linarith [hu₀_sq_id t]
      change 0 + 2 * (1 / (1 + u₀ t ^ 2) * (Real.exp (-Real.pi * t) * -Real.pi / s)) =
        -(2 * Real.pi * (1 - θ) * (s / (2 * (1 - θ) * (Real.cosh (Real.pi * t) - c_θ))))
      rw [hu_div]
      field_simp [hs_ne, h1θ_ne, hden_ne, hexp_ne]
      ring
    have hφ₁_diff : Differentiable ℝ φ₁ := fun t => (hφ₁_deriv t).differentiableAt
    have hφ₀_diff : Differentiable ℝ φ₀ := fun t => (hφ₀_deriv t).differentiableAt
    have hφ₁_mono : StrictMono φ₁ := by
      apply strictMono_of_deriv_pos
      intro t
      rw [(hφ₁_deriv t).deriv]
      exact mul_pos (mul_pos (mul_pos two_pos hπ_pos) hθ0) (hβ_pos t)
    have hφ₀_anti : StrictAnti φ₀ := by
      have hneg_mono : StrictMono (-φ₀) := by
        apply strictMono_of_deriv_pos
        intro t
        rw [((hφ₀_deriv t).neg).deriv, neg_neg]
        exact mul_pos (mul_pos (mul_pos two_pos hπ_pos) h1θ) (hα_pos t)
      intro a b hab
      exact neg_lt_neg_iff.mp (hneg_mono hab)
    have hexp_atBot : Filter.Tendsto (fun t : ℝ => Real.exp (-Real.pi * t))
        Filter.atBot Filter.atTop := by
      have hlin : Filter.Tendsto (fun t : ℝ => -Real.pi * t) Filter.atBot Filter.atTop := by
        simpa [mul_neg, neg_mul] using
          Filter.Tendsto.const_mul_atTop hπ_pos Filter.tendsto_neg_atBot_atTop
      exact Real.tendsto_exp_atTop.comp hlin
    have hu₁_atBot : Filter.Tendsto u₁ Filter.atBot Filter.atTop := by
      have h1 : Filter.Tendsto (fun t => Real.exp (-Real.pi * t) + c_θ) Filter.atBot Filter.atTop :=
        Filter.Tendsto.atTop_add hexp_atBot tendsto_const_nhds
      have heq : u₁ = fun t => (Real.exp (-Real.pi * t) + c_θ) * s⁻¹ := by ext t; rfl
      rw [heq]
      exact Filter.Tendsto.atTop_mul_const (inv_pos.mpr hs_pos) h1
    have hu₀_atBot : Filter.Tendsto u₀ Filter.atBot Filter.atTop := by
      have h1 : Filter.Tendsto (fun t => Real.exp (-Real.pi * t) + (-c_θ)) Filter.atBot Filter.atTop :=
        Filter.Tendsto.atTop_add hexp_atBot tendsto_const_nhds
      have heq : u₀ = fun t => (Real.exp (-Real.pi * t) + (-c_θ)) * s⁻¹ := by
        ext t; dsimp only [u₀]; ring
      rw [heq]
      exact Filter.Tendsto.atTop_mul_const (inv_pos.mpr hs_pos) h1
    have hφ₁_atBot : Filter.Tendsto φ₁ Filter.atBot (nhds 0) := by
      have harc : Filter.Tendsto (fun t => Real.arctan (u₁ t)) Filter.atBot (nhds (Real.pi / 2)) :=
        (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hu₁_atBot
      have h := (tendsto_const_nhds (x := Real.pi)).sub (harc.const_mul 2)
      have hval : Real.pi - 2 * (Real.pi / 2) = 0 := by ring
      rwa [hval] at h
    have hφ₀_atBot : Filter.Tendsto φ₀ Filter.atBot (nhds (2 * Real.pi)) := by
      have harc : Filter.Tendsto (fun t => Real.arctan (u₀ t)) Filter.atBot (nhds (Real.pi / 2)) :=
        (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hu₀_atBot
      have h := (tendsto_const_nhds (x := Real.pi)).add (harc.const_mul 2)
      have hval : Real.pi + 2 * (Real.pi / 2) = 2 * Real.pi := by ring
      rwa [hval] at h
    have hexp_atTop : Filter.Tendsto (fun t : ℝ => Real.exp (-Real.pi * t))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun t : ℝ => -(Real.pi * t)) Filter.atTop Filter.atBot :=
        Filter.tendsto_neg_atTop_atBot.comp
          (Filter.Tendsto.const_mul_atTop hπ_pos Filter.tendsto_id)
      have hlin : Filter.Tendsto (fun t : ℝ => -Real.pi * t) Filter.atTop Filter.atBot :=
        h1.congr (fun t => by ring)
      exact Real.tendsto_exp_atBot.comp hlin
    have hcot_eq : c_θ / s = Real.tan (Real.pi / 2 - Real.pi * θ) := by
      rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    have harctan_cot : Real.arctan (c_θ / s) = Real.pi / 2 - Real.pi * θ := by
      rw [hcot_eq]
      exact Real.arctan_tan (by linarith) (by linarith)
    have harctan_neg_cot : Real.arctan (-c_θ / s) = Real.pi * θ - Real.pi / 2 := by
      rw [neg_div, Real.arctan_neg, harctan_cot]
      ring
    have hφ₁_atTop : Filter.Tendsto φ₁ Filter.atTop (nhds (2 * Real.pi * θ)) := by
      have hu : Filter.Tendsto u₁ Filter.atTop (nhds (c_θ / s)) := by
        simpa [u₁] using (hexp_atTop.add_const c_θ).div_const s
      have h := (tendsto_const_nhds (x := Real.pi)).sub
        ((Real.continuous_arctan.continuousAt.tendsto.comp hu).const_mul 2)
      rw [harctan_cot] at h
      have hval : Real.pi - 2 * (Real.pi / 2 - Real.pi * θ) = 2 * Real.pi * θ := by ring
      rwa [hval] at h
    have hφ₀_atTop : Filter.Tendsto φ₀ Filter.atTop (nhds (2 * Real.pi * θ)) := by
      have hu : Filter.Tendsto u₀ Filter.atTop (nhds (-c_θ / s)) := by
        simpa [u₀, zero_sub] using (hexp_atTop.sub_const c_θ).div_const s
      have h := (tendsto_const_nhds (x := Real.pi)).add
        ((Real.continuous_arctan.continuousAt.tendsto.comp hu).const_mul 2)
      rw [harctan_neg_cot] at h
      have hval : Real.pi + 2 * (Real.pi * θ - Real.pi / 2) = 2 * Real.pi * θ := by ring
      rwa [hval] at h
    have hφ₁_img : φ₁ '' Set.univ = Set.Ioo 0 (2 * Real.pi * θ) := by
      ext y
      constructor
      · rintro ⟨t, -, rfl⟩
        constructor
        · by_contra hle
          have hlt : φ₁ (t - 1) < 0 := (hφ₁_mono (by linarith)).trans_le (not_lt.mp hle)
          rcases ((hφ₁_atBot.eventually (lt_mem_nhds hlt)).and
            (Filter.eventually_le_atBot (t - 1))).exists with ⟨x, hx1, hx2⟩
          exact absurd (hφ₁_mono.monotone hx2) (not_le.mpr hx1)
        · by_contra hge
          have hgt : 2 * Real.pi * θ < φ₁ (t + 1) :=
            (not_lt.mp hge).trans_lt (hφ₁_mono (by linarith))
          rcases ((hφ₁_atTop.eventually (gt_mem_nhds hgt)).and
            (Filter.eventually_ge_atTop (t + 1))).exists with ⟨x, hx1, hx2⟩
          exact absurd (hφ₁_mono.monotone hx2) (not_le.mpr hx1)
      · rintro ⟨hy0, hy1⟩
        rcases (hφ₁_atBot.eventually (gt_mem_nhds hy0)).exists with ⟨a, ha⟩
        rcases (hφ₁_atTop.eventually (lt_mem_nhds hy1)).exists with ⟨b, hb⟩
        have hab : a ≤ b := by
          by_contra hba
          exact absurd (ha.trans hb) (not_lt.mpr (hφ₁_mono.monotone (not_le.mp hba).le))
        rcases intermediate_value_Icc hab hφ₁_diff.continuous.continuousOn ⟨ha.le, hb.le⟩
          with ⟨t, -, ht⟩
        exact ⟨t, Set.mem_univ t, ht⟩
    have hφ₀_img : φ₀ '' Set.univ = Set.Ioo (2 * Real.pi * θ) (2 * Real.pi) := by
      ext y
      constructor
      · rintro ⟨t, -, rfl⟩
        constructor
        · by_contra hle
          have hlt : φ₀ (t + 1) < 2 * Real.pi * θ :=
            (hφ₀_anti (by linarith)).trans_le (not_lt.mp hle)
          rcases ((hφ₀_atTop.eventually (lt_mem_nhds hlt)).and
            (Filter.eventually_ge_atTop (t + 1))).exists with ⟨x, hx1, hx2⟩
          exact absurd (hφ₀_anti.antitone hx2) (not_le.mpr hx1)
        · by_contra hge
          have hgt : 2 * Real.pi < φ₀ (t - 1) :=
            (not_lt.mp hge).trans_lt (hφ₀_anti (by linarith))
          rcases ((hφ₀_atBot.eventually (gt_mem_nhds hgt)).and
            (Filter.eventually_le_atBot (t - 1))).exists with ⟨x, hx1, hx2⟩
          exact absurd (hφ₀_anti.antitone hx2) (not_le.mpr hx1)
      · rintro ⟨hy0, hy1⟩
        rcases (hφ₀_atBot.eventually (lt_mem_nhds hy1)).exists with ⟨a, ha⟩
        rcases (hφ₀_atTop.eventually (gt_mem_nhds hy0)).exists with ⟨b, hb⟩
        have hab : a ≤ b := by
          by_contra hba
          exact absurd (hb.trans ha) (not_lt.mpr (hφ₀_anti.antitone (not_le.mp hba).le))
        rcases intermediate_value_Icc' hab hφ₀_diff.continuous.continuousOn ⟨hb.le, ha.le⟩
          with ⟨t, -, ht⟩
        exact ⟨t, Set.mem_univ t, ht⟩
    have hβ_int : Integrable (hirschmanBeta θ) := by
      have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (φ₁ '' Set.univ) volume := by
        rw [hφ₁_img]
        exact (continuousOn_const.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
      have h2 := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
        (fun t _ => (hφ₁_deriv t).hasDerivWithinAt) hφ₁_mono.injective.injOn
        (fun _ : ℝ => (1 : ℝ))).mp h1
      rw [integrableOn_univ] at h2
      have h3 : Integrable (fun t => 2 * Real.pi * θ * hirschmanBeta θ t) := by
        refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
        have hd_pos : 0 < 2 * Real.pi * θ * hirschmanBeta θ t :=
          mul_pos (mul_pos (mul_pos two_pos hπ_pos) hθ0) (hβ_pos t)
        simp [abs_of_pos hd_pos]
      have h4 := h3.const_mul ((2 * Real.pi * θ)⁻¹)
      refine h4.congr (Filter.Eventually.of_forall fun t => ?_)
      have hne : 2 * Real.pi * θ ≠ 0 := (mul_pos (mul_pos two_pos hπ_pos) hθ0).ne'
      dsimp only
      field_simp [hne]
    have hα_int : Integrable (hirschmanAlpha θ) := by
      have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (φ₀ '' Set.univ) volume := by
        rw [hφ₀_img]
        exact (continuousOn_const.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
      have h2 := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
        (fun t _ => (hφ₀_deriv t).hasDerivWithinAt) hφ₀_anti.injective.injOn
        (fun _ : ℝ => (1 : ℝ))).mp h1
      rw [integrableOn_univ] at h2
      have h3 : Integrable (fun t => 2 * Real.pi * (1 - θ) * hirschmanAlpha θ t) := by
        refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
        have hd_pos : 0 < 2 * Real.pi * (1 - θ) * hirschmanAlpha θ t :=
          mul_pos (mul_pos (mul_pos two_pos hπ_pos) h1θ) (hα_pos t)
        simp [abs_neg, abs_of_pos hd_pos]
      have h4 := h3.const_mul ((2 * Real.pi * (1 - θ))⁻¹)
      refine h4.congr (Filter.Eventually.of_forall fun t => ?_)
      have hne : 2 * Real.pi * (1 - θ) ≠ 0 := (mul_pos (mul_pos two_pos hπ_pos) h1θ).ne'
      dsimp only
      field_simp [hne]
    let η₀ : ℂ := (s : ℂ) - (c_θ : ℂ) * I
    let η : ℂ → ℂ := fun w => (η₀ + star η₀ * w) / (1 - w)
    let Φ : ℂ → ℂ := fun w => (2⁻¹ : ℂ) + Complex.log (η w) / ((Real.pi : ℂ) * I)
    have h1w_ne_ball : ∀ w ∈ Metric.ball (0 : ℂ) 1, 1 - w ≠ 0 := by
      intro w hw h
      have hw_lt : ‖w‖ < 1 := by simpa using hw
      have hw1 : w = 1 := (sub_eq_zero.mp h).symm
      simp [hw1] at hw_lt
    have hη_re_pos : ∀ w ∈ Metric.ball (0 : ℂ) 1, 0 < (η w).re := by
      intro w hw
      have hw_lt : ‖w‖ < 1 := by simpa using hw
      have hw_sq_lt : Complex.normSq w < 1 := by
        rw [Complex.normSq_eq_norm_sq]
        have := norm_nonneg w
        nlinarith
      have hden_pos : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr (h1w_ne_ball w hw)
      dsimp only [η, η₀]
      rw [Complex.div_re, ← add_div]
      have hnum : (↑s - ↑c_θ * I + star (↑s - ↑c_θ * I) * w).re * (1 - w).re +
          (↑s - ↑c_θ * I + star (↑s - ↑c_θ * I) * w).im * (1 - w).im =
          s * (1 - (w.re * w.re + w.im * w.im)) := by
        simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
          add_im, sub_im, mul_im, star_def, conj_re, conj_im, one_re, one_im]
        ring
      have hnsq : w.re * w.re + w.im * w.im = Complex.normSq w := (Complex.normSq_apply w).symm
      rw [hnum, hnsq]
      exact div_pos (mul_pos hs_pos (sub_pos.mpr hw_sq_lt)) hden_pos
    have hη_diff_at : ∀ w : ℂ, 1 - w ≠ 0 → DifferentiableAt ℂ η w := by
      intro w hne
      exact ((differentiableAt_const η₀).add
        ((differentiableAt_const (star η₀)).mul differentiableAt_id)).div
        ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id) hne
    have hΦ_diff : DifferentiableOn ℂ Φ (Metric.ball 0 1) := by
      intro w hw
      have hslit : η w ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (hη_re_pos w hw))
      have hd_at : DifferentiableAt ℂ Φ w :=
        (differentiableAt_const (2⁻¹ : ℂ)).add
          (((Complex.differentiableAt_log hslit).comp w (hη_diff_at w (h1w_ne_ball w hw))).div_const
            ((Real.pi : ℂ) * I))
      exact hd_at.differentiableWithinAt
    have hdiv_piI_re : ∀ z : ℂ, (z / ((Real.pi : ℂ) * I)).re = z.im / Real.pi := by
      intro z
      have hpiI : z / ((Real.pi : ℂ) * I) = (z * (-I)) / (Real.pi : ℂ) := by
        have hI_ne : (I : ℂ) ≠ 0 := I_ne_zero
        have hπc_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ_ne
        field_simp [hI_ne, hπc_ne]
        rw [I_sq]
        ring
      rw [hpiI, div_ofReal_re]
      simp [mul_re]
    have hΦ_maps : ∀ w ∈ Metric.ball (0 : ℂ) 1, Φ w ∈ verticalStrip 0 1 := by
      intro w hw
      have harg_abs : |(η w).arg| < Real.pi / 2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hη_re_pos w hw))
      rcases abs_lt.mp harg_abs with ⟨harg_gt, harg_lt⟩
      have hre : (Φ w).re = 2⁻¹ + (η w).arg / Real.pi := by
        dsimp only [Φ]
        rw [add_re, hdiv_piI_re, Complex.log_im]
        norm_num
      change 0 < (Φ w).re ∧ (Φ w).re < 1
      rw [hre]
      have hdiv_gt : -(2⁻¹ : ℝ) < (η w).arg / Real.pi := by
        rw [lt_div_iff₀ hπ_pos]
        linarith
      have hdiv_lt : (η w).arg / Real.pi < 2⁻¹ := by
        rw [div_lt_iff₀ hπ_pos]
        linarith
      constructor <;> linarith
    have hΦ0 : Φ 0 = (θ : ℂ) := by
      have hη0_exp : η 0 = Complex.exp (((Real.pi * θ - Real.pi / 2 : ℝ) : ℂ) * I) := by
        have h0 : η 0 = η₀ := by simp [η]
        rw [h0, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        have hcos : Real.cos (Real.pi * θ - Real.pi / 2) = s := by
          have heq : Real.pi * θ - Real.pi / 2 = -(Real.pi / 2 - Real.pi * θ) := by ring
          rw [heq, Real.cos_neg, Real.cos_pi_div_two_sub]
        have hsin : Real.sin (Real.pi * θ - Real.pi / 2) = -c_θ := by
          have heq : Real.pi * θ - Real.pi / 2 = -(Real.pi / 2 - Real.pi * θ) := by ring
          rw [heq, Real.sin_neg, Real.sin_pi_div_two_sub]
        dsimp only [η₀]
        rw [hcos, hsin]
        push_cast
        ring
      have him1 : -Real.pi < (((Real.pi * θ - Real.pi / 2 : ℝ) : ℂ) * I).im := by
        simp; linarith
      have him2 : (((Real.pi * θ - Real.pi / 2 : ℝ) : ℂ) * I).im ≤ Real.pi := by
        simp; linarith
      dsimp only [Φ]
      rw [hη0_exp, Complex.log_exp him1 him2]
      have hπc_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ_ne
      have hI_ne : (I : ℂ) ≠ 0 := I_ne_zero
      field_simp [hπc_ne, hI_ne]
      push_cast
      ring
    have hbd_φ₁ : ∀ t : ℝ,
        let w := Complex.exp (I * (φ₁ t : ℂ))
        1 - w ≠ 0 ∧ η w ∈ Complex.slitPlane ∧ Φ w = 1 + I * (t : ℂ) := by
      intro t
      dsimp only
      let w : ℂ := Complex.exp (I * (φ₁ t : ℂ))
      let α : ℝ := Real.arctan (u₁ t)
      let E : ℝ := Real.exp (-Real.pi * t)
      let cα : ℝ := Real.cos α
      have hcos_pos : 0 < cα := Real.cos_pos_of_mem_Ioo (Real.arctan_mem_Ioo _)
      have hcos_ne : (cα : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcos_pos.ne'
      have hsin_α : Real.sin α = u₁ t * cα := by
        have htan := Real.tan_arctan (u₁ t)
        rw [Real.tan_eq_sin_div_cos] at htan
        exact (div_eq_iff hcos_pos.ne').mp htan
      have hcos_sq_id : cα ^ 2 * (1 + u₁ t ^ 2) = 1 := by
        calc cα ^ 2 * (1 + u₁ t ^ 2)
            = cα ^ 2 + (u₁ t * cα) ^ 2 := by ring
          _ = Real.cos α ^ 2 + Real.sin α ^ 2 := by rw [← hsin_α]
          _ = 1 := Real.cos_sq_add_sin_sq α
      have h1_c : ((cα : ℂ) ^ 2) * (1 + (u₁ t : ℂ) ^ 2) = 1 := by
        exact_mod_cast hcos_sq_id
      have hw_eq : w = -((cα : ℂ) ^ 2 * (1 - (u₁ t : ℂ) * I) ^ 2) := by
        have hexp : w = Complex.exp (((Real.pi - 2 * α : ℝ) : ℂ) * I) := by
          dsimp only [w, φ₁, α]
          congr 1
          push_cast
          ring
        rw [hexp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_two_mul', Real.sin_two_mul, hsin_α]
        change ↑(-(cα ^ 2 - (u₁ t * cα) ^ 2)) + ↑(2 * (u₁ t * cα) * cα) * I =
          -((cα : ℂ) ^ 2 * (1 - (u₁ t : ℂ) * I) ^ 2)
        apply Complex.ext <;> simp [pow_two] <;> ring
      have h1w_eq : 1 - w = 2 * (cα : ℂ) ^ 2 * (1 - (u₁ t : ℂ) * I) := by
        have h1_sub : (1 : ℂ) - w = ((cα : ℂ) ^ 2) * (1 + (u₁ t : ℂ) ^ 2) -
            (-((cα : ℂ) ^ 2 * (1 - (u₁ t : ℂ) * I) ^ 2)) := by
          rw [h1_c, hw_eq]
        rw [h1_sub]
        apply Complex.ext <;> simp [pow_two] <;> ring
      have h1u_ne : (1 : ℂ) - (u₁ t : ℂ) * I ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
      have h1w_ne : 1 - w ≠ 0 := by
        rw [h1w_eq]
        exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hcos_ne)) h1u_ne
      have hη_val : η w = (E : ℂ) * I := by
        dsimp only [η]
        rw [div_eq_iff h1w_ne]
        have hη₀_bar : star η₀ = (s : ℂ) + (c_θ : ℂ) * I := by
          dsimp only [η₀]
          simp
        have hu_c : (u₁ t : ℂ) = ((E : ℂ) + (c_θ : ℂ)) / (s : ℂ) := by
          dsimp only [u₁, E]
          push_cast
          rfl
        have hsc_ne : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs_ne
        have hη₀_mul : η₀ = ((s : ℂ) - (c_θ : ℂ) * I) * (((cα : ℂ) ^ 2) * (1 + (u₁ t : ℂ) ^ 2)) := by
          rw [h1_c, mul_one]
        calc η₀ + star η₀ * w
            = ((s : ℂ) - (c_θ : ℂ) * I) * (((cα : ℂ) ^ 2) * (1 + (u₁ t : ℂ) ^ 2)) +
              ((s : ℂ) + (c_θ : ℂ) * I) * (-((cα : ℂ) ^ 2 * (1 - (u₁ t : ℂ) * I) ^ 2)) := by
                rw [← hη₀_mul, hη₀_bar, hw_eq]
          _ = ((E : ℂ) * I) * (2 * (cα : ℂ) ^ 2 * (1 - (u₁ t : ℂ) * I)) := by
                rw [hu_c]
                field_simp [hsc_ne]
                apply Complex.ext <;> simp [pow_two] <;> ring
          _ = ((E : ℂ) * I) * (1 - w) := by rw [← h1w_eq]
      have hslit : η w ∈ Complex.slitPlane := by
        have hE_ne : E ≠ 0 := Real.exp_ne_zero _
        rw [hη_val, Complex.mem_slitPlane_iff]
        exact Or.inr (by simp [hE_ne])
      have hΦ_val : Φ w = 1 + I * (t : ℂ) := by
        have hexp_E : ((E : ℂ) * I) = Complex.exp (↑(-Real.pi * t) + ↑(Real.pi / 2) * I) := by
          rw [Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
            ← Complex.ofReal_cos, ← Complex.ofReal_sin,
            Real.cos_pi_div_two, Real.sin_pi_div_two]
          simp [E]
        have him1 : -Real.pi < (↑(-Real.pi * t) + ↑(Real.pi / 2) * I).im := by
          simp; linarith
        have him2 : (↑(-Real.pi * t) + ↑(Real.pi / 2) * I).im ≤ Real.pi := by
          simp; linarith
        dsimp only [Φ]
        rw [hη_val, hexp_E, Complex.log_exp him1 him2]
        have hπc_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ_ne
        have hI_ne : (I : ℂ) ≠ 0 := I_ne_zero
        field_simp [hπc_ne, hI_ne]
        apply Complex.ext <;> simp <;> ring
      exact ⟨h1w_ne, hslit, hΦ_val⟩
    have hbd_φ₀ : ∀ t : ℝ,
        let w := Complex.exp (I * (φ₀ t : ℂ))
        1 - w ≠ 0 ∧ η w ∈ Complex.slitPlane ∧ Φ w = I * (t : ℂ) := by
      intro t
      dsimp only
      let w : ℂ := Complex.exp (I * (φ₀ t : ℂ))
      let β : ℝ := Real.arctan (u₀ t)
      let cβ : ℝ := Real.cos β
      let E : ℝ := Real.exp (-Real.pi * t)
      have hcos_pos : 0 < cβ := Real.cos_pos_of_mem_Ioo (Real.arctan_mem_Ioo _)
      have hcos_ne : (cβ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcos_pos.ne'
      have hsin_β : Real.sin β = u₀ t * cβ := by
        have htan := Real.tan_arctan (u₀ t)
        rw [Real.tan_eq_sin_div_cos] at htan
        exact (div_eq_iff hcos_pos.ne').mp htan
      have hcos_sq_id : cβ ^ 2 * (1 + u₀ t ^ 2) = 1 := by
        calc cβ ^ 2 * (1 + u₀ t ^ 2)
            = cβ ^ 2 + (u₀ t * cβ) ^ 2 := by ring
          _ = Real.cos β ^ 2 + Real.sin β ^ 2 := by rw [← hsin_β]
          _ = 1 := Real.cos_sq_add_sin_sq β
      have h1_c : ((cβ : ℂ) ^ 2) * (1 + (u₀ t : ℂ) ^ 2) = 1 := by
        exact_mod_cast hcos_sq_id
      have hw_eq : w = -((cβ : ℂ) ^ 2 * (1 + (u₀ t : ℂ) * I) ^ 2) := by
        have hexp : w = Complex.exp (((Real.pi + 2 * β : ℝ) : ℂ) * I) := by
          dsimp only [w, φ₀, β]
          congr 1
          push_cast
          ring
        have hcos_add : Real.cos (Real.pi + 2 * β) = -Real.cos (2 * β) := by
          rw [add_comm, Real.cos_add_pi]
        have hsin_add : Real.sin (Real.pi + 2 * β) = -Real.sin (2 * β) := by
          rw [add_comm, Real.sin_add_pi]
        rw [hexp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          hcos_add, hsin_add, Real.cos_two_mul', Real.sin_two_mul, hsin_β]
        change ↑(-(cβ ^ 2 - (u₀ t * cβ) ^ 2)) + ↑(-(2 * (u₀ t * cβ) * cβ)) * I =
          -((cβ : ℂ) ^ 2 * (1 + (u₀ t : ℂ) * I) ^ 2)
        apply Complex.ext <;> simp [pow_two] <;> ring
      have h1w_eq : 1 - w = 2 * (cβ : ℂ) ^ 2 * (1 + (u₀ t : ℂ) * I) := by
        have h1_sub : (1 : ℂ) - w = ((cβ : ℂ) ^ 2) * (1 + (u₀ t : ℂ) ^ 2) -
            (-((cβ : ℂ) ^ 2 * (1 + (u₀ t : ℂ) * I) ^ 2)) := by
          rw [h1_c, hw_eq]
        rw [h1_sub]
        apply Complex.ext <;> simp [pow_two] <;> ring
      have h1u_ne : (1 : ℂ) + (u₀ t : ℂ) * I ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
      have h1w_ne : 1 - w ≠ 0 := by
        rw [h1w_eq]
        exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hcos_ne)) h1u_ne
      have hη_val : η w = -((E : ℂ) * I) := by
        dsimp only [η]
        rw [div_eq_iff h1w_ne]
        have hη₀_bar : star η₀ = (s : ℂ) + (c_θ : ℂ) * I := by
          dsimp only [η₀]
          simp
        have hu_c : (u₀ t : ℂ) = ((E : ℂ) - (c_θ : ℂ)) / (s : ℂ) := by
          dsimp only [u₀, E]
          push_cast
          rfl
        have hsc_ne : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs_ne
        have hη₀_mul : η₀ = ((s : ℂ) - (c_θ : ℂ) * I) * (((cβ : ℂ) ^ 2) * (1 + (u₀ t : ℂ) ^ 2)) := by
          rw [h1_c, mul_one]
        calc η₀ + star η₀ * w
            = ((s : ℂ) - (c_θ : ℂ) * I) * (((cβ : ℂ) ^ 2) * (1 + (u₀ t : ℂ) ^ 2)) +
              ((s : ℂ) + (c_θ : ℂ) * I) * (-((cβ : ℂ) ^ 2 * (1 + (u₀ t : ℂ) * I) ^ 2)) := by
                rw [← hη₀_mul, hη₀_bar, hw_eq]
          _ = -((E : ℂ) * I) * (2 * (cβ : ℂ) ^ 2 * (1 + (u₀ t : ℂ) * I)) := by
                rw [hu_c]
                field_simp [hsc_ne]
                apply Complex.ext <;> simp [pow_two] <;> ring
          _ = -((E : ℂ) * I) * (1 - w) := by rw [← h1w_eq]
      have hslit : η w ∈ Complex.slitPlane := by
        have hE_ne : E ≠ 0 := Real.exp_ne_zero _
        rw [hη_val, Complex.mem_slitPlane_iff]
        exact Or.inr (by simp [hE_ne])
      have hΦ_val : Φ w = I * (t : ℂ) := by
        have hexp_E : -((E : ℂ) * I) = Complex.exp (↑(-Real.pi * t) - ↑(Real.pi / 2) * I) := by
          rw [sub_eq_add_neg, Complex.exp_add, ← Complex.ofReal_exp]
          have hneg_I : -(↑(Real.pi / 2) * I) = ↑(-(Real.pi / 2)) * I := by push_cast; ring
          rw [hneg_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
            Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
          simp [E]
        have him1 : -Real.pi < (↑(-Real.pi * t) - ↑(Real.pi / 2) * I).im := by
          simp; linarith
        have him2 : (↑(-Real.pi * t) - ↑(Real.pi / 2) * I).im ≤ Real.pi := by
          simp; linarith
        dsimp only [Φ]
        rw [hη_val, hexp_E, Complex.log_exp him1 him2]
        have hπc_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ_ne
        have hI_ne : (I : ℂ) ≠ 0 := I_ne_zero
        field_simp [hπc_ne, hI_ne]
        apply Complex.ext <;> simp <;> ring
      exact ⟨h1w_ne, hslit, hΦ_val⟩
    have hbd_arc : ∀ φ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi), φ ≠ 2 * Real.pi * θ →
        ContinuousAt Φ (Complex.exp (I * (φ : ℂ))) ∧
        Φ (Complex.exp (I * (φ : ℂ))) ∈ verticalClosedStrip 0 1 := by
      intro φ hφ hne
      have hcases : φ ∈ Set.Ioo 0 (2 * Real.pi * θ) ∨ φ ∈ Set.Ioo (2 * Real.pi * θ) (2 * Real.pi) := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨hφ.1, hlt⟩
        · exact Or.inr ⟨hgt, hφ.2⟩
      rcases hcases with h1 | h0
      · rw [← hφ₁_img] at h1
        rcases h1 with ⟨t, -, rfl⟩
        rcases hbd_φ₁ t with ⟨h1w_ne, hslit, hΦ_eq⟩
        have hcont : ContinuousAt Φ (Complex.exp (I * (φ₁ t : ℂ))) :=
          continuousAt_const.add
            (((Complex.differentiableAt_log hslit).continuousAt.comp
              (hη_diff_at _ h1w_ne).continuousAt).div_const _)
        have hmem : Φ (Complex.exp (I * (φ₁ t : ℂ))) ∈ verticalClosedStrip 0 1 := by
          rw [hΦ_eq]
          change 0 ≤ (1 + I * (t : ℂ)).re ∧ (1 + I * (t : ℂ)).re ≤ 1
          simp
        exact ⟨hcont, hmem⟩
      · rw [← hφ₀_img] at h0
        rcases h0 with ⟨t, -, rfl⟩
        rcases hbd_φ₀ t with ⟨h1w_ne, hslit, hΦ_eq⟩
        have hcont : ContinuousAt Φ (Complex.exp (I * (φ₀ t : ℂ))) :=
          continuousAt_const.add
            (((Complex.differentiableAt_log hslit).continuousAt.comp
              (hη_diff_at _ h1w_ne).continuousAt).div_const _)
        have hmem : Φ (Complex.exp (I * (φ₀ t : ℂ))) ∈ verticalClosedStrip 0 1 := by
          rw [hΦ_eq]
          change 0 ≤ (I * (t : ℂ)).re ∧ (I * (t : ℂ)).re ≤ 1
          simp
        exact ⟨hcont, hmem⟩
    refine ⟨hα_pos, hα_int, hβ_pos, hβ_int, Φ, hΦ_diff, hΦ_maps, hΦ0, ?_⟩
    intro ψ hψ_cont ⟨C, hψ_bdd⟩
    have h0_mem : (0 : ℂ) ∈ verticalClosedStrip 0 1 := by
      change 0 ≤ (0 : ℂ).re ∧ (0 : ℂ).re ≤ 1
      simp
    have hC_nn : 0 ≤ C := (abs_nonneg (ψ 0)).trans (hψ_bdd 0 h0_mem)
    let r_seq : ℕ → ℝ := fun n => 1 - ((n : ℝ) + 2)⁻¹
    have hr_mem : ∀ n : ℕ, r_seq n ∈ Set.Ioo (0 : ℝ) 1 := by
      intro n
      have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hinv_pos : 0 < ((n : ℝ) + 2)⁻¹ := inv_pos.mpr (zero_lt_one.trans hn2)
      have hinv_lt1 : ((n : ℝ) + 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hn2
      exact ⟨sub_pos.mpr hinv_lt1, sub_lt_self 1 hinv_pos⟩
    have hr_tendsto : Filter.Tendsto r_seq Filter.atTop (nhds 1) := by
      have hinv0 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp
          (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      simpa [r_seq] using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv0
    let F_seq : ℕ → ℝ → ℝ := fun n φ =>
      ψ (Φ (((r_seq n : ℝ) : ℂ) * Complex.exp (I * (φ : ℂ))))
    let f_lim : ℝ → ℝ := fun φ => ψ (Φ (Complex.exp (I * (φ : ℂ))))
    have hball_rn : ∀ (n : ℕ) (φ : ℝ),
        ((r_seq n : ℝ) : ℂ) * Complex.exp (I * (φ : ℂ)) ∈ Metric.ball (0 : ℂ) 1 := by
      intro n φ
      rw [Metric.mem_ball, dist_zero_right, norm_mul,
        Complex.norm_of_nonneg (hr_mem n).1.le]
      have hnorm_exp : ‖Complex.exp (I * (φ : ℂ))‖ = 1 := by
        rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
      rw [hnorm_exp, mul_one]
      exact (hr_mem n).2
    have hstrip_sub_closed : verticalStrip 0 1 ⊆ verticalClosedStrip 0 1 :=
      fun z hz => ⟨hz.1.le, hz.2.le⟩
    have hF_cont : ∀ n : ℕ, Continuous (F_seq n) := by
      intro n
      have hcont_c : Continuous (fun φ : ℝ => ((r_seq n : ℝ) : ℂ) * Complex.exp (I * (φ : ℂ))) :=
        continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal))
      have hcont_Φ : Continuous (fun φ : ℝ => Φ (((r_seq n : ℝ) : ℂ) * Complex.exp (I * (φ : ℂ)))) :=
        hΦ_diff.continuousOn.comp_continuous hcont_c (hball_rn n)
      exact hψ_cont.comp_continuous hcont_Φ (fun φ => hstrip_sub_closed (hΦ_maps _ (hball_rn n φ)))
    have hF_meas : ∀ᶠ n in Filter.atTop,
        AEStronglyMeasurable (F_seq n) (volume.restrict (Set.uIoc 0 (2 * Real.pi))) :=
      Filter.Eventually.of_forall fun n => (hF_cont n).aestronglyMeasurable
    have hF_bound : ∀ᶠ n in Filter.atTop,
        ∀ᵐ φ ∂volume, φ ∈ Set.uIoc 0 (2 * Real.pi) → ‖F_seq n φ‖ ≤ C := by
      refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun φ _ => ?_
      rw [Real.norm_eq_abs]
      exact hψ_bdd _ (hstrip_sub_closed (hΦ_maps _ (hball_rn n φ)))
    let S_bad : Set ℝ := ({0, 2 * Real.pi * θ, 2 * Real.pi} : Set ℝ)
    have hS_bad_null : volume S_bad = 0 :=
      ((Set.finite_singleton _).insert _ |>.insert _).countable.measure_zero volume
    have hae_not_bad : ∀ᵐ φ ∂volume, φ ∉ S_bad := by
      simpa [ae_iff] using hS_bad_null
    have hF_ptwise : ∀ᵐ φ ∂volume,
        φ ∈ Set.uIoc 0 (2 * Real.pi) → Filter.Tendsto (fun n => F_seq n φ) Filter.atTop (nhds (f_lim φ)) := by
      filter_upwards [hae_not_bad] with φ hnot_bad hmem_uIoc
      have h2pi_pos : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      rw [Set.uIoc_of_le h2pi_pos] at hmem_uIoc
      have hφ_ne_2pi : φ ≠ 2 * Real.pi := fun h => hnot_bad (Or.inr (Or.inr h))
      have hφ_ne_θ : φ ≠ 2 * Real.pi * θ := fun h => hnot_bad (Or.inr (Or.inl h))
      have hφ_Ioo : φ ∈ Set.Ioo 0 (2 * Real.pi) :=
        ⟨hmem_uIoc.1, lt_of_le_of_ne hmem_uIoc.2 hφ_ne_2pi⟩
      rcases hbd_arc φ hφ_Ioo hφ_ne_θ with ⟨hΦ_cont_at, hΦ_mem_cl⟩
      have hw_tendsto : Filter.Tendsto
          (fun n : ℕ => ((r_seq n : ℝ) : ℂ) * Complex.exp (I * (φ : ℂ)))
          Filter.atTop (nhds (Complex.exp (I * (φ : ℂ)))) := by
        have hc : Filter.Tendsto (fun n : ℕ => ((r_seq n : ℝ) : ℂ)) Filter.atTop (nhds (1 : ℂ)) :=
          (Complex.continuous_ofReal.continuousAt.tendsto).comp hr_tendsto
        simpa using hc.mul_const (Complex.exp (I * (φ : ℂ)))
      have hΦ_tendsto : Filter.Tendsto
          (fun n : ℕ => Φ (((r_seq n : ℝ) : ℂ) * Complex.exp (I * (φ : ℂ))))
          Filter.atTop (nhds (Φ (Complex.exp (I * (φ : ℂ))))) :=
        hΦ_cont_at.tendsto.comp hw_tendsto
      have hΦ_nhdsWithin : Filter.Tendsto
          (fun n : ℕ => Φ (((r_seq n : ℝ) : ℂ) * Complex.exp (I * (φ : ℂ))))
          Filter.atTop (nhdsWithin (Φ (Complex.exp (I * (φ : ℂ)))) (verticalClosedStrip 0 1)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hΦ_tendsto
          (Filter.Eventually.of_forall fun n => hstrip_sub_closed (hΦ_maps _ (hball_rn n φ)))
      exact (hψ_cont _ hΦ_mem_cl).tendsto.comp hΦ_nhdsWithin
    have hint_dct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ => C) hF_meas hF_bound intervalIntegrable_const hF_ptwise
    have havg_dct := hint_dct.const_mul (2 * Real.pi)⁻¹
    have hf_lim_meas_Ioc : AEStronglyMeasurable f_lim (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
      have h2pi_pos : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      have hpt_res : ∀ᵐ φ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))),
          Filter.Tendsto (fun n => F_seq n φ) Filter.atTop (nhds (f_lim φ)) := by
        rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hF_ptwise] with φ hφ hmem
        rw [← Set.uIoc_of_le h2pi_pos] at hmem
        exact hφ hmem
      exact aestronglyMeasurable_of_tendsto_ae Filter.atTop
        (fun n => (hF_cont n).aestronglyMeasurable) hpt_res
    have hf_lim_int_Ioc : IntegrableOn f_lim (Set.Ioc 0 (2 * Real.pi)) volume := by
      have hconst_int : IntegrableOn (fun _ : ℝ => C) (Set.Ioc 0 (2 * Real.pi)) volume :=
        (continuousOn_const.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
      refine hconst_int.mono' hf_lim_meas_Ioc ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hae_not_bad] with φ hnot_bad hmem
      have hφ_ne_2pi : φ ≠ 2 * Real.pi := fun h => hnot_bad (Or.inr (Or.inr h))
      have hφ_ne_θ : φ ≠ 2 * Real.pi * θ := fun h => hnot_bad (Or.inr (Or.inl h))
      have hφ_Ioo : φ ∈ Set.Ioo 0 (2 * Real.pi) :=
        ⟨hmem.1, lt_of_le_of_ne hmem.2 hφ_ne_2pi⟩
      rw [Real.norm_eq_abs]
      exact hψ_bdd _ (hbd_arc φ hφ_Ioo hφ_ne_θ).2
    have h0_le_2πθ : (0 : ℝ) ≤ 2 * Real.pi * θ := by positivity
    have h2πθ_le_2π : 2 * Real.pi * θ ≤ 2 * Real.pi := by nlinarith
    have hint_part1 : IntervalIntegrable f_lim volume 0 (2 * Real.pi * θ) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h0_le_2πθ]
      exact hf_lim_int_Ioc.mono_set (Set.Ioc_subset_Ioc_right h2πθ_le_2π)
    have hint_part0 : IntervalIntegrable f_lim volume (2 * Real.pi * θ) (2 * Real.pi) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2πθ_le_2π]
      exact hf_lim_int_Ioc.mono_set (Set.Ioc_subset_Ioc_left h0_le_2πθ)
    have hsplit : (∫ φ in (0 : ℝ)..(2 * Real.pi), f_lim φ) =
        (∫ φ in Set.Ioo 0 (2 * Real.pi * θ), f_lim φ) +
        (∫ φ in Set.Ioo (2 * Real.pi * θ) (2 * Real.pi), f_lim φ) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_part1 hint_part0,
        intervalIntegral.integral_of_le h0_le_2πθ,
        intervalIntegral.integral_of_le h2πθ_le_2π,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    have hjac1 : (∫ φ in Set.Ioo 0 (2 * Real.pi * θ), f_lim φ) =
        ∫ t : ℝ, (2 * Real.pi) * (hirschmanBeta θ t * (θ * ψ (1 + I * (t : ℂ)))) := by
      rw [← hφ₁_img, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
        (fun t _ => (hφ₁_deriv t).hasDerivWithinAt) hφ₁_mono.injective.injOn f_lim,
        setIntegral_univ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      have hd_pos : 0 < 2 * Real.pi * θ * hirschmanBeta θ t :=
        mul_pos (mul_pos (mul_pos two_pos hπ_pos) hθ0) (hβ_pos t)
      dsimp only [f_lim]
      rw [abs_of_pos hd_pos, smul_eq_mul, (hbd_φ₁ t).2.2]
      ring
    have hjac0 : (∫ φ in Set.Ioo (2 * Real.pi * θ) (2 * Real.pi), f_lim φ) =
        ∫ t : ℝ, (2 * Real.pi) * (hirschmanAlpha θ t * ((1 - θ) * ψ (I * (t : ℂ)))) := by
      rw [← hφ₀_img, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
        (fun t _ => (hφ₀_deriv t).hasDerivWithinAt) hφ₀_anti.injective.injOn f_lim,
        setIntegral_univ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      have hd_pos : 0 < 2 * Real.pi * (1 - θ) * hirschmanAlpha θ t :=
        mul_pos (mul_pos (mul_pos two_pos hπ_pos) h1θ) (hα_pos t)
      dsimp only [f_lim]
      rw [abs_neg, abs_of_pos hd_pos, smul_eq_mul, (hbd_φ₀ t).2.2]
      ring
    have htermα_int : Integrable (fun t : ℝ => hirschmanAlpha θ t * ((1 - θ) * ψ (I * (t : ℂ)))) := by
      have hcont_ψ0 : Continuous (fun t : ℝ => ψ (I * (t : ℂ))) :=
        hψ_cont.comp_continuous (continuous_const.mul continuous_ofReal) (fun t => by
          change 0 ≤ (I * (t : ℂ)).re ∧ (I * (t : ℂ)).re ≤ 1; simp)
      refine (hα_int.norm.mul_const ((1 - θ) * C)).mono'
        (hα_int.aestronglyMeasurable.mul (continuous_const.mul hcont_ψ0).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun t => ?_)
      have hmem0 : I * (t : ℂ) ∈ verticalClosedStrip 0 1 := by
        change 0 ≤ (I * (t : ℂ)).re ∧ (I * (t : ℂ)).re ≤ 1; simp
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (hα_pos t), abs_of_pos h1θ]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hψ_bdd _ hmem0) h1θ.le) (hα_pos t).le
    have htermβ_int : Integrable (fun t : ℝ => hirschmanBeta θ t * (θ * ψ (1 + I * (t : ℂ)))) := by
      have hcont_ψ1 : Continuous (fun t : ℝ => ψ (1 + I * (t : ℂ))) :=
        hψ_cont.comp_continuous (continuous_const.add (continuous_const.mul continuous_ofReal))
          (fun t => by change 0 ≤ (1 + I * (t : ℂ)).re ∧ (1 + I * (t : ℂ)).re ≤ 1; simp)
      refine (hβ_int.norm.mul_const (θ * C)).mono'
        (hβ_int.aestronglyMeasurable.mul (continuous_const.mul hcont_ψ1).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun t => ?_)
      have hmem1 : 1 + I * (t : ℂ) ∈ verticalClosedStrip 0 1 := by
        change 0 ≤ (1 + I * (t : ℂ)).re ∧ (1 + I * (t : ℂ)).re ≤ 1; simp
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (hβ_pos t), abs_of_pos hθ0]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hψ_bdd _ hmem1) hθ0.le) (hβ_pos t).le
    have htarget_eq : (2 * Real.pi)⁻¹ * (∫ φ in (0 : ℝ)..(2 * Real.pi), f_lim φ) =
        ∫ t : ℝ, (hirschmanAlpha θ t * ((1 - θ) * ψ (I * (t : ℂ))) +
          hirschmanBeta θ t * (θ * ψ (1 + I * (t : ℂ)))) := by
      rw [hsplit, hjac1, hjac0, integral_const_mul, integral_const_mul, add_comm]
      have h2π_ne : 2 * Real.pi ≠ 0 := (mul_pos two_pos hπ_pos).ne'
      rw [← mul_add, inv_mul_cancel_left₀ h2π_ne, ← integral_add htermα_int htermβ_int]
    rwa [htarget_eq] at havg_dct
  
  have hs4 : ∀ {c : ℝ}, 0 < c →
      ∀ {w₀ w₁ a₀ b₀ A B : ℝ → ℝ},
      (∀ t, 0 < w₀ t) → Integrable w₀ →
      (∀ t, 0 < w₁ t) → Integrable w₁ →
      Continuous a₀ → Continuous b₀ →
      (∀ t, 0 ≤ a₀ t ∧ a₀ t ≤ A t) → (∀ t, 0 ≤ b₀ t ∧ b₀ t ≤ B t) →
      (∃ M : ℝ, (∀ t, a₀ t ≤ M) ∧ (∀ t, b₀ t ≤ M)) →
      (∀ ε : ℝ, 0 < ε → Real.log c ≤
        ∫ t : ℝ, (w₀ t * ((1 - θ) * Real.log (max (a₀ t) ε)) +
          w₁ t * (θ * Real.log (max (b₀ t) ε)))) →
      Integrable (fun t : ℝ => w₀ t * Real.log (A t ^ (1 - θ))) →
      Integrable (fun t : ℝ => w₁ t * Real.log (B t ^ θ)) →
      Real.log c ≤ ∫ t : ℝ, (w₀ t * Real.log (A t ^ (1 - θ)) + w₁ t * Real.log (B t ^ θ)) := by
    clear hs1 hs2 hs3 G hd hb hp₀ hp₁ hpθ hGθ hα hβ p₀ p₁ pθ
    intro c _hc w₀ w₁ a₀ b₀ A B hw₀_pos hw₀_int hw₁_pos hw₁_int ha₀_cont hb₀_cont
      ha₀_le hb₀_le hab_bdd h_eps hα hβ
    have hθ0 : 0 < θ := hθ.1
    have hθ1 : θ < 1 := hθ.2
    have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
    rcases hab_bdd with ⟨M₀, haM₀, hbM₀⟩
    let M' : ℝ := max 1 M₀
    have hM'1 : 1 ≤ M' := le_max_left 1 M₀
    have hM'_pos : 0 < M' := lt_of_lt_of_le zero_lt_one hM'1
    have hlogM'_nn : 0 ≤ Real.log M' := Real.log_nonneg hM'1
    have haM' : ∀ t, a₀ t ≤ M' := fun t => (haM₀ t).trans (le_max_right 1 M₀)
    have hbM' : ∀ t, b₀ t ≤ M' := fun t => (hbM₀ t).trans (le_max_right 1 M₀)
    have hint_reg : ∀ {w u : ℝ → ℝ} (hw_int : Integrable w) (hu_cont : Continuous u)
        (hu_bdd : ∀ t, u t ≤ M') (κ ε : ℝ) (hε : 0 < ε),
        Integrable (fun t => w t * (κ * Real.log (max (u t) ε))) := by
      intro w u hw_int hu_cont hu_bdd κ ε hε
      let L : ℝ := max |Real.log ε| |Real.log (max M' ε)|
      have hcont_f : Continuous (fun t => κ * Real.log (max (u t) ε)) :=
        continuous_const.mul ((hu_cont.max continuous_const).log fun t =>
          (lt_of_lt_of_le hε (le_max_right _ _)).ne')
      refine (hw_int.norm.mul_const (|κ| * L)).mono'
        (hw_int.aestronglyMeasurable.mul hcont_f.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun t => ?_)
      have h1 : Real.log ε ≤ Real.log (max (u t) ε) :=
        Real.log_le_log hε (le_max_right _ _)
      have h2 : Real.log (max (u t) ε) ≤ Real.log (max M' ε) :=
        Real.log_le_log (lt_of_lt_of_le hε (le_max_right _ _))
          (max_le_max (hu_bdd t) le_rfl)
      have habs_log : |Real.log (max (u t) ε)| ≤ L := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · linarith [neg_abs_le (Real.log ε), le_max_left |Real.log ε| |Real.log (max M' ε)|]
        · linarith [le_abs_self (Real.log (max M' ε)),
            le_max_right |Real.log ε| |Real.log (max M' ε)|]
      simp only [Real.norm_eq_abs, abs_mul]
      calc |w t| * (|κ| * |Real.log (max (u t) ε)|)
          ≤ |w t| * (|κ| * L) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left habs_log (abs_nonneg κ)) (abs_nonneg _)
        _ = ‖w t‖ * (|κ| * L) := by rw [Real.norm_eq_abs]
    let Z₀ : Set ℝ := {t : ℝ | a₀ t = 0}
    have hZ₀_meas : MeasurableSet Z₀ := (isClosed_singleton.preimage ha₀_cont).measurableSet
    have hZ₀_null : volume Z₀ = 0 := by
      let C₀ : ℝ := (1 - θ) * Real.log M' * (∫ t, w₀ t) + θ * Real.log M' * (∫ t, w₁ t)
      let I₀ : ℝ := ∫ t, Z₀.indicator w₀ t
      have hZ₀_int : Integrable (Z₀.indicator w₀) := hw₀_int.indicator hZ₀_meas
      have hZ₀_nn : 0 ≤ Z₀.indicator w₀ := fun t =>
        Set.indicator_nonneg (fun s _ => (hw₀_pos s).le) t
      have hI₀_nn : 0 ≤ I₀ := integral_nonneg hZ₀_nn
      have hR_bound : ∀ R : ℝ, 0 < R →
          Real.log c ≤ C₀ - (1 - θ) * (R + Real.log M') * I₀ := by
        intro R hR
        let ε : ℝ := Real.exp (-R)
        have hε_pos : 0 < ε := Real.exp_pos (-R)
        have hε_lt1 : ε < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        have hε_le_M' : ε ≤ M' := hε_lt1.le.trans hM'1
        have h1 : Integrable (fun t => w₀ t * ((1 - θ) * Real.log (max (a₀ t) ε))) :=
          hint_reg hw₀_int ha₀_cont haM' (1 - θ) ε hε_pos
        have h2 : Integrable (fun t => w₁ t * (θ * Real.log (max (b₀ t) ε))) :=
          hint_reg hw₁_int hb₀_cont hbM' θ ε hε_pos
        let U : ℝ → ℝ := fun t =>
          ((1 - θ) * Real.log M') * w₀ t + (θ * Real.log M') * w₁ t -
            ((1 - θ) * (R + Real.log M')) * Z₀.indicator w₀ t
        have hU_int : Integrable U :=
          ((hw₀_int.const_mul _).add (hw₁_int.const_mul _)).sub (hZ₀_int.const_mul _)
        have hpwise : ∀ t : ℝ,
            w₀ t * ((1 - θ) * Real.log (max (a₀ t) ε)) +
              w₁ t * (θ * Real.log (max (b₀ t) ε)) ≤ U t := by
          intro t
          have hb_log : Real.log (max (b₀ t) ε) ≤ Real.log M' :=
            Real.log_le_log (lt_of_lt_of_le hε_pos (le_max_right _ _))
              (max_le (hbM' t) hε_le_M')
          have hb_term : w₁ t * (θ * Real.log (max (b₀ t) ε)) ≤ (θ * Real.log M') * w₁ t := by
            have := mul_le_mul_of_nonneg_left hb_log (mul_pos (hw₁_pos t) hθ0).le
            linarith
          by_cases ht : t ∈ Z₀
          · have ha0 : a₀ t = 0 := ht
            have hmax_a : max (a₀ t) ε = ε := by rw [ha0, max_eq_right hε_pos.le]
            have hlog_a : Real.log (max (a₀ t) ε) = -R := by
              rw [hmax_a, Real.log_exp]
            have hind : Z₀.indicator w₀ t = w₀ t := Set.indicator_of_mem ht w₀
            dsimp only [U]
            rw [hlog_a, hind]
            linarith
          · have ha_log : Real.log (max (a₀ t) ε) ≤ Real.log M' :=
              Real.log_le_log (lt_of_lt_of_le hε_pos (le_max_right _ _))
                (max_le (haM' t) hε_le_M')
            have ha_term :
                w₀ t * ((1 - θ) * Real.log (max (a₀ t) ε)) ≤ ((1 - θ) * Real.log M') * w₀ t := by
              have := mul_le_mul_of_nonneg_left ha_log (mul_pos (hw₀_pos t) h1θ).le
              linarith
            have hind : Z₀.indicator w₀ t = 0 := Set.indicator_of_notMem ht w₀
            dsimp only [U]
            rw [hind, mul_zero, sub_zero]
            linarith
        have hint_le := integral_mono (h1.add h2) hU_int hpwise
        have hU_eq : ∫ t, U t = C₀ - (1 - θ) * (R + Real.log M') * I₀ := by
          dsimp only [U, C₀, I₀]
          have h12 : Integrable (fun t => (1 - θ) * Real.log M' * w₀ t + θ * Real.log M' * w₁ t) :=
            (hw₀_int.const_mul _).add (hw₁_int.const_mul _)
          have h3 : Integrable (fun t => (1 - θ) * (R + Real.log M') * Z₀.indicator w₀ t) :=
            hZ₀_int.const_mul _
          rw [integral_sub h12 h3, integral_add (hw₀_int.const_mul _) (hw₁_int.const_mul _),
            integral_const_mul, integral_const_mul, integral_const_mul]
        exact (h_eps ε hε_pos).trans (hint_le.trans_eq hU_eq)
      have hI₀_eq : I₀ = 0 := by
        by_contra hne
        have hI₀_pos : 0 < I₀ := lt_of_le_of_ne hI₀_nn (Ne.symm hne)
        have hdenom_pos : 0 < (1 - θ) * I₀ := mul_pos h1θ hI₀_pos
        let R : ℝ := max 1 ((C₀ - Real.log c) / ((1 - θ) * I₀) + 1)
        have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
        have hR_gt : (C₀ - Real.log c) / ((1 - θ) * I₀) + 1 ≤ R := le_max_right _ _
        have hmul : C₀ - Real.log c + (1 - θ) * I₀ ≤ R * ((1 - θ) * I₀) := by
          have := mul_le_mul_of_nonneg_right hR_gt hdenom_pos.le
          rwa [add_mul, div_mul_cancel₀ _ hdenom_pos.ne', one_mul] at this
        have hbound := hR_bound R hR_pos
        have hnonneg_extra : 0 ≤ (1 - θ) * Real.log M' * I₀ :=
          mul_nonneg (mul_nonneg h1θ.le hlogM'_nn) hI₀_nn
        linarith
      have hae_zero : Z₀.indicator w₀ =ᵐ[volume] 0 :=
        (integral_eq_zero_iff_of_nonneg hZ₀_nn hZ₀_int).mp hI₀_eq
      rw [Filter.EventuallyEq, ae_iff] at hae_zero
      refine measure_mono_null (fun t ht => ?_) hae_zero
      simp only [Set.mem_setOf_eq, Pi.zero_apply]
      rw [Set.indicator_of_mem ht]
      exact (hw₀_pos t).ne'
    let Z₁ : Set ℝ := {t : ℝ | b₀ t = 0}
    have hZ₁_meas : MeasurableSet Z₁ := (isClosed_singleton.preimage hb₀_cont).measurableSet
    have hZ₁_null : volume Z₁ = 0 := by
      let C₁ : ℝ := (1 - θ) * Real.log M' * (∫ t, w₀ t) + θ * Real.log M' * (∫ t, w₁ t)
      let I₁ : ℝ := ∫ t, Z₁.indicator w₁ t
      have hZ₁_int : Integrable (Z₁.indicator w₁) := hw₁_int.indicator hZ₁_meas
      have hZ₁_nn : 0 ≤ Z₁.indicator w₁ := fun t =>
        Set.indicator_nonneg (fun s _ => (hw₁_pos s).le) t
      have hI₁_nn : 0 ≤ I₁ := integral_nonneg hZ₁_nn
      have hR_bound : ∀ R : ℝ, 0 < R →
          Real.log c ≤ C₁ - θ * (R + Real.log M') * I₁ := by
        intro R hR
        let ε : ℝ := Real.exp (-R)
        have hε_pos : 0 < ε := Real.exp_pos (-R)
        have hε_lt1 : ε < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        have hε_le_M' : ε ≤ M' := hε_lt1.le.trans hM'1
        have h1 : Integrable (fun t => w₀ t * ((1 - θ) * Real.log (max (a₀ t) ε))) :=
          hint_reg hw₀_int ha₀_cont haM' (1 - θ) ε hε_pos
        have h2 : Integrable (fun t => w₁ t * (θ * Real.log (max (b₀ t) ε))) :=
          hint_reg hw₁_int hb₀_cont hbM' θ ε hε_pos
        let U : ℝ → ℝ := fun t =>
          ((1 - θ) * Real.log M') * w₀ t + (θ * Real.log M') * w₁ t -
            (θ * (R + Real.log M')) * Z₁.indicator w₁ t
        have hU_int : Integrable U :=
          ((hw₀_int.const_mul _).add (hw₁_int.const_mul _)).sub (hZ₁_int.const_mul _)
        have hpwise : ∀ t : ℝ,
            w₀ t * ((1 - θ) * Real.log (max (a₀ t) ε)) +
              w₁ t * (θ * Real.log (max (b₀ t) ε)) ≤ U t := by
          intro t
          have ha_log : Real.log (max (a₀ t) ε) ≤ Real.log M' :=
            Real.log_le_log (lt_of_lt_of_le hε_pos (le_max_right _ _))
              (max_le (haM' t) hε_le_M')
          have ha_term :
              w₀ t * ((1 - θ) * Real.log (max (a₀ t) ε)) ≤ ((1 - θ) * Real.log M') * w₀ t := by
            have := mul_le_mul_of_nonneg_left ha_log (mul_pos (hw₀_pos t) h1θ).le
            linarith
          by_cases ht : t ∈ Z₁
          · have hb0 : b₀ t = 0 := ht
            have hmax_b : max (b₀ t) ε = ε := by rw [hb0, max_eq_right hε_pos.le]
            have hlog_b : Real.log (max (b₀ t) ε) = -R := by
              rw [hmax_b, Real.log_exp]
            have hind : Z₁.indicator w₁ t = w₁ t := Set.indicator_of_mem ht w₁
            dsimp only [U]
            rw [hlog_b, hind]
            linarith
          · have hb_log : Real.log (max (b₀ t) ε) ≤ Real.log M' :=
              Real.log_le_log (lt_of_lt_of_le hε_pos (le_max_right _ _))
                (max_le (hbM' t) hε_le_M')
            have hb_term :
                w₁ t * (θ * Real.log (max (b₀ t) ε)) ≤ (θ * Real.log M') * w₁ t := by
              have := mul_le_mul_of_nonneg_left hb_log (mul_pos (hw₁_pos t) hθ0).le
              linarith
            have hind : Z₁.indicator w₁ t = 0 := Set.indicator_of_notMem ht w₁
            dsimp only [U]
            rw [hind, mul_zero, sub_zero]
            linarith
        have hint_le := integral_mono (h1.add h2) hU_int hpwise
        have hU_eq : ∫ t, U t = C₁ - θ * (R + Real.log M') * I₁ := by
          dsimp only [U, C₁, I₁]
          have h12 : Integrable (fun t => (1 - θ) * Real.log M' * w₀ t + θ * Real.log M' * w₁ t) :=
            (hw₀_int.const_mul _).add (hw₁_int.const_mul _)
          have h3 : Integrable (fun t => θ * (R + Real.log M') * Z₁.indicator w₁ t) :=
            hZ₁_int.const_mul _
          rw [integral_sub h12 h3, integral_add (hw₀_int.const_mul _) (hw₁_int.const_mul _),
            integral_const_mul, integral_const_mul, integral_const_mul]
        exact (h_eps ε hε_pos).trans (hint_le.trans_eq hU_eq)
      have hI₁_eq : I₁ = 0 := by
        by_contra hne
        have hI₁_pos : 0 < I₁ := lt_of_le_of_ne hI₁_nn (Ne.symm hne)
        have hdenom_pos : 0 < θ * I₁ := mul_pos hθ0 hI₁_pos
        let R : ℝ := max 1 ((C₁ - Real.log c) / (θ * I₁) + 1)
        have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
        have hR_gt : (C₁ - Real.log c) / (θ * I₁) + 1 ≤ R := le_max_right _ _
        have hmul : C₁ - Real.log c + θ * I₁ ≤ R * (θ * I₁) := by
          have := mul_le_mul_of_nonneg_right hR_gt hdenom_pos.le
          rwa [add_mul, div_mul_cancel₀ _ hdenom_pos.ne', one_mul] at this
        have hbound := hR_bound R hR_pos
        have hnonneg_extra : 0 ≤ θ * Real.log M' * I₁ :=
          mul_nonneg (mul_nonneg hθ0.le hlogM'_nn) hI₁_nn
        linarith
      have hae_zero : Z₁.indicator w₁ =ᵐ[volume] 0 :=
        (integral_eq_zero_iff_of_nonneg hZ₁_nn hZ₁_int).mp hI₁_eq
      rw [Filter.EventuallyEq, ae_iff] at hae_zero
      refine measure_mono_null (fun t ht => ?_) hae_zero
      simp only [Set.mem_setOf_eq, Pi.zero_apply]
      rw [Set.indicator_of_mem ht]
      exact (hw₁_pos t).ne'
    have hA_pos_ae : ∀ᵐ t ∂volume, 0 < A t := by
      rw [ae_iff]
      refine measure_mono_null (fun t ht => ?_) hZ₀_null
      have ha0_nn := (ha₀_le t).1
      have ha0_le_A := (ha₀_le t).2
      by_contra hne
      exact ht (lt_of_lt_of_le (lt_of_le_of_ne ha0_nn (Ne.symm hne)) ha0_le_A)
    have hB_pos_ae : ∀ᵐ t ∂volume, 0 < B t := by
      rw [ae_iff]
      refine measure_mono_null (fun t ht => ?_) hZ₁_null
      have hb0_nn := (hb₀_le t).1
      have hb0_le_B := (hb₀_le t).2
      by_contra hne
      exact ht (lt_of_lt_of_le (lt_of_le_of_ne hb0_nn (Ne.symm hne)) hb0_le_B)
    have hA_meas : AEStronglyMeasurable A volume := by
      let reconA : ℝ → ℝ := fun t =>
        Real.exp ((w₀ t * Real.log (A t ^ (1 - θ))) * (w₀ t * (1 - θ))⁻¹)
      have hreconA_meas : AEStronglyMeasurable reconA volume :=
        Real.continuous_exp.comp_aestronglyMeasurable
          (hα.aestronglyMeasurable.mul
            (measurable_inv.comp_aemeasurable
              (hw₀_int.aestronglyMeasurable.mul_const (1 - θ)).aemeasurable).aestronglyMeasurable)
      refine hreconA_meas.congr ?_
      filter_upwards [hA_pos_ae] with t ht
      dsimp only [reconA]
      rw [Real.log_rpow ht]
      have hw_ne : w₀ t ≠ 0 := (hw₀_pos t).ne'
      have h1θ_ne : 1 - θ ≠ 0 := h1θ.ne'
      have hsimp : (w₀ t * ((1 - θ) * Real.log (A t))) * (w₀ t * (1 - θ))⁻¹ = Real.log (A t) := by
        field_simp
      rw [hsimp, Real.exp_log ht]
    have hB_meas : AEStronglyMeasurable B volume := by
      let reconB : ℝ → ℝ := fun t =>
        Real.exp ((w₁ t * Real.log (B t ^ θ)) * (w₁ t * θ)⁻¹)
      have hreconB_meas : AEStronglyMeasurable reconB volume :=
        Real.continuous_exp.comp_aestronglyMeasurable
          (hβ.aestronglyMeasurable.mul
            (measurable_inv.comp_aemeasurable
              (hw₁_int.aestronglyMeasurable.mul_const θ).aemeasurable).aestronglyMeasurable)
      refine hreconB_meas.congr ?_
      filter_upwards [hB_pos_ae] with t ht
      dsimp only [reconB]
      rw [Real.log_rpow ht]
      have hw_ne : w₁ t ≠ 0 := (hw₁_pos t).ne'
      have hθ_ne : θ ≠ 0 := hθ0.ne'
      have hsimp : (w₁ t * (θ * Real.log (B t))) * (w₁ t * θ)⁻¹ = Real.log (B t) := by
        field_simp
      rw [hsimp, Real.exp_log ht]
    have habs_log_max : ∀ {x ε : ℝ}, 0 < x → 0 < ε → ε < 1 →
        |Real.log (max x ε)| ≤ |Real.log x| := by
      intro x ε hx _hε0 hε1
      by_cases hx1 : 1 ≤ x
      · rw [max_eq_left (hε1.le.trans hx1)]
      · have hx_lt1 : x < 1 := not_le.mp hx1
        have hlog_le : Real.log x ≤ Real.log (max x ε) := Real.log_le_log hx (le_max_left _ _)
        have hlog_nonpos : Real.log (max x ε) ≤ 0 := by
          have hmax_le1 : max x ε ≤ 1 := max_le hx_lt1.le hε1.le
          simpa using Real.log_le_log (lt_of_lt_of_le hx (le_max_left _ _)) hmax_le1
        rw [abs_of_nonpos hlog_nonpos, abs_of_nonpos (hlog_le.trans hlog_nonpos)]
        linarith
    let ε_seq : ℕ → ℝ := fun k => ((k : ℝ) + 2)⁻¹
    have hε_pos : ∀ k, 0 < ε_seq k := fun k => inv_pos.mpr (by positivity)
    have hε_lt1 : ∀ k, ε_seq k < 1 := fun k =>
      inv_lt_one_of_one_lt₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    let F : ℕ → ℝ → ℝ := fun k t => w₀ t * ((1 - θ) * Real.log (max (A t) (ε_seq k)))
    let G_seq : ℕ → ℝ → ℝ := fun k t => w₁ t * (θ * Real.log (max (B t) (ε_seq k)))
    have hF_meas : ∀ k, AEStronglyMeasurable (F k) volume := fun k =>
      hw₀_int.aestronglyMeasurable.mul
        (aestronglyMeasurable_const.mul
          (Real.measurable_log.comp_aemeasurable
            (hA_meas.aemeasurable.max aemeasurable_const)).aestronglyMeasurable)
    have hG_meas : ∀ k, AEStronglyMeasurable (G_seq k) volume := fun k =>
      hw₁_int.aestronglyMeasurable.mul
        (aestronglyMeasurable_const.mul
          (Real.measurable_log.comp_aemeasurable
            (hB_meas.aemeasurable.max aemeasurable_const)).aestronglyMeasurable)
    have hF_dom : ∀ k, ∀ᵐ t ∂volume, ‖F k t‖ ≤ ‖w₀ t * Real.log (A t ^ (1 - θ))‖ := by
      intro k
      filter_upwards [hA_pos_ae] with t ht
      dsimp only [F]
      rw [Real.log_rpow ht, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (hw₀_pos t), abs_of_pos h1θ]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (habs_log_max ht (hε_pos k) (hε_lt1 k)) h1θ.le)
        (hw₀_pos t).le
    have hG_dom : ∀ k, ∀ᵐ t ∂volume, ‖G_seq k t‖ ≤ ‖w₁ t * Real.log (B t ^ θ)‖ := by
      intro k
      filter_upwards [hB_pos_ae] with t ht
      dsimp only [G_seq]
      rw [Real.log_rpow ht, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (hw₁_pos t), abs_of_pos hθ0]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (habs_log_max ht (hε_pos k) (hε_lt1 k)) hθ0.le)
        (hw₁_pos t).le
    have hF_int : ∀ k, Integrable (F k) := fun k => hα.norm.mono' (hF_meas k) (hF_dom k)
    have hG_int : ∀ k, Integrable (G_seq k) := fun k => hβ.norm.mono' (hG_meas k) (hG_dom k)
    have hk_bound : ∀ k : ℕ, Real.log c ≤ (∫ t, F k t) + (∫ t, G_seq k t) := by
      intro k
      have hf_int : Integrable (fun t => w₀ t * ((1 - θ) * Real.log (max (a₀ t) (ε_seq k)))) :=
        hint_reg hw₀_int ha₀_cont haM' (1 - θ) (ε_seq k) (hε_pos k)
      have hg_int : Integrable (fun t => w₁ t * (θ * Real.log (max (b₀ t) (ε_seq k)))) :=
        hint_reg hw₁_int hb₀_cont hbM' θ (ε_seq k) (hε_pos k)
      have hfF : ∀ t, w₀ t * ((1 - θ) * Real.log (max (a₀ t) (ε_seq k))) ≤ F k t := by
        intro t
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (Real.log_le_log (lt_of_lt_of_le (hε_pos k) (le_max_right _ _))
              (max_le_max ((ha₀_le t).2) le_rfl))
            h1θ.le)
          (hw₀_pos t).le
      have hgG : ∀ t, w₁ t * (θ * Real.log (max (b₀ t) (ε_seq k))) ≤ G_seq k t := by
        intro t
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (Real.log_le_log (lt_of_lt_of_le (hε_pos k) (le_max_right _ _))
              (max_le_max ((hb₀_le t).2) le_rfl))
            hθ0.le)
          (hw₁_pos t).le
      calc Real.log c
          ≤ ∫ t, (w₀ t * ((1 - θ) * Real.log (max (a₀ t) (ε_seq k))) +
              w₁ t * (θ * Real.log (max (b₀ t) (ε_seq k)))) := h_eps (ε_seq k) (hε_pos k)
        _ = (∫ t, w₀ t * ((1 - θ) * Real.log (max (a₀ t) (ε_seq k)))) +
              (∫ t, w₁ t * (θ * Real.log (max (b₀ t) (ε_seq k)))) := integral_add hf_int hg_int
        _ ≤ (∫ t, F k t) + (∫ t, G_seq k t) :=
            add_le_add (integral_mono hf_int (hF_int k) hfF) (integral_mono hg_int (hG_int k) hgG)
    have hε_tendsto : Filter.Tendsto ε_seq Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have hF_lim : ∀ᵐ t ∂volume,
        Filter.Tendsto (fun k => F k t) Filter.atTop
          (nhds (w₀ t * Real.log (A t ^ (1 - θ)))) := by
      filter_upwards [hA_pos_ae] with t ht
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hε_tendsto.eventually (gt_mem_nhds ht)] with k hk
      dsimp only [F]
      rw [max_eq_left hk.le, Real.log_rpow ht]
    have hG_lim : ∀ᵐ t ∂volume,
        Filter.Tendsto (fun k => G_seq k t) Filter.atTop
          (nhds (w₁ t * Real.log (B t ^ θ))) := by
      filter_upwards [hB_pos_ae] with t ht
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hε_tendsto.eventually (gt_mem_nhds ht)] with k hk
      dsimp only [G_seq]
      rw [max_eq_left hk.le, Real.log_rpow ht]
    have hint_F_lim := tendsto_integral_of_dominated_convergence
      (fun t => ‖w₀ t * Real.log (A t ^ (1 - θ))‖) hF_meas hα.norm hF_dom hF_lim
    have hint_G_lim := tendsto_integral_of_dominated_convergence
      (fun t => ‖w₁ t * Real.log (B t ^ θ)‖) hG_meas hβ.norm hG_dom hG_lim
    have hsum_lim := hint_F_lim.add hint_G_lim
    rw [← integral_add hα hβ] at hsum_lim
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hsum_lim hk_bound
  
  rcases hs1 with ⟨g, hg_diff, hg_cont, ⟨M, _hM0, hg_bdd⟩, hc_pos, hgθ, hg0, hg1⟩
  rcases hs3 with ⟨hα_pos, hα_int, hβ_pos, hβ_int, Φ, hΦ_diff, hΦ_maps, hΦ0, hΦ_lim⟩
  let h : ℂ → ℂ := g ∘ Φ
  have hh_diff : DifferentiableOn ℂ h (Metric.ball 0 1) :=
    hg_diff.comp hΦ_diff hΦ_maps
  have hh0_norm : ‖h 0‖ = schattenNorm pθ (G θ) := by
    dsimp only [h, Function.comp_apply]
    rw [hΦ0, hgθ]
  have hh0 : h 0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hh0_norm
    exact hc_pos.ne hh0_norm
  have h_eps : ∀ ε : ℝ, 0 < ε → Real.log (schattenNorm pθ (G θ)) ≤
      ∫ t : ℝ, (hirschmanAlpha θ t * ((1 - θ) * Real.log (max ‖g (I * t)‖ ε)) +
        hirschmanBeta θ t * (θ * Real.log (max ‖g (1 + I * t)‖ ε))) := by
    intro ε hε
    let ψ_ε : ℂ → ℝ := fun z => Real.log (max ‖g z‖ ε)
    have hψ_cont : ContinuousOn ψ_ε (verticalClosedStrip 0 1) := by
      have hmax_cont : ContinuousOn (fun z => max ‖g z‖ ε) (verticalClosedStrip 0 1) :=
        (continuous_norm.comp_continuousOn hg_cont).sup continuousOn_const
      exact hmax_cont.log (fun z _ => (lt_of_lt_of_le hε (le_max_right _ _)).ne')
    have hψ_bdd : ∃ C : ℝ, ∀ z ∈ verticalClosedStrip 0 1, |ψ_ε z| ≤ C := by
      refine ⟨max |Real.log ε| |Real.log (max M ε)|, fun z hz => ?_⟩
      have h1 : Real.log ε ≤ ψ_ε z := Real.log_le_log hε (le_max_right _ _)
      have h2 : ψ_ε z ≤ Real.log (max M ε) :=
        Real.log_le_log (lt_of_lt_of_le hε (le_max_right _ _)) (max_le_max (hg_bdd z hz) le_rfl)
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · linarith [neg_abs_le (Real.log ε), le_max_left |Real.log ε| |Real.log (max M ε)|]
      · linarith [le_abs_self (Real.log (max M ε)), le_max_right |Real.log ε| |Real.log (max M ε)|]
    have hn_bound : ∀ n : ℕ, Real.log (schattenNorm pθ (G θ)) ≤
        (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi),
          ψ_ε (Φ (((1 - ((n : ℝ) + 2)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * φ))) := by
      intro n
      have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hr_mem : (1 - ((n : ℝ) + 2)⁻¹ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨sub_pos.mpr (inv_lt_one_of_one_lt₀ hn2), sub_lt_self 1 (inv_pos.mpr (zero_lt_one.trans hn2))⟩
      have hj := hs2 hh_diff hh0 hr_mem hε
      rwa [hh0_norm] at hj
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hΦ_lim ψ_ε hψ_cont hψ_bdd) hn_bound
  have hmem0 : ∀ t : ℝ, I * (t : ℂ) ∈ verticalClosedStrip 0 1 := fun t => by
    change 0 ≤ (I * (t : ℂ)).re ∧ (I * (t : ℂ)).re ≤ 1; simp
  have hmem1 : ∀ t : ℝ, 1 + I * (t : ℂ) ∈ verticalClosedStrip 0 1 := fun t => by
    change 0 ≤ (1 + I * (t : ℂ)).re ∧ (1 + I * (t : ℂ)).re ≤ 1; simp
  have ha₀_cont : Continuous (fun t : ℝ => ‖g (I * t)‖) :=
    continuous_norm.comp (hg_cont.comp_continuous (continuous_const.mul continuous_ofReal) hmem0)
  have hb₀_cont : Continuous (fun t : ℝ => ‖g (1 + I * t)‖) :=
    continuous_norm.comp
      (hg_cont.comp_continuous (continuous_const.add (continuous_const.mul continuous_ofReal)) hmem1)
  exact hs4 hc_pos hα_pos hα_int hβ_pos hβ_int ha₀_cont hb₀_cont
    (fun t => ⟨norm_nonneg _, hg0 t⟩) (fun t => ⟨norm_nonneg _, hg1 t⟩)
    ⟨M, fun t => hg_bdd _ (hmem0 t), fun t => hg_bdd _ (hmem1 t)⟩
    h_eps hα hβ

end Leap
