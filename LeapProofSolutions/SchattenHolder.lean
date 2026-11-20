import LeapProofObligations.Definitions

open scoped Real

namespace Leap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- Schatten Hölder / duality, `|tr(T X)| ≤ ‖T‖_p ‖X‖_q` for conjugate `p, q`. -/
theorem schatten_holder (T : H →L[ℂ] H) (X : H →L[ℂ] H) {p q : ℝ} (hp : 1 < p)
    (hpq : 1 / p + 1 / q = 1) :
    ‖LinearMap.trace ℂ H (T ∘L X : H →L[ℂ] H)‖ ≤ schattenNorm p T * schattenNorm q X := by
  
  have h_decomp : ∀ (A : H →L[ℂ] H),
      ∃ (v : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
        (u : Fin (Module.finrank ℂ H) → H),
        (∀ i, A (v i) = (singularValues A i : ℂ) • u i) ∧
        (∀ i, ‖u i‖ ≤ 1) ∧
        (∀ x : H, ∑ i, ‖inner ℂ (u i) x‖ ^ 2 ≤ ‖x‖ ^ 2) := by
    intro A
    let hA := isSymmetric_adjoint_comp_self A
    let v : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := hA.eigenvectorBasis rfl
    let s : Fin (Module.finrank ℂ H) → ℝ := singularValues A
    let u : Fin (Module.finrank ℂ H) → H := fun i => (s i : ℂ)⁻¹ • A (v i)
    have hs_norm : ∀ i, s i = ‖A (v i)‖ := by
      intro i
      have heig : hA.eigenvalues rfl i = ‖A (v i)‖ ^ 2 := by
        apply Complex.ofReal_injective
        have h_eig_app : ContinuousLinearMap.adjoint A (A (v i)) = (hA.eigenvalues rfl i : ℂ) • v i :=
          hA.apply_eigenvectorBasis rfl i
        have h1 := congr_arg (inner ℂ (v i)) h_eig_app
        rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K,
          inner_smul_right, inner_self_eq_norm_sq_to_K, v.orthonormal.1 i] at h1
        simpa [← Complex.ofReal_pow] using h1.symm
      change Real.sqrt (hA.eigenvalues rfl i) = ‖A (v i)‖
      rw [heig, Real.sqrt_sq (norm_nonneg (A (v i)))]
    have hAv : ∀ i, A (v i) = (s i : ℂ) • u i := by
      intro i
      by_cases hs0 : s i = 0
      · have hAv0 : A (v i) = 0 := norm_eq_zero.mp (by rw [← hs_norm i, hs0])
        simp [u, hs0, hAv0]
      · dsimp only [u]
        rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs0), one_smul]
    have hu_norm_one : ∀ i, s i ≠ 0 → ‖u i‖ = 1 := by
      intro i hs0
      dsimp only [u]
      rw [norm_smul, norm_inv, Complex.norm_of_nonneg (by rw [hs_norm i]; exact norm_nonneg _),
        ← hs_norm i, inv_mul_cancel₀ hs0]
    have hu_norm : ∀ i, ‖u i‖ ≤ 1 := by
      intro i
      by_cases hs0 : s i = 0
      · simp [u, hs0]
      · exact le_of_eq (hu_norm_one i hs0)
    have hu_orth : ∀ {i k}, i ≠ k → inner ℂ (u i) (u k) = 0 := by
      intro i k hik
      dsimp only [u]
      rw [inner_smul_left, inner_smul_right]
      have hAv_orth : inner ℂ (A (v i)) (A (v k)) = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
        change inner ℂ (v i) ((↑(ContinuousLinearMap.adjoint A ∘SL A) : H →ₗ[ℂ] H) (v k)) = 0
        rw [hA.apply_eigenvectorBasis rfl k, inner_smul_right, v.orthonormal.2 hik, mul_zero]
      rw [hAv_orth, mul_zero, mul_zero]
    have hu_bessel : ∀ x : H, ∑ i, ‖inner ℂ (u i) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      intro x
      classical
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i => s i ≠ 0) (fun i => ‖inner ℂ (u i) x‖ ^ 2)]
      have h_zero : ∑ i : {i // ¬ s i ≠ 0}, ‖inner ℂ (u i.1) x‖ ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hsi : s i.1 = 0 := not_not.mp i.2
        simp [u, hsi]
      rw [h_zero, add_zero]
      have horth : Orthonormal ℂ (fun i : {i // s i ≠ 0} => u i.1) := by
        refine ⟨fun i => hu_norm_one i.1 i.2, ?_⟩
        intro i k hik
        exact hu_orth (fun h => hik (Subtype.ext h))
      exact horth.sum_inner_products_le x
    exact ⟨v, u, hAv, hu_norm, hu_bessel⟩

  obtain ⟨vT, uT, hT_eq, hT_norm, hT_bessel⟩ := h_decomp T
  obtain ⟨vX, uX, hX_eq, hX_norm, hX_bessel⟩ := h_decomp X
  let s := singularValues T
  let t := singularValues X
  have hs : ∀ i, 0 ≤ s i := fun _ => Real.sqrt_nonneg _
  have ht : ∀ j, 0 ≤ t j := fun _ => Real.sqrt_nonneg _
  let W : Fin (Module.finrank ℂ H) → Fin (Module.finrank ℂ H) → ℝ :=
    fun i j => (‖inner ℂ (vT i) (uX j)‖ ^ 2 + ‖inner ℂ (vX j) (uT i)‖ ^ 2) / 2
  have hW_nonneg : ∀ i j, 0 ≤ W i j := fun i j => by
    dsimp only [W]
    positivity

  
  have h_trace_le : ‖LinearMap.trace ℂ H (T ∘L X : H →L[ℂ] H)‖ ≤ ∑ i, ∑ j, s i * t j * W i j := by
    have h_tr_eq : LinearMap.trace ℂ H (T ∘L X : H →L[ℂ] H) =
        ∑ i, ∑ j, (s i : ℂ) * (t j : ℂ) * inner ℂ (vT i) (uX j) * inner ℂ (vX j) (uT i) := by
      rw [LinearMap.trace_eq_sum_inner ((T ∘L X : H →L[ℂ] H) : H →ₗ[ℂ] H) vX]
      have h_term : ∀ j, inner ℂ (vX j) (((T ∘L X : H →L[ℂ] H) : H →ₗ[ℂ] H) (vX j)) =
          ∑ i, (s i : ℂ) * (t j : ℂ) * inner ℂ (vT i) (uX j) * inner ℂ (vX j) (uT i) := by
        intro j
        change inner ℂ (vX j) (T (X (vX j))) = _
        have huX_exp : T (uX j) = ∑ i, inner ℂ (vT i) (uX j) • ((s i : ℂ) • uT i) := by
          conv_lhs => rw [← vT.sum_repr' (uX j)]
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [T.map_smul, hT_eq i]
        rw [hX_eq j, T.map_smul, huX_exp, inner_smul_right, inner_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_smul_right, inner_smul_right]
        ring
      simp_rw [h_term]
      exact Finset.sum_comm
    calc ‖LinearMap.trace ℂ H (T ∘L X : H →L[ℂ] H)‖
        = ‖∑ i, ∑ j, (s i : ℂ) * (t j : ℂ) * inner ℂ (vT i) (uX j) * inner ℂ (vX j) (uT i)‖ := by
          rw [h_tr_eq]
      _ ≤ ∑ i, ‖∑ j, (s i : ℂ) * (t j : ℂ) * inner ℂ (vT i) (uX j) * inner ℂ (vX j) (uT i)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖(s i : ℂ) * (t j : ℂ) * inner ℂ (vT i) (uX j) * inner ℂ (vX j) (uT i)‖ :=
          Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ = ∑ i, ∑ j, s i * t j * (‖inner ℂ (vT i) (uX j)‖ * ‖inner ℂ (vX j) (uT i)‖) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          simp only [norm_mul, Complex.norm_of_nonneg (hs i), Complex.norm_of_nonneg (ht j)]
          ring
      _ ≤ ∑ i, ∑ j, s i * t j * W i j := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hs i) (ht j))
          dsimp only [W]
          have h2 := two_mul_le_add_sq ‖inner ℂ (vT i) (uX j)‖ ‖inner ℂ (vX j) (uT i)‖
          linarith

  
  have hW_row : ∀ i, ∑ j, W i j ≤ 1 := by
    intro i
    dsimp only [W]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    have h1 : ∑ j, ‖inner ℂ (vT i) (uX j)‖ ^ 2 ≤ 1 := by
      have hsym : ∑ j, ‖inner ℂ (vT i) (uX j)‖ ^ 2 = ∑ j, ‖inner ℂ (uX j) (vT i)‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [norm_inner_symm]
      rw [hsym]
      calc ∑ j, ‖inner ℂ (uX j) (vT i)‖ ^ 2 ≤ ‖vT i‖ ^ 2 := hX_bessel (vT i)
        _ = 1 := by rw [vT.orthonormal.1 i, one_pow]
    have h2 : ∑ j, ‖inner ℂ (vX j) (uT i)‖ ^ 2 ≤ 1 := by
      have h_b := vX.orthonormal.sum_inner_products_le (s := Finset.univ) (uT i)
      have h_n := hT_norm i
      have h_nn := norm_nonneg (uT i)
      nlinarith
    linarith

  have hW_col : ∀ j, ∑ i, W i j ≤ 1 := by
    intro j
    dsimp only [W]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    have h1 : ∑ i, ‖inner ℂ (vT i) (uX j)‖ ^ 2 ≤ 1 := by
      have h_b := vT.orthonormal.sum_inner_products_le (s := Finset.univ) (uX j)
      have h_n := hX_norm j
      have h_nn := norm_nonneg (uX j)
      nlinarith
    have h2 : ∑ i, ‖inner ℂ (vX j) (uT i)‖ ^ 2 ≤ 1 := by
      have hsym : ∑ i, ‖inner ℂ (vX j) (uT i)‖ ^ 2 = ∑ i, ‖inner ℂ (uT i) (vX j)‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [norm_inner_symm]
      rw [hsym]
      calc ∑ i, ‖inner ℂ (uT i) (vX j)‖ ^ 2 ≤ ‖vX j‖ ^ 2 := hT_bessel (vX j)
        _ = 1 := by rw [vX.orthonormal.1 j, one_pow]
    linarith

  
  have hpq_conj : p.HolderConjugate q :=
    Real.holderConjugate_iff.mpr ⟨hp, by simpa only [one_div] using hpq⟩
  have hq : 1 < q := (Real.holderConjugate_iff.mp hpq_conj.symm).1
  have hp_pos : 0 < p := zero_lt_one.trans hp
  have hq_pos : 0 < q := zero_lt_one.trans hq

  let f : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H) → ℝ :=
    fun x => s x.1 * W x.1 x.2 ^ (1 / p)
  let g : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H) → ℝ :=
    fun x => t x.2 * W x.1 x.2 ^ (1 / q)

  have hf_nn : ∀ x ∈ (Finset.univ : Finset (Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H))), 0 ≤ f x :=
    fun x _ => mul_nonneg (hs x.1) (Real.rpow_nonneg (hW_nonneg x.1 x.2) _)
  have hg_nn : ∀ x ∈ (Finset.univ : Finset (Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H))), 0 ≤ g x :=
    fun x _ => mul_nonneg (ht x.2) (Real.rpow_nonneg (hW_nonneg x.1 x.2) _)

  have h_sum_fg : ∑ i, ∑ j, s i * t j * W i j = ∑ x, f x * g x := by
    rw [← Fintype.sum_prod_type (fun x : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H) =>
      s x.1 * t x.2 * W x.1 x.2)]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only [f, g]
    have hW_split : W x.1 x.2 ^ (1 / p) * W x.1 x.2 ^ (1 / q) = W x.1 x.2 := by
      rw [← Real.rpow_add' (hW_nonneg x.1 x.2) (by rw [hpq]; exact one_ne_zero), hpq, Real.rpow_one]
    calc s x.1 * t x.2 * W x.1 x.2
        = s x.1 * t x.2 * (W x.1 x.2 ^ (1 / p) * W x.1 x.2 ^ (1 / q)) := by rw [hW_split]
      _ = s x.1 * W x.1 x.2 ^ (1 / p) * (t x.2 * W x.1 x.2 ^ (1 / q)) := by ring

  have h_holder := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq_conj hf_nn hg_nn

  have h_fp_le : (∑ x, f x ^ p) ^ (1 / p) ≤ schattenNorm p T := by
    have h_sum_p : ∑ x, f x ^ p ≤ ∑ i, s i ^ p := by
      rw [Fintype.sum_prod_type]
      have h_pt : ∀ i j, f (i, j) ^ p = s i ^ p * W i j := by
        intro i j
        dsimp only [f]
        rw [Real.mul_rpow (hs i) (Real.rpow_nonneg (hW_nonneg i j) _),
          ← Real.rpow_mul (hW_nonneg i j), one_div_mul_cancel (ne_of_gt hp_pos), Real.rpow_one]
      simp_rw [h_pt, ← Finset.mul_sum]
      calc ∑ i, s i ^ p * (∑ j, W i j)
          ≤ ∑ i, s i ^ p * 1 :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hW_row i) (Real.rpow_nonneg (hs i) p)
        _ = ∑ i, s i ^ p := by simp only [mul_one]
    exact Real.rpow_le_rpow
      (Finset.sum_nonneg fun x h => Real.rpow_nonneg (hf_nn x h) p)
      h_sum_p (by positivity)

  have h_gq_le : (∑ x, g x ^ q) ^ (1 / q) ≤ schattenNorm q X := by
    have h_sum_q : ∑ x, g x ^ q ≤ ∑ j, t j ^ q := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      have h_qt : ∀ j i, g (i, j) ^ q = t j ^ q * W i j := by
        intro j i
        dsimp only [g]
        rw [Real.mul_rpow (ht j) (Real.rpow_nonneg (hW_nonneg i j) _),
          ← Real.rpow_mul (hW_nonneg i j), one_div_mul_cancel (ne_of_gt hq_pos), Real.rpow_one]
      simp_rw [h_qt, ← Finset.mul_sum]
      calc ∑ j, t j ^ q * (∑ i, W i j)
          ≤ ∑ j, t j ^ q * 1 :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (hW_col j) (Real.rpow_nonneg (ht j) q)
        _ = ∑ j, t j ^ q := by simp only [mul_one]
    exact Real.rpow_le_rpow
      (Finset.sum_nonneg fun x h => Real.rpow_nonneg (hg_nn x h) q)
      h_sum_q (by positivity)

  calc ‖LinearMap.trace ℂ H (T ∘L X : H →L[ℂ] H)‖
      ≤ ∑ i, ∑ j, s i * t j * W i j := h_trace_le
    _ = ∑ x, f x * g x := h_sum_fg
    _ ≤ (∑ x, f x ^ p) ^ (1 / p) * (∑ x, g x ^ q) ^ (1 / q) := h_holder
    _ ≤ schattenNorm p T * schattenNorm q X :=
        mul_le_mul h_fp_le h_gq_le
          (Real.rpow_nonneg (Finset.sum_nonneg fun x h => Real.rpow_nonneg (hg_nn x h) q) _)
          (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hs i) p) _)

end Leap
