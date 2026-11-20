import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Golden–Thompson inequality (premise of Wilde Lemma 17.3.3). -/
theorem golden_thompson (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (cfc Real.exp (A + B)).trace.re ≤ (cfc Real.exp A * cfc Real.exp B).trace.re := by
  by_cases hn : Nonempty n
  · have : Nonempty n := hn
    let _ : NormedAddCommGroup (Matrix n n ℂ) := Matrix.instL2OpNormedAddCommGroup
    let _ : NormedRing (Matrix n n ℂ) := Matrix.instL2OpNormedRing
    let _ : CStarRing (Matrix n n ℂ) := Matrix.instCStarRing
    let _ : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.instCStarAlgebra.toNormedAlgebra
    have hAsa : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
    have hBsa : IsSelfAdjoint B := Matrix.isHermitian_iff_isSelfAdjoint.mp hB
    have hABsa : IsSelfAdjoint (A + B) := Matrix.isHermitian_iff_isSelfAdjoint.mp (hA.add hB)
    have h_cfc_A : cfc Real.exp A = NormedSpace.exp A := CFC.real_exp_eq_normedSpace_exp
    have h_cfc_B : cfc Real.exp B = NormedSpace.exp B := CFC.real_exp_eq_normedSpace_exp
    have h_cfc_AB : cfc Real.exp (A + B) = NormedSpace.exp (A + B) := CFC.real_exp_eq_normedSpace_exp
    rw [h_cfc_AB, h_cfc_A, h_cfc_B]
    
    have h_pow_shift : ∀ (U V : Matrix n n ℂ) (m : ℕ), (U * V) ^ (m + 1) = U * (V * U) ^ m * V := by
      intro U V m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ (U * V) (m + 1), ih, pow_succ (V * U) m]
        simp only [mul_assoc]
    have h_tr_pow_comm : ∀ (U V : Matrix n n ℂ) (r : ℕ), ((U * V) ^ r).trace = ((V * U) ^ r).trace := by
      intro U V r
      cases r with
      | zero => simp
      | succ m =>
        rw [h_pow_shift U V m, mul_assoc U ((V * U) ^ m) V,
            Matrix.trace_mul_comm U (((V * U) ^ m) * V),
            mul_assoc ((V * U) ^ m) V U, ← pow_succ (V * U) m]
    have h_tr_conj_mul_nonneg : ∀ W : Matrix n n ℂ, 0 ≤ (Wᴴ * W).trace.re := by
      intro W
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
      simp only [RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
      exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    have h_tr_sq_le : ∀ Z : Matrix n n ℂ, (Z ^ 2).trace.re ≤ (Zᴴ * Z).trace.re := by
      intro Z
      have hpos := h_tr_conj_mul_nonneg (Z - Zᴴ)
      have hexp : (Z - Zᴴ)ᴴ * (Z - Zᴴ) = Zᴴ * Z - Zᴴ * Zᴴ - Z * Z + Z * Zᴴ := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, mul_sub, sub_mul, sub_mul]
        abel
      have htr : ((Z - Zᴴ)ᴴ * (Z - Zᴴ)).trace.re = 2 * (Zᴴ * Z).trace.re - 2 * (Z ^ 2).trace.re := by
        have h1 : (Z * Zᴴ).trace = (Zᴴ * Z).trace := Matrix.trace_mul_comm Z Zᴴ
        have h2 : (Zᴴ * Zᴴ).trace.re = (Z * Z).trace.re := by
          rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, RCLike.star_def, Complex.conj_re]
        rw [hexp, sq]
        simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, h1, h2]
        ring
      linarith
    have h_herm_amgm : ∀ (P Q : Matrix n n ℂ), P.IsHermitian → Q.IsHermitian →
        2 * (Q * P).trace.re ≤ (Q ^ 2).trace.re + (P ^ 2).trace.re := by
      intro P Q hP hQ
      have hpos := h_tr_conj_mul_nonneg (Q - P)
      have hexp : (Q - P)ᴴ * (Q - P) = Q ^ 2 - Q * P - P * Q + P ^ 2 := by
        rw [Matrix.conjTranspose_sub, hQ.eq, hP.eq, mul_sub, sub_mul, sub_mul, sq, sq]
        abel
      have htr : ((Q - P)ᴴ * (Q - P)).trace.re =
          (Q ^ 2).trace.re + (P ^ 2).trace.re - 2 * (Q * P).trace.re := by
        have hcomm : (P * Q).trace = (Q * P).trace := Matrix.trace_mul_comm P Q
        rw [hexp]
        simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, hcomm]
        ring
      linarith
    have h_dyadic : ∀ (k : ℕ) (X Y : Matrix n n ℂ), X.IsHermitian → Y.IsHermitian →
        ((X * Y) ^ (2 ^ k)).trace.re ≤ (X ^ (2 ^ k) * Y ^ (2 ^ k)).trace.re := by
      intro k
      induction k using Nat.case_strong_induction_on with
      | hz =>
        intro X Y _ _
        simp
      | hi k ih =>
        have hL : ∀ j ≤ k, ∀ M : Matrix n n ℂ,
            (((M ^ 2)ᴴ * M ^ 2) ^ (2 ^ j)).trace.re ≤ ((Mᴴ * M) ^ (2 ^ (j + 1))).trace.re := by
          intro j hj M
          let P : Matrix n n ℂ := Mᴴ * M
          let Q : Matrix n n ℂ := M * Mᴴ
          have hP : P.IsHermitian := by
            rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          have hQ : Q.IsHermitian := by
            rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          let U : Matrix n n ℂ := Mᴴ * Mᴴ * M
          have hUM : U * M = (M ^ 2)ᴴ * M ^ 2 := by
            simp only [U, sq, Matrix.conjTranspose_mul, mul_assoc]
          have hMU : M * U = Q * P := by
            simp only [U, P, Q, mul_assoc]
          have htr1 : (((M ^ 2)ᴴ * M ^ 2) ^ (2 ^ j)).trace = ((Q * P) ^ (2 ^ j)).trace := by
            rw [← hUM, h_tr_pow_comm U M (2 ^ j), hMU]
          have h_ih_qp : ((Q * P) ^ (2 ^ j)).trace.re ≤ (Q ^ (2 ^ j) * P ^ (2 ^ j)).trace.re :=
            ih j hj Q P hQ hP
          have h_cs : 2 * (Q ^ (2 ^ j) * P ^ (2 ^ j)).trace.re ≤
              ((Q ^ (2 ^ j)) ^ 2).trace.re + ((P ^ (2 ^ j)) ^ 2).trace.re :=
            h_herm_amgm (P ^ (2 ^ j)) (Q ^ (2 ^ j)) (hP.pow (2 ^ j)) (hQ.pow (2 ^ j))
          have hpowQ : (Q ^ (2 ^ j)) ^ 2 = Q ^ (2 ^ (j + 1)) := by
            rw [← pow_mul, ← pow_succ]
          have hpowP : (P ^ (2 ^ j)) ^ 2 = P ^ (2 ^ (j + 1)) := by
            rw [← pow_mul, ← pow_succ]
          have htrQP : (Q ^ (2 ^ (j + 1))).trace = (P ^ (2 ^ (j + 1))).trace :=
            h_tr_pow_comm M Mᴴ (2 ^ (j + 1))
          rw [htr1]
          rw [hpowQ, hpowP, htrQP] at h_cs
          linarith
        have h_tele : ∀ m ≤ k, ∀ M : Matrix n n ℂ,
            (((M ^ (2 ^ m))ᴴ * M ^ (2 ^ m)) ^ (2 ^ (k - m))).trace.re ≤
              ((Mᴴ * M) ^ (2 ^ k)).trace.re := by
          intro m
          induction m with
          | zero =>
            intro _ M
            simp
          | succ m ihm =>
            intro hm M
            have hmk : m ≤ k := Nat.le_of_succ_le hm
            have hsub : k - (m + 1) + 1 = k - m := by omega
            have hpowM : M ^ (2 ^ (m + 1)) = (M ^ (2 ^ m)) ^ 2 := by
              rw [pow_succ 2 m, pow_mul]
            have hstep := hL (k - (m + 1)) (Nat.sub_le k (m + 1)) (M ^ (2 ^ m))
            rw [← hpowM, hsub] at hstep
            exact le_trans hstep (ihm hmk M)
        intro X Y hX hY
        let M : Matrix n n ℂ := X * Y
        have h1 : ((X * Y) ^ (2 ^ (k + 1))).trace.re ≤ ((M ^ (2 ^ k))ᴴ * M ^ (2 ^ k)).trace.re := by
          have hpow : (X * Y) ^ (2 ^ (k + 1)) = (M ^ (2 ^ k)) ^ 2 := by
            rw [pow_succ 2 k, pow_mul]
          rw [hpow]
          exact h_tr_sq_le (M ^ (2 ^ k))
        have h2 : ((M ^ (2 ^ k))ᴴ * M ^ (2 ^ k)).trace.re ≤ ((Mᴴ * M) ^ (2 ^ k)).trace.re := by
          have hk := h_tele k (le_refl k) M
          simpa [Nat.sub_self] using hk
        have h3 : ((Mᴴ * M) ^ (2 ^ k)).trace = ((X ^ 2 * Y ^ 2) ^ (2 ^ k)).trace := by
          have hMM : Mᴴ * M = Y * (X ^ 2 * Y) := by
            simp only [M, Matrix.conjTranspose_mul, hX.eq, hY.eq, sq, mul_assoc]
          have hYY : (X ^ 2 * Y) * Y = X ^ 2 * Y ^ 2 := by
            simp only [sq, mul_assoc]
          rw [hMM, h_tr_pow_comm Y (X ^ 2 * Y) (2 ^ k), hYY]
        have h4 : ((X ^ 2 * Y ^ 2) ^ (2 ^ k)).trace.re ≤
            ((X ^ 2) ^ (2 ^ k) * (Y ^ 2) ^ (2 ^ k)).trace.re :=
          ih k (le_refl k) (X ^ 2) (Y ^ 2) (hX.pow 2) (hY.pow 2)
        have hpowX : (X ^ 2) ^ (2 ^ k) = X ^ (2 ^ (k + 1)) := by
          rw [← pow_mul, ← pow_succ' 2 k]
        have hpowY : (Y ^ 2) ^ (2 ^ k) = Y ^ (2 ^ (k + 1)) := by
          rw [← pow_mul, ← pow_succ' 2 k]
        rw [hpowX, hpowY] at h4
        have h3re : ((Mᴴ * M) ^ (2 ^ k)).trace.re = ((X ^ 2 * Y ^ 2) ^ (2 ^ k)).trace.re :=
          congrArg Complex.re h3
        linarith
    
    let u : ℝ → Matrix n n ℂ := fun t => NormedSpace.exp (t • A) * NormedSpace.exp (t • B)
    let v : ℝ → Matrix n n ℂ := fun t => NormedSpace.exp (t • (A + B))
    have hu0 : u 0 = 1 := by simp [u, NormedSpace.exp_zero]
    have hv0 : v 0 = 1 := by simp [v, NormedSpace.exp_zero]
    have hderiv_exp : ∀ M : Matrix n n ℂ, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • M)) M 0 := by
      intro M
      simpa [NormedSpace.exp_zero] using hasDerivAt_exp_smul_const M (0 : ℝ)
    have hu_deriv : HasDerivAt u (A + B) 0 := by
      change HasDerivAt ((fun t : ℝ => NormedSpace.exp (t • A)) * (fun t : ℝ => NormedSpace.exp (t • B))) (A + B) 0
      simpa [NormedSpace.exp_zero] using (hderiv_exp A).mul (hderiv_exp B)
    have hv_deriv : HasDerivAt v (A + B) 0 := hderiv_exp (A + B)
    have huv_deriv : HasDerivAt (fun t => u t - v t) 0 0 := by
      change HasDerivAt (u - v) 0 0
      simpa [sub_self] using hu_deriv.sub hv_deriv
    have ht_tendsto : Filter.Tendsto (fun N : ℕ => (N : ℝ)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have huv_lim : Filter.Tendsto (fun N : ℕ => (N : ℝ) * ‖u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹‖)
        Filter.atTop (nhds 0) := by
      refine ((hasDerivAt_iff_tendsto.mp huv_deriv).comp ht_tendsto).congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN))
      simp [hu0, hv0, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN_pos)]
    let K : ℝ := ‖A + B‖ + 1
    have hK_pos : 0 < K := by positivity
    have hexp_bound : ∀ g : ℝ → Matrix n n ℂ, g 0 = 1 → HasDerivAt g (A + B) 0 →
        ∀ᶠ N : ℕ in Filter.atTop, ‖g (N : ℝ)⁻¹‖ ≤ Real.exp (K / (N : ℝ)) := by
      intro g hg0 hg
      have hlim : Filter.Tendsto
          (fun N : ℕ => (N : ℝ) * ‖g (N : ℝ)⁻¹ - 1 - (N : ℝ)⁻¹ • (A + B)‖)
          Filter.atTop (nhds 0) := by
        refine ((hasDerivAt_iff_tendsto.mp hg).comp ht_tendsto).congr' ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN))
        simp [hg0, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN_pos)]
      have hev_lt : ∀ᶠ N : ℕ in Filter.atTop,
          (N : ℝ) * ‖g (N : ℝ)⁻¹ - 1 - (N : ℝ)⁻¹ • (A + B)‖ < 1 :=
        (tendsto_order.mp hlim).2 1 zero_lt_one
      filter_upwards [Filter.eventually_ge_atTop 1, hev_lt] with N hN hlt
      have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN))
      have herr : ‖g (N : ℝ)⁻¹ - 1 - (N : ℝ)⁻¹ • (A + B)‖ ≤ 1 / (N : ℝ) := by
        rw [le_div_iff₀ hN_pos, mul_comm]
        exact le_of_lt hlt
      have hsplit : g (N : ℝ)⁻¹ =
          (1 + (N : ℝ)⁻¹ • (A + B)) + (g (N : ℝ)⁻¹ - 1 - (N : ℝ)⁻¹ • (A + B)) := by
        abel
      have hnorm_smul : ‖(N : ℝ)⁻¹ • (A + B)‖ = ‖A + B‖ / (N : ℝ) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN_pos), inv_mul_eq_div]
      have hnorm1 : ‖(1 : Matrix n n ℂ)‖ = 1 := norm_one
      calc ‖g (N : ℝ)⁻¹‖
          = ‖(1 + (N : ℝ)⁻¹ • (A + B)) + (g (N : ℝ)⁻¹ - 1 - (N : ℝ)⁻¹ • (A + B))‖ := by
            rw [← hsplit]
        _ ≤ ‖(1 : Matrix n n ℂ) + (N : ℝ)⁻¹ • (A + B)‖ +
              ‖g (N : ℝ)⁻¹ - 1 - (N : ℝ)⁻¹ • (A + B)‖ := norm_add_le _ _
        _ ≤ (‖(1 : Matrix n n ℂ)‖ + ‖(N : ℝ)⁻¹ • (A + B)‖) + 1 / (N : ℝ) := by
            gcongr
            exact norm_add_le _ _
        _ = K / (N : ℝ) + 1 := by
            rw [hnorm1, hnorm_smul]
            simp only [K]
            ring
        _ ≤ Real.exp (K / (N : ℝ)) := Real.add_one_le_exp (K / (N : ℝ))
    have h_pow_sub_pow : ∀ (x y : Matrix n n ℂ) (N : ℕ),
        x ^ N - y ^ N = ∑ j ∈ Finset.range N, x ^ j * (x - y) * y ^ (N - 1 - j) := by
      intro x y N
      induction N with
      | zero => simp
      | succ m ihm =>
        simp only [Nat.add_sub_cancel]
        rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
        have hsum : (∑ j ∈ Finset.range m, x ^ j * (x - y) * y ^ (m - j)) =
            (∑ j ∈ Finset.range m, x ^ j * (x - y) * y ^ (m - 1 - j)) * y := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjm : j < m := Finset.mem_range.mp hj
          have hsub : m - j = m - 1 - j + 1 := by omega
          rw [hsub, pow_succ y (m - 1 - j), ← mul_assoc]
        rw [hsum, ← ihm, sub_mul, mul_sub, pow_succ x m, pow_succ y m]
        abel
    have h_lie_trotter : Filter.Tendsto (fun N : ℕ => u (N : ℝ)⁻¹ ^ N)
        Filter.atTop (nhds (NormedSpace.exp (A + B))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h_upper : Filter.Tendsto
          (fun N : ℕ => Real.exp K * ((N : ℝ) * ‖u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹‖))
          Filter.atTop (nhds 0) := by
        simpa [mul_zero] using huv_lim.const_mul (Real.exp K)
      refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h_upper
      filter_upwards [Filter.eventually_ge_atTop 1,
                      hexp_bound u hu0 hu_deriv,
                      hexp_bound v hv0 hv_deriv] with N hN huN hvN
      have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hN)
      have hv_pow : v (N : ℝ)⁻¹ ^ N = NormedSpace.exp (A + B) := by
        dsimp only [v]
        rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
            mul_inv_cancel₀ hN_ne, one_smul]
      rw [← hv_pow, h_pow_sub_pow]
      let C : ℝ := Real.exp (K / (N : ℝ))
      have hC_one : 1 ≤ C := Real.one_le_exp (by positivity)
      have hC_nonneg : 0 ≤ C := by positivity
      have hC_pow : C ^ N = Real.exp K := by
        dsimp only [C]
        rw [← Real.exp_nat_mul, mul_div_cancel₀ K hN_ne]
      calc ‖∑ j ∈ Finset.range N,
              u (N : ℝ)⁻¹ ^ j * (u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹) * v (N : ℝ)⁻¹ ^ (N - 1 - j)‖
          ≤ ∑ j ∈ Finset.range N,
              ‖u (N : ℝ)⁻¹ ^ j * (u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹) * v (N : ℝ)⁻¹ ^ (N - 1 - j)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.range N, Real.exp K * ‖u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹‖ := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjN : j < N := Finset.mem_range.mp hj
            have hidx : j + (N - 1 - j) = N - 1 := by omega
            have hN1 : N - 1 ≤ N := Nat.sub_le N 1
            calc ‖u (N : ℝ)⁻¹ ^ j * (u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹) * v (N : ℝ)⁻¹ ^ (N - 1 - j)‖
                ≤ ‖u (N : ℝ)⁻¹ ^ j * (u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹)‖ * ‖v (N : ℝ)⁻¹ ^ (N - 1 - j)‖ :=
                  norm_mul_le _ _
              _ ≤ (‖u (N : ℝ)⁻¹ ^ j‖ * ‖u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹‖) * ‖v (N : ℝ)⁻¹ ^ (N - 1 - j)‖ := by
                  gcongr
                  exact norm_mul_le _ _
              _ ≤ (C ^ j * ‖u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹‖) * C ^ (N - 1 - j) := by
                  gcongr
                  · exact le_trans (norm_pow_le _ _) (pow_le_pow_left₀ (norm_nonneg _) huN j)
                  · exact le_trans (norm_pow_le _ _) (pow_le_pow_left₀ (norm_nonneg _) hvN (N - 1 - j))
              _ = C ^ (j + (N - 1 - j)) * ‖u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹‖ := by
                  rw [pow_add]
                  ring
              _ = C ^ (N - 1) * ‖u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹‖ := by rw [hidx]
              _ ≤ C ^ N * ‖u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹‖ := by gcongr
              _ = Real.exp K * ‖u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹‖ := by rw [hC_pow]
        _ = Real.exp K * ((N : ℝ) * ‖u (N : ℝ)⁻¹ - v (N : ℝ)⁻¹‖) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    
    have h_subseq : Filter.Tendsto
        (fun k : ℕ => ((u (((2 ^ k : ℕ) : ℝ)⁻¹)) ^ (2 ^ k)).trace.re)
        Filter.atTop (nhds (NormedSpace.exp (A + B)).trace.re) := by
      have h_cont : Continuous (fun M : Matrix n n ℂ => M.trace.re) :=
        Complex.continuous_re.comp continuous_id.matrix_trace
      have h_pow2 : Filter.Tendsto (fun k : ℕ => 2 ^ k) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt one_lt_two
      exact (h_cont.tendsto _).comp (h_lie_trotter.comp h_pow2)
    refine le_of_tendsto' h_subseq fun k => ?_
    let ck : ℝ := (((2 ^ k : ℕ) : ℝ)⁻¹)
    have hX_herm : (NormedSpace.exp (ck • A)).IsHermitian := by
      have hsmul : (ck • A).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hA.eq]
      exact hsmul.exp
    have hY_herm : (NormedSpace.exp (ck • B)).IsHermitian := by
      have hsmul : (ck • B).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hB.eq]
      exact hsmul.exp
    have hpow_exp : ∀ M : Matrix n n ℂ, (NormedSpace.exp (ck • M)) ^ (2 ^ k) = NormedSpace.exp M := by
      intro M
      have h2k_ne : ((2 ^ k : ℕ) : ℝ) ≠ 0 := by positivity
      rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          mul_inv_cancel₀ h2k_ne, one_smul]
    have hbound := h_dyadic k (NormedSpace.exp (ck • A)) (NormedSpace.exp (ck • B)) hX_herm hY_herm
    simpa only [u, ck, hpow_exp A, hpow_exp B] using hbound
  · have : IsEmpty n := not_nonempty_iff.mp hn
    simp [Matrix.trace]

end Leap
