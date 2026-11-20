import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Wilde Ex 11.9.2 / Thm 11.6.1: Holevo bound for one finite-outcome POVM. -/
theorem holevo_bound {ι o : Type*} [Fintype ι] [Fintype o]
    (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x) (hps : ∑ x, p x = 1)
    (ρ : ι → Matrix n n ℂ) (hρ : ∀ x, (ρ x).PosSemidef) (htr : ∀ x, (ρ x).trace = 1)
    (Λ : o → Matrix n n ℂ) (hΛ : ∀ y, (Λ y).PosSemidef) (hΛ1 : ∑ y, Λ y = 1) :
    let P : ι → o → ℝ := fun x y => p x * (Λ y * ρ x).trace.re
    let q : o → ℝ := fun y => ∑ x, P x y
    (∑ x, ∑ y, P x y * Real.log (P x y / (p x * q y))) ≤
      vnEntropy (∑ x, (p x : ℂ) • ρ x) - ∑ x, p x * vnEntropy (ρ x) := by
  have _ : (∑ x, p x = 1) ∧ (∀ x, (ρ x).trace = 1) := ⟨hps, htr⟩
  have h_norm_mul_star : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h_ofReal_nn : ∀ {r : ℝ}, 0 ≤ r → 0 ≤ (r : ℂ) := fun hr =>
    Complex.le_def.mpr ⟨by simpa using hr, by simp⟩
  
  have h_vn : ∀ (A : Matrix n n ℂ) (hA : A.IsHermitian),
      vnEntropy A = - ∑ i : n, hA.eigenvalues i * Real.log (hA.eigenvalues i) := by
    intro A hA
    rw [Leap.vnEntropy.eq_def, neg_inj]
    let Φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
    let d1 : n → ℂ := RCLike.ofReal ∘ hA.eigenvalues
    let d2 : n → ℂ := RCLike.ofReal ∘ Real.log ∘ hA.eigenvalues
    have hA_eq : A = Φ (Matrix.diagonal d1) := hA.spectral_theorem
    have hcfc_eq : cfc Real.log A = Φ (Matrix.diagonal d2) := by
      rw [hA.cfc_eq, Matrix.IsHermitian.cfc.eq_def]
    have hprod : A * cfc Real.log A =
        (hA.eigenvectorUnitary : Matrix n n ℂ) *
          Matrix.diagonal (fun i => ((hA.eigenvalues i * Real.log (hA.eigenvalues i) : ℝ) : ℂ)) *
          star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
      refine (congr_arg₂ (· * ·) hA_eq hcfc_eq).trans ?_
      rw [← map_mul, Matrix.diagonal_mul_diagonal, Unitary.conjStarAlgAut_apply]
      congr 2
      ext i
      simp [d1, d2]
    rw [hprod, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
    simp
  
  have h_trace_conj : ∀ (A : Matrix n n ℂ) (hA : A.IsHermitian)
      (V : unitary (Matrix n n ℂ)) (β : n → ℝ),
      let U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
      let lam : n → ℝ := hA.eigenvalues
      (∀ i : n, ∑ j : n, ‖(star U * (V : Matrix n n ℂ)) i j‖ ^ 2 = 1) ∧
      ((((V : Matrix n n ℂ) * Matrix.diagonal (fun j => (β j : ℂ)) * star (V : Matrix n n ℂ)) * A).trace.re =
        ∑ i : n, ∑ j : n, ‖(star U * (V : Matrix n n ℂ)) i j‖ ^ 2 * lam i * β j) := by
    intro A hA V β
    dsimp only
    set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
    set lam : n → ℝ := hA.eigenvalues
    set Vm : Matrix n n ℂ := (V : Matrix n n ℂ)
    let Wu : unitary (Matrix n n ℂ) := star hA.eigenvectorUnitary * V
    let W : Matrix n n ℂ := (Wu : Matrix n n ℂ)
    have hW_def : W = star U * Vm := rfl
    refine ⟨?_, ?_⟩
    · intro i
      have hWW : W * star W = 1 := Unitary.coe_mul_star_self Wu
      have hii := congr_arg (fun M : Matrix n n ℂ => (M i i).re) hWW
      rw [Matrix.mul_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at hii
      rw [← hii, ← hW_def]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : W i j * (star W) j i = ((‖W i j‖ ^ 2 : ℝ) : ℂ) := by
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
        exact h_norm_mul_star (W i j)
      rw [hj, Complex.ofReal_re]
    · have hA_eq : A = U * Matrix.diagonal (fun i => (lam i : ℂ)) * star U := by
        have hs := hA.spectral_theorem
        rw [Unitary.conjStarAlgAut_apply] at hs
        exact hs
      let Dbeta : Matrix n n ℂ := Matrix.diagonal (fun j => (β j : ℂ))
      let Dlam : Matrix n n ℂ := Matrix.diagonal (fun i => (lam i : ℂ))
      have hstarW : star W = star Vm * U := by
        simp [hW_def, star_mul]
      have htr_eq : ((Vm * Dbeta * star Vm) * A).trace = ((W * Dbeta * star W) * Dlam).trace := by
        have h1 : (Vm * Dbeta * star Vm) * A = ((Vm * Dbeta * star Vm) * (U * Dlam)) * star U := by
          rw [hA_eq]
          simp only [Dlam, Matrix.mul_assoc]
        rw [h1, Matrix.trace_mul_comm]
        congr 1
        rw [hstarW, hW_def]
        simp only [Matrix.mul_assoc]
      rw [htr_eq]
      simp only [Matrix.trace, Matrix.diag_apply, Dlam, Dbeta, Matrix.mul_diagonal]
      have hdiag : ∀ i : n, ((W * Matrix.diagonal (fun j => (β j : ℂ)) * star W) i i * (lam i : ℂ)) =
          ∑ j : n, ((‖W i j‖ ^ 2 * lam i * β j : ℝ) : ℂ) := by
        intro i
        rw [Matrix.mul_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
        have h1 : W i j * (β j : ℂ) * star (W i j) * (lam i : ℂ) =
            (W i j * star (W i j)) * (lam i : ℂ) * (β j : ℂ) := by ring
        rw [h1, h_norm_mul_star]
        push_cast
        ring
      simp_rw [hdiag]
      rw [← hW_def]
      norm_cast
  have h_psd_tr : ∀ (M N : Matrix n n ℂ), M.PosSemidef → N.PosSemidef → 0 ≤ (M * N).trace.re := by
    intro M N hM hN
    have hHM := hM.isHermitian
    have hHN := hN.isHermitian
    have hM_eq : M = (hHM.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun j => (hHM.eigenvalues j : ℂ)) *
        star (hHM.eigenvectorUnitary : Matrix n n ℂ) := by
      have hs := hHM.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at hs
      exact hs
    rw [hM_eq, (h_trace_conj N hHN hHM.eigenvectorUnitary hHM.eigenvalues).2]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hN.eigenvalues_nonneg i)) (hM.eigenvalues_nonneg j)
  
  have h_crux : ∀ (A : Matrix n n ℂ) (hA : A.PosSemidef)
      (V : unitary (Matrix n n ℂ)) (ν : n → ℝ) (_hν : ∀ j, 0 < ν j)
      (s : ℝ) (_hs0 : 0 < s) (_hs1 : s < 1),
      let B : Matrix n n ℂ := (V : Matrix n n ℂ) * Matrix.diagonal (fun j => (ν j : ℂ)) * star (V : Matrix n n ℂ)
      let U : Matrix n n ℂ := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
      let lam : n → ℝ := hA.isHermitian.eigenvalues
      (∑ y : o, ((Λ y * A).trace.re) ^ 2 / ((1 - s) * (Λ y * A).trace.re + s * (Λ y * B).trace.re)) ≤
        ∑ i : n, ∑ j : n, ‖(star U * (V : Matrix n n ℂ)) i j‖ ^ 2 *
          ((lam i) ^ 2 / ((1 - s) * lam i + s * ν j)) := by
    intro A hA V ν hν s hs0 hs1
    dsimp only
    set Vm : Matrix n n ℂ := (V : Matrix n n ℂ)
    set Dnu : Matrix n n ℂ := Matrix.diagonal (fun j => (ν j : ℂ))
    set B : Matrix n n ℂ := Vm * Dnu * star Vm
    set hHA := hA.isHermitian
    set U : Matrix n n ℂ := (hHA.eigenvectorUnitary : Matrix n n ℂ)
    set lam : n → ℝ := hHA.eigenvalues
    set Dlam : Matrix n n ℂ := Matrix.diagonal (fun i => (lam i : ℂ))
    let W : Matrix n n ℂ := star U * Vm
    have hW_def : W = star U * Vm := rfl
    have hs1' : 0 < 1 - s := sub_pos.mpr hs1
    have hlam_nn : ∀ i, 0 ≤ lam i := hA.eigenvalues_nonneg
    have hB : B.PosSemidef := by
      have hDnu : Dnu.PosSemidef := Matrix.PosSemidef.diagonal fun j =>
        h_ofReal_nn (le_of_lt (hν j))
      simpa only [B, Matrix.star_eq_conjTranspose] using hDnu.mul_mul_conjTranspose_same Vm
    let a : o → ℝ := fun y => (Λ y * A).trace.re
    let b : o → ℝ := fun y => (Λ y * B).trace.re
    have ha_nn : ∀ y, 0 ≤ a y := fun y => h_psd_tr (Λ y) A (hΛ y) hA
    have hb_nn : ∀ y, 0 ≤ b y := fun y => h_psd_tr (Λ y) B (hΛ y) hB
    let d : n → n → ℝ := fun i j => (1 - s) * lam i + s * ν j
    have hd_pos : ∀ i j, 0 < d i j := fun i j =>
      add_pos_of_nonneg_of_pos (mul_nonneg (le_of_lt hs1') (hlam_nn i)) (mul_pos hs0 (hν j))
    let Ms : Matrix n n ℂ := Matrix.of (fun i j => ((lam i / d i j : ℝ) : ℂ) * W i j)
    let Ws : Matrix n n ℂ := U * Ms * star Vm
    have hA_eq : A = U * Dlam * star U := by
      have hs_thm := hHA.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at hs_thm
      exact hs_thm
    have hUU : star U * U = 1 := Unitary.coe_star_mul_self hHA.eigenvectorUnitary
    have hVV1 : star Vm * Vm = 1 := Unitary.coe_star_mul_self V
    have hVV2 : Vm * star Vm = 1 := Unitary.coe_mul_star_self V
    have hAWs : A * Ws = U * (Dlam * Ms) * star Vm := by
      refine (congr_arg (· * Ws) hA_eq).trans ?_
      calc (U * Dlam * star U) * (U * Ms * star Vm)
          = U * Dlam * (star U * U) * Ms * star Vm := by simp only [Matrix.mul_assoc]
        _ = U * (Dlam * Ms) * star Vm := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have hWsB : Ws * B = U * (Ms * Dnu) * star Vm := by
      calc Ws * B = (U * Ms * star Vm) * (Vm * Dnu * star Vm) := rfl
        _ = U * Ms * (star Vm * Vm) * Dnu * star Vm := by simp only [Matrix.mul_assoc]
        _ = U * (Ms * Dnu) * star Vm := by rw [hVV1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have hSylv_mid : ((1 - s : ℝ) : ℂ) • (Dlam * Ms) + ((s : ℝ) : ℂ) • (Ms * Dnu) = Dlam * W := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Dlam, Dnu,
        Matrix.diagonal_mul, Matrix.mul_diagonal, Ms, Matrix.of_apply]
      have hd_ne : (d i j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hd_pos i j))
      have hcomb : ((1 - s : ℝ) : ℂ) * ((lam i : ℂ) * (((lam i / d i j : ℝ) : ℂ) * W i j)) +
          ((s : ℝ) : ℂ) * ((((lam i / d i j : ℝ) : ℂ) * W i j) * (ν j : ℂ)) =
          ((d i j : ℂ) * ((lam i / d i j : ℝ) : ℂ)) * W i j := by
        simp only [d]
        push_cast
        ring
      rw [hcomb]
      push_cast
      rw [mul_div_cancel₀ _ hd_ne]
    have hSylv : ((1 - s : ℝ) : ℂ) • (A * Ws) + ((s : ℝ) : ℂ) • (Ws * B) = A := by
      rw [hAWs, hWsB]
      calc ((1 - s : ℝ) : ℂ) • (U * (Dlam * Ms) * star Vm) + ((s : ℝ) : ℂ) • (U * (Ms * Dnu) * star Vm)
          = U * (((1 - s : ℝ) : ℂ) • (Dlam * Ms) + ((s : ℝ) : ℂ) • (Ms * Dnu)) * star Vm := by
              simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
        _ = U * (Dlam * W) * star Vm := by rw [hSylv_mid]
        _ = (U * Dlam * star U) * (Vm * star Vm) := by simp only [hW_def, Matrix.mul_assoc]
        _ = A := by rw [hVV2, Matrix.mul_one, ← hA_eq]
    have hWsA_tr : (star Ws * A).trace.re =
        ∑ i : n, ∑ j : n, ‖W i j‖ ^ 2 * ((lam i) ^ 2 / d i j) := by
      have hstarWs : star Ws = Vm * star Ms * star U := by
        simp only [Ws, star_mul, star_star, Matrix.mul_assoc]
      have hmul : star Ws * A = (Vm * star Ms) * (Dlam * star U) := by
        refine (congr_arg₂ (· * ·) hstarWs hA_eq).trans ?_
        calc (Vm * star Ms * star U) * (U * Dlam * star U)
            = Vm * star Ms * (star U * U) * Dlam * star U := by simp only [Matrix.mul_assoc]
          _ = (Vm * star Ms) * (Dlam * star U) := by rw [hUU, Matrix.mul_one, Matrix.mul_assoc]
      have htr : (star Ws * A).trace = ((Dlam * W) * star Ms).trace := by
        rw [hmul, Matrix.trace_mul_comm]
        simp only [hW_def, Matrix.mul_assoc]
      rw [htr]
      simp only [Matrix.trace, Matrix.diag_apply]
      have hdiag : ∀ i : n, ((Dlam * W) * star Ms) i i =
          ∑ j : n, ((‖W i j‖ ^ 2 * ((lam i) ^ 2 / d i j) : ℝ) : ℂ) := by
        intro i
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Dlam, Matrix.diagonal_mul, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_apply, Ms, Matrix.of_apply, star_mul', RCLike.star_def,
          Complex.conj_ofReal]
        have h1 : (lam i : ℂ) * W i j * (((lam i / d i j : ℝ) : ℂ) * (starRingEnd ℂ) (W i j)) =
            (W i j * star (W i j)) * ((lam i : ℂ) * ((lam i / d i j : ℝ) : ℂ)) := by
          simp only [RCLike.star_def]
          ring
        rw [h1, h_norm_mul_star]
        push_cast
        ring
      simp_rw [hdiag]
      norm_cast
    let z : o → ℝ := fun y => a y / ((1 - s) * a y + s * b y)
    let Z : Matrix n n ℂ := ∑ y : o, (z y : ℂ) • Λ y
    have hZ_star : star Z = Z := by
      simp only [Z, star_sum, star_smul, RCLike.star_def, Complex.conj_ofReal]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Matrix.star_eq_conjTranspose, (hΛ y).isHermitian.eq]
    let E : o → Matrix n n ℂ := fun y => (z y : ℂ) • (1 : Matrix n n ℂ) - Z
    have hE_star : ∀ y, (E y).conjTranspose = E y := by
      intro y
      rw [← Matrix.star_eq_conjTranspose]
      simp only [E, star_sub, star_smul, star_one, hZ_star, RCLike.star_def, Complex.conj_ofReal]
    let S : Matrix n n ℂ := ∑ y : o, (E y).conjTranspose * Λ y * E y
    have hS_psd : S.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun y _ => (hΛ y).conjTranspose_mul_mul_same (E y)
    have hS_eq : S = (∑ y : o, ((z y ^ 2 : ℝ) : ℂ) • Λ y) - Z * Z := by
      have hexp : ∀ y : o, (E y).conjTranspose * Λ y * E y =
          (((z y ^ 2 : ℝ) : ℂ) • Λ y - (z y : ℂ) • (Z * Λ y)) -
            ((z y : ℂ) • (Λ y * Z) - Z * Λ y * Z) := by
        intro y
        rw [hE_star y]
        simp only [E, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul, Matrix.mul_assoc]
        push_cast
        rw [sq]
      simp_rw [S, hexp, Finset.sum_sub_distrib]
      have hz1 : (∑ y : o, (z y : ℂ) • (Z * Λ y)) = Z * Z := by
        simp_rw [← Matrix.mul_smul, ← Finset.mul_sum]; rfl
      have hz2 : (∑ y : o, (z y : ℂ) • (Λ y * Z)) = Z * Z := by
        simp_rw [← Matrix.smul_mul, ← Finset.sum_mul]; rfl
      have hz3 : (∑ y : o, Z * Λ y * Z) = Z * Z := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hΛ1, Matrix.mul_one]
      rw [hz1, hz2, hz3, sub_self, sub_zero]
    let Cs : Matrix n n ℂ := ((1 - s : ℝ) : ℂ) • A + ((s : ℝ) : ℂ) • B
    have hCs_psd : Cs.PosSemidef :=
      (hA.smul (h_ofReal_nn (le_of_lt hs1'))).add
        (hB.smul (h_ofReal_nn (le_of_lt hs0)))
    have hSC_nn : 0 ≤ (S * Cs).trace.re := h_psd_tr S Cs hS_psd hCs_psd
    have hKadison : (Z * Z * Cs).trace.re ≤ ∑ y : o, z y ^ 2 * ((1 - s) * a y + s * b y) := by
      have htrS : (S * Cs).trace.re =
          (∑ y : o, z y ^ 2 * ((1 - s) * a y + s * b y)) - (Z * Z * Cs).trace.re := by
        rw [hS_eq, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
        congr 1
        simp only [Cs, Finset.sum_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add,
          Matrix.trace_sum, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
          Complex.re_sum, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, a, b]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      linarith
    let X : Matrix n n ℂ := Z - Ws
    let Q : Matrix n n ℂ := ((1 - s : ℝ) : ℂ) • (X.conjTranspose * A * X) +
      ((s : ℝ) : ℂ) • (X * B * X.conjTranspose)
    have hQ_psd : Q.PosSemidef :=
      ((hA.conjTranspose_mul_mul_same X).smul (h_ofReal_nn (le_of_lt hs1'))).add
        ((hB.mul_mul_conjTranspose_same X).smul (h_ofReal_nn (le_of_lt hs0)))
    have hQ_nn : 0 ≤ Q.trace.re := by
      simpa using h_psd_tr Q 1 hQ_psd Matrix.PosSemidef.one
    have hQ_tr : Q.trace.re = (Z * Z * Cs).trace.re - 2 * (Z * A).trace.re + (star Ws * A).trace.re := by
      have hXstar : X.conjTranspose = Z - star Ws := by
        rw [← Matrix.star_eq_conjTranspose, star_sub, hZ_star]
      let L : Matrix n n ℂ := ((1 - s : ℝ) : ℂ) • (Z * A * Ws) + ((s : ℝ) : ℂ) • (Ws * B * Z)
      have hL_tr : L.trace = (Z * A).trace := by
        have h1 : (Z * A * Ws).trace = (Z * (A * Ws)).trace := by rw [Matrix.mul_assoc]
        have h2 : (Ws * B * Z).trace = (Z * (Ws * B)).trace := Matrix.trace_mul_comm (Ws * B) Z
        calc L.trace = ((1 - s : ℝ) : ℂ) * (Z * A * Ws).trace + ((s : ℝ) : ℂ) * (Ws * B * Z).trace := by
              simp [L, Matrix.trace_add, Matrix.trace_smul]
          _ = (Z * (((1 - s : ℝ) : ℂ) • (A * Ws) + ((s : ℝ) : ℂ) • (Ws * B))).trace := by
              rw [h1, h2]
              simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
          _ = (Z * A).trace := by rw [hSylv]
      have hstarL : star L = ((1 - s : ℝ) : ℂ) • (star Ws * A * Z) + ((s : ℝ) : ℂ) • (Z * B * star Ws) := by
        have hAstar : star A = A := hHA.eq
        have hBstar : star B = B := hB.isHermitian.eq
        simp only [L, star_add, star_smul, star_mul, hZ_star, hAstar, hBstar,
          RCLike.star_def, Complex.conj_ofReal, Matrix.mul_assoc]
      have hstarL_tr : (star L).trace.re = (Z * A).trace.re := by
        rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose,
          hL_tr, RCLike.star_def, Complex.conj_re]
      have hQ_Z : (((1 - s : ℝ) : ℂ) • (Z * A * Z) + ((s : ℝ) : ℂ) • (Z * B * Z)).trace =
          (Z * Z * Cs).trace := by
        have h1 : (Z * A * Z).trace = (Z * Z * A).trace := by
          rw [Matrix.trace_mul_comm (Z * A) Z, Matrix.mul_assoc]
        have h2 : (Z * B * Z).trace = (Z * Z * B).trace := by
          rw [Matrix.trace_mul_comm (Z * B) Z, Matrix.mul_assoc]
        simp [Cs, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, h1, h2]
      have hQ_W : (((1 - s : ℝ) : ℂ) • (star Ws * A * Ws) + ((s : ℝ) : ℂ) • (Ws * B * star Ws)).trace =
          (star Ws * A).trace := by
        have h1 : (star Ws * A * Ws).trace = (star Ws * (A * Ws)).trace := by rw [Matrix.mul_assoc]
        have h2 : (Ws * B * star Ws).trace = (star Ws * (Ws * B)).trace :=
          Matrix.trace_mul_comm (Ws * B) (star Ws)
        calc (((1 - s : ℝ) : ℂ) • (star Ws * A * Ws) + ((s : ℝ) : ℂ) • (Ws * B * star Ws)).trace
            = ((1 - s : ℝ) : ℂ) * (star Ws * A * Ws).trace + ((s : ℝ) : ℂ) * (Ws * B * star Ws).trace := by
              simp [Matrix.trace_add, Matrix.trace_smul]
          _ = (star Ws * (((1 - s : ℝ) : ℂ) • (A * Ws) + ((s : ℝ) : ℂ) • (Ws * B))).trace := by
              rw [h1, h2]
              simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
          _ = (star Ws * A).trace := by rw [hSylv]
      have hQ_decomp : Q = (((1 - s : ℝ) : ℂ) • (Z * A * Z) + ((s : ℝ) : ℂ) • (Z * B * Z)) -
          L - star L + (((1 - s : ℝ) : ℂ) • (star Ws * A * Ws) + ((s : ℝ) : ℂ) • (Ws * B * star Ws)) := by
        simp only [Q, hXstar, hstarL, L]
        simp only [X, Matrix.sub_mul, Matrix.mul_sub, smul_sub, Matrix.mul_assoc]
        abel
      rw [hQ_decomp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
        hQ_Z, hL_tr, hQ_W, Complex.add_re, Complex.sub_re, Complex.sub_re, hstarL_tr]
      ring
    have hZA_tr : (Z * A).trace.re = ∑ y : o, z y * a y := by
      simp only [Z, Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
        smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, a]
    have h_term : ∀ y : o, z y ^ 2 * ((1 - s) * a y + s * b y) - 2 * (z y * a y) =
        - (a y ^ 2 / ((1 - s) * a y + s * b y)) := by
      intro y
      set den : ℝ := (1 - s) * a y + s * b y
      by_cases hden : den = 0
      · have hay0 : a y = 0 := by
          have h1 : 0 ≤ (1 - s) * a y := mul_nonneg (le_of_lt hs1') (ha_nn y)
          have h2 : 0 ≤ s * b y := mul_nonneg (le_of_lt hs0) (hb_nn y)
          have h3 : (1 - s) * a y = 0 := by linarith [show (1 - s) * a y + s * b y = 0 from hden]
          exact (mul_eq_zero.mp h3).resolve_left (ne_of_gt hs1')
        simp [z, den, hden, hay0]
      · simp only [z]
        change (a y / den) ^ 2 * den - 2 * (a y / den * a y) = - (a y ^ 2 / den)
        field_simp [hden]
        ring
    have hsum_combine : (∑ y : o, z y ^ 2 * ((1 - s) * a y + s * b y)) - 2 * (Z * A).trace.re =
        - ∑ y : o, a y ^ 2 / ((1 - s) * a y + s * b y) := by
      rw [hZA_tr, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      simpa only [mul_assoc] using h_term y
    linarith [hQ_nn, hQ_tr, hKadison, hsum_combine, hWsA_tr]
  
  have h_int_bound : ∀ (a b : o → ℝ),
      (∀ y, 0 ≤ a y) → (∀ y, 0 ≤ b y) → (∀ y, b y = 0 → a y = 0) →
      ∀ (w u v : n × n → ℝ),
      (∀ k, 0 ≤ w k) → (∀ k, 0 ≤ u k) → (∀ k, 0 < v k) →
      (∑ y : o, a y = ∑ k : n × n, w k * u k) →
      (∀ s : ℝ, 0 < s → s < 1 →
        (∑ y : o, (a y) ^ 2 / ((1 - s) * a y + s * b y)) ≤
          ∑ k : n × n, w k * ((u k) ^ 2 / ((1 - s) * u k + s * v k))) →
      (∑ y : o, a y * Real.log (a y / b y)) ≤ ∑ k : n × n, w k * (u k * Real.log (u k / v k)) := by
    intro a b ha hb hab w u v _hw hu hv hmass hquad
    let g : ℝ → ℝ → ℝ → ℝ := fun c d s => c * (c - d) / ((1 - s) * c + s * d)
    have h_scalar : ∀ (c d : ℝ), 0 ≤ c → (c = 0 ∨ 0 < d) →
        IntervalIntegrable (g c d) MeasureTheory.volume 0 1 ∧
        (∫ s in (0 : ℝ)..1, g c d s) = c * Real.log (c / d) ∧
        (∀ s : ℝ, 0 < s → s < 1 → c ^ 2 / ((1 - s) * c + s * d) - c = s * g c d s) := by
      intro c d hc hcd
      rcases eq_or_lt_of_le hc with rfl | hc_pos
      · have hg0 : g 0 d = fun _ => 0 := by
          funext s
          simp [g]
        refine ⟨by rw [hg0]; exact intervalIntegrable_const, by simp [hg0], ?_⟩
        intro s _ _
        simp [g]
      · have hd_pos : 0 < d := hcd.resolve_left (ne_of_gt hc_pos)
        let den : ℝ → ℝ := fun s => (1 - s) * c + s * d
        have hden_pos : ∀ s ∈ Set.uIcc (0 : ℝ) 1, 0 < den s := by
          rw [Set.uIcc_of_le zero_le_one]
          rintro s ⟨hs0, hs1⟩
          rcases eq_or_lt_of_le hs0 with rfl | hs0'
          · simp [den, hc_pos]
          · exact add_pos_of_nonneg_of_pos
              (mul_nonneg (sub_nonneg.mpr hs1) (le_of_lt hc_pos))
              (mul_pos hs0' hd_pos)
        have hcont_den : Continuous den :=
          (((continuous_const.sub continuous_id).mul continuous_const).add
            (continuous_id.mul continuous_const))
        have hcont_g : ContinuousOn (g c d) (Set.uIcc 0 1) :=
          continuousOn_const.div hcont_den.continuousOn fun s hs => ne_of_gt (hden_pos s hs)
        have hInt : IntervalIntegrable (g c d) MeasureTheory.volume 0 1 := hcont_g.intervalIntegrable
        let F : ℝ → ℝ := fun s => -c * Real.log (den s)
        have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (g c d s) s := by
          intro s hs
          have h1 : HasDerivAt den (((0 - 1) * c) + (1 * d)) s :=
            (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const c).add
              ((hasDerivAt_id s).mul_const d)
          have h2 := (h1.log (ne_of_gt (hden_pos s hs))).const_mul (-c)
          convert h2 using 1
          simp only [g, den]
          ring
        have hint_eq : (∫ s in (0 : ℝ)..1, g c d s) = c * Real.log (c / d) := by
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt]
          simp only [F, den, sub_self, zero_mul, one_mul, zero_add, sub_zero, add_zero]
          rw [Real.log_div (ne_of_gt hc_pos) (ne_of_gt hd_pos)]
          ring
        refine ⟨hInt, hint_eq, ?_⟩
        intro s hs0 hs1
        have hs_mem : s ∈ Set.uIcc (0 : ℝ) 1 := by
          rw [Set.uIcc_of_le zero_le_one]
          exact ⟨le_of_lt hs0, le_of_lt hs1⟩
        have hden_ne : den s ≠ 0 := ne_of_gt (hden_pos s hs_mem)
        change c ^ 2 / den s - c = s * (c * (c - d) / den s)
        field_simp [hden_ne]
        ring
    have hab_or : ∀ y : o, a y = 0 ∨ 0 < b y := fun y =>
      (eq_or_lt_of_le (hb y)).imp (fun h0 => hab y h0.symm) id
    have huv_or : ∀ k : n × n, u k = 0 ∨ 0 < v k := fun k => Or.inr (hv k)
    have h_le_Ioo : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
        (∑ y : o, g (a y) (b y) s) ≤ ∑ k : n × n, w k * g (u k) (v k) s := by
      rintro s ⟨hs0, hs1⟩
      have hL : (∑ y : o, (a y) ^ 2 / ((1 - s) * a y + s * b y)) - ∑ y : o, a y =
          s * ∑ y : o, g (a y) (b y) s := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => (h_scalar (a y) (b y) (ha y) (hab_or y)).2.2 s hs0 hs1
      have hR : (∑ k : n × n, w k * ((u k) ^ 2 / ((1 - s) * u k + s * v k))) - ∑ k : n × n, w k * u k =
          s * ∑ k : n × n, w k * g (u k) (v k) s := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_sub, (h_scalar (u k) (v k) (hu k) (huv_or k)).2.2 s hs0 hs1]
        ring
      have hsub : s * (∑ y : o, g (a y) (b y) s) ≤ s * ∑ k : n × n, w k * g (u k) (v k) s := by
        linarith [hquad s hs0 hs1, hmass, hL, hR]
      exact le_of_mul_le_mul_left hsub hs0
    have hIntL : IntervalIntegrable (fun s => ∑ y : o, g (a y) (b y) s) MeasureTheory.volume 0 1 := by
      have hfn : (fun s => ∑ y : o, g (a y) (b y) s) = ∑ y : o, g (a y) (b y) := by
        ext s; simp
      rw [hfn]
      exact IntervalIntegrable.sum Finset.univ fun y _ => (h_scalar (a y) (b y) (ha y) (hab_or y)).1
    have hIntR : IntervalIntegrable (fun s => ∑ k : n × n, w k * g (u k) (v k) s) MeasureTheory.volume 0 1 := by
      have hfn : (fun s => ∑ k : n × n, w k * g (u k) (v k) s) = ∑ k : n × n, fun s => w k * g (u k) (v k) s := by
        ext s; simp
      rw [hfn]
      exact IntervalIntegrable.sum Finset.univ fun k _ =>
        ((h_scalar (u k) (v k) (hu k) (huv_or k)).1).const_mul (w k)
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hIntL hIntR h_le_Ioo
    rw [intervalIntegral.integral_finsetSum (fun y _ => (h_scalar (a y) (b y) (ha y) (hab_or y)).1),
      intervalIntegral.integral_finsetSum (fun k _ =>
        ((h_scalar (u k) (v k) (hu k) (huv_or k)).1).const_mul (w k))] at hmono
    have hL_eval : (∑ y : o, ∫ s in (0 : ℝ)..1, g (a y) (b y) s) =
        ∑ y : o, a y * Real.log (a y / b y) :=
      Finset.sum_congr rfl fun y _ => (h_scalar (a y) (b y) (ha y) (hab_or y)).2.1
    have hR_eval : (∑ k : n × n, ∫ s in (0 : ℝ)..1, w k * g (u k) (v k) s) =
        ∑ k : n × n, w k * (u k * Real.log (u k / v k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul, (h_scalar (u k) (v k) (hu k) (huv_or k)).2.1]
    linarith [hmono, hL_eval, hR_eval]
  
  have h_eps_limit : ∀ (P_arr : ι → o → ℝ) (c : o → ℝ) (B_bound : ℝ),
      (∀ x y, 0 ≤ P_arr x y) → (∀ x y, p x = 0 → P_arr x y = 0) →
      (∀ ε : ℝ, 0 < ε →
        (∑ x : ι, ∑ y : o, P_arr x y * Real.log (P_arr x y / (p x * ((∑ x', P_arr x' y) + ε * c y)))) ≤ B_bound) →
      (∑ x : ι, ∑ y : o, P_arr x y * Real.log (P_arr x y / (p x * (∑ x', P_arr x' y)))) ≤ B_bound := by
    intro P_arr c B_bound hP hpP hbound
    let q_arr : o → ℝ := fun y => ∑ x', P_arr x' y
    let ε_seq : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    have hε_pos : ∀ k : ℕ, 0 < ε_seq k := fun k => one_div_pos.mpr (by positivity)
    have hε_tendsto : Filter.Tendsto ε_seq Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have htend : Filter.Tendsto
        (fun k : ℕ => ∑ x : ι, ∑ y : o,
          P_arr x y * Real.log (P_arr x y / (p x * (q_arr y + ε_seq k * c y))))
        Filter.atTop
        (nhds (∑ x : ι, ∑ y : o, P_arr x y * Real.log (P_arr x y / (p x * q_arr y)))) := by
      refine tendsto_finsetSum Finset.univ fun x _ => tendsto_finsetSum Finset.univ fun y _ => ?_
      by_cases hP0 : P_arr x y = 0
      · simp only [hP0, zero_div, Real.log_zero, mul_zero]
        exact tendsto_const_nhds
      · have hP_pos : 0 < P_arr x y := lt_of_le_of_ne (hP x y) (Ne.symm hP0)
        have hpx_ne : p x ≠ 0 := fun h0 => hP0 (hpP x y h0)
        have hq_pos : 0 < q_arr y := lt_of_lt_of_le hP_pos
          (Finset.single_le_sum (fun x' _ => hP x' y) (Finset.mem_univ x))
        have hden_ne : p x * q_arr y ≠ 0 := mul_ne_zero hpx_ne (ne_of_gt hq_pos)
        have hquot_ne : P_arr x y / (p x * q_arr y) ≠ 0 := div_ne_zero hP0 hden_ne
        have ht1 : Filter.Tendsto (fun k => q_arr y + ε_seq k * c y) Filter.atTop (nhds (q_arr y)) := by
          simpa using tendsto_const_nhds.add (hε_tendsto.mul_const (c y))
        have ht2 : Filter.Tendsto (fun k => p x * (q_arr y + ε_seq k * c y)) Filter.atTop
            (nhds (p x * q_arr y)) :=
          tendsto_const_nhds.mul ht1
        have ht3 : Filter.Tendsto (fun k => P_arr x y / (p x * (q_arr y + ε_seq k * c y))) Filter.atTop
            (nhds (P_arr x y / (p x * q_arr y))) :=
          tendsto_const_nhds.div ht2 hden_ne
        exact (ht3.log hquot_ne).const_mul (P_arr x y)
    exact le_of_tendsto' htend (fun k => hbound (ε_seq k) (hε_pos k))
  
  intro P q
  let a : ι → o → ℝ := fun x y => (Λ y * ρ x).trace.re
  let c : o → ℝ := fun y => (Λ y).trace.re
  let ρ_bar : Matrix n n ℂ := ∑ x : ι, (p x : ℂ) • ρ x
  have ha_nn : ∀ x y, 0 ≤ a x y := fun x y => h_psd_tr (Λ y) (ρ x) (hΛ y) (hρ x)
  have hP_nn : ∀ x y, 0 ≤ P x y := fun x y => mul_nonneg (hp x) (ha_nn x y)
  have hpP : ∀ x y, p x = 0 → P x y = 0 := fun x y h0 => by simp [P, h0]
  have hc_nn : ∀ y, 0 ≤ c y := fun y => by
    simpa [c] using h_psd_tr (Λ y) 1 (hΛ y) Matrix.PosSemidef.one
  have hρ_bar_psd : ρ_bar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun x _ =>
      (hρ x).smul (h_ofReal_nn (hp x))
  refine h_eps_limit P c (vnEntropy ρ_bar - ∑ x : ι, p x * vnEntropy (ρ x)) hP_nn hpP ?_
  intro ε hε
  let hH_bar := hρ_bar_psd.isHermitian
  let V : unitary (Matrix n n ℂ) := hH_bar.eigenvectorUnitary
  let Vm : Matrix n n ℂ := (V : Matrix n n ℂ)
  let μ : n → ℝ := hH_bar.eigenvalues
  have hμ_nn : ∀ j, 0 ≤ μ j := hρ_bar_psd.eigenvalues_nonneg
  let ν : n → ℝ := fun j => μ j + ε
  have hν_pos : ∀ j, 0 < ν j := fun j => add_pos_of_nonneg_of_pos (hμ_nn j) hε
  let B_ε : Matrix n n ℂ := Vm * Matrix.diagonal (fun j => (ν j : ℂ)) * star Vm
  let L_ε : Matrix n n ℂ := Vm * Matrix.diagonal (fun j => (Real.log (ν j) : ℂ)) * star Vm
  have hVV_mul_star : Vm * star Vm = 1 := Unitary.coe_mul_star_self V
  have hB_ε_eq : B_ε = ρ_bar + (ε : ℂ) • (1 : Matrix n n ℂ) := by
    have hbar_spec : ρ_bar = Vm * Matrix.diagonal (fun j => (μ j : ℂ)) * star Vm := by
      have hs := hH_bar.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at hs
      exact hs
    have hdiag_split : Matrix.diagonal (fun j : n => (ν j : ℂ)) =
        Matrix.diagonal (fun j : n => (μ j : ℂ)) + (ε : ℂ) • (1 : Matrix n n ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [ν]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    calc B_ε = Vm * (Matrix.diagonal (fun j => (μ j : ℂ)) + (ε : ℂ) • (1 : Matrix n n ℂ)) * star Vm := by
          rw [← hdiag_split]
      _ = Vm * Matrix.diagonal (fun j => (μ j : ℂ)) * star Vm + (ε : ℂ) • (Vm * star Vm) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = ρ_bar + (ε : ℂ) • (1 : Matrix n n ℂ) := by rw [← hbar_spec, hVV_mul_star]
  let b_ε : o → ℝ := fun y => q y + ε * c y
  have hb_ε_tr : ∀ y : o, (Λ y * B_ε).trace.re = b_ε y := by
    intro y
    rw [hB_ε_eq, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul]
    simp only [ρ_bar, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul, Complex.add_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, b_ε, q, P, c]
  have hq_nn : ∀ y : o, 0 ≤ q y := fun y => Finset.sum_nonneg fun x _ => hP_nn x y
  have hb_ε_nn : ∀ y : o, 0 ≤ b_ε y := fun y =>
    add_nonneg (hq_nn y) (mul_nonneg (le_of_lt hε) (hc_nn y))
  have h_per_x : ∀ x : ι,
      (∑ y : o, P x y * Real.log (P x y / (p x * b_ε y))) ≤
        p x * (- vnEntropy (ρ x) - (L_ε * ρ x).trace.re) := by
    intro x
    by_cases hpx : p x = 0
    · simp [P, hpx]
    · have hpx_pos : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hpx)
      have hLHS_factor : (∑ y : o, P x y * Real.log (P x y / (p x * b_ε y))) =
          p x * ∑ y : o, a x y * Real.log (a x y / b_ε y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        have hdiv : P x y / (p x * b_ε y) = a x y / b_ε y :=
          mul_div_mul_left (a x y) (b_ε y) hpx
        rw [hdiv]
        simp only [P, a, mul_assoc]
      rw [hLHS_factor]
      refine mul_le_mul_of_nonneg_left ?_ (hp x)
      let hHx := (hρ x).isHermitian
      let U_x : Matrix n n ℂ := (hHx.eigenvectorUnitary : Matrix n n ℂ)
      let lam_x : n → ℝ := hHx.eigenvalues
      let w : n × n → ℝ := fun k => ‖(star U_x * Vm) k.1 k.2‖ ^ 2
      let u : n × n → ℝ := fun k => lam_x k.1
      let v : n × n → ℝ := fun k => ν k.2
      have hab_x : ∀ y : o, b_ε y = 0 → a x y = 0 := by
        intro y hb0
        have h1 : P x y ≤ q y := Finset.single_le_sum (fun x' _ => hP_nn x' y) (Finset.mem_univ x)
        have h2 : 0 ≤ ε * c y := mul_nonneg (le_of_lt hε) (hc_nn y)
        have h3 : p x * a x y = 0 := by
          linarith [hP_nn x y, h1, h2, show q y + ε * c y = 0 from hb0]
        exact (mul_eq_zero.mp h3).resolve_left hpx
      have hmass_x : (∑ y : o, a x y) = ∑ k : n × n, w k * u k := by
        have hsum_a : (∑ y : o, a x y) = (ρ x).trace.re := by
          have h1 : (∑ y : o, a x y) = ((∑ y : o, Λ y) * ρ x).trace.re := by
            simp only [a, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
          rw [h1, hΛ1, Matrix.one_mul]
        have h1_conj : (Vm * Matrix.diagonal (fun _ : n => ((1 : ℝ) : ℂ)) * star Vm) = 1 := by
          have hd1 : Matrix.diagonal (fun _ : n => ((1 : ℝ) : ℂ)) = 1 := by
            ext i j
            by_cases hij : i = j
            · subst hij; simp
            · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
          rw [hd1, Matrix.mul_one]
          exact hVV_mul_star
        have htr_prod := (h_trace_conj (ρ x) hHx V (fun _ => 1)).2
        change ((Vm * Matrix.diagonal (fun _ : n => ((1 : ℝ) : ℂ)) * star Vm) * ρ x).trace.re =
          ∑ i : n, ∑ j : n, ‖(star U_x * Vm) i j‖ ^ 2 * lam_x i * 1 at htr_prod
        rw [h1_conj, Matrix.one_mul] at htr_prod
        rw [hsum_a, htr_prod, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [w, u]
      have hquad_x : ∀ s : ℝ, 0 < s → s < 1 →
          (∑ y : o, (a x y) ^ 2 / ((1 - s) * a x y + s * b_ε y)) ≤
            ∑ k : n × n, w k * ((u k) ^ 2 / ((1 - s) * u k + s * v k)) := by
        intro s hs0 hs1
        have hc_s := h_crux (ρ x) (hρ x) V ν hν_pos s hs0 hs1
        change (∑ y : o, (a x y) ^ 2 / ((1 - s) * a x y + s * (Λ y * B_ε).trace.re)) ≤
          ∑ i : n, ∑ j : n, w (i, j) * ((u (i, j)) ^ 2 / ((1 - s) * u (i, j) + s * v (i, j))) at hc_s
        simp_rw [hb_ε_tr] at hc_s
        rw [Fintype.sum_prod_type]
        exact hc_s
      have hlog_le := h_int_bound (fun y => a x y) b_ε (ha_nn x) hb_ε_nn hab_x
        w u v (fun _ => sq_nonneg _) (fun k => (hρ x).eigenvalues_nonneg k.1)
        (fun k => hν_pos k.2) hmass_x hquad_x
      have hRHS_simp : (∑ k : n × n, w k * (u k * Real.log (u k / v k))) =
          - vnEntropy (ρ x) - (L_ε * ρ x).trace.re := by
        rw [Fintype.sum_prod_type]
        have h_split : ∀ (i j : n),
            w (i, j) * (u (i, j) * Real.log (u (i, j) / v (i, j))) =
              ‖(star U_x * Vm) i j‖ ^ 2 * (lam_x i * Real.log (lam_x i)) -
                ‖(star U_x * Vm) i j‖ ^ 2 * lam_x i * Real.log (ν j) := by
          intro i j
          simp only [w, u, v]
          by_cases hli : lam_x i = 0
          · simp [hli]
          · rw [Real.log_div hli (ne_of_gt (hν_pos j))]
            ring
        simp_rw [h_split, Finset.sum_sub_distrib]
        have h_part1 : (∑ i : n, ∑ j : n, ‖(star U_x * Vm) i j‖ ^ 2 * (lam_x i * Real.log (lam_x i))) =
            - vnEntropy (ρ x) := by
          have hrow := (h_trace_conj (ρ x) hHx V (fun _ => 0)).1
          have hfactor : ∀ i : n,
              (∑ j : n, ‖(star U_x * Vm) i j‖ ^ 2 * (lam_x i * Real.log (lam_x i))) =
                lam_x i * Real.log (lam_x i) := by
            intro i
            rw [← Finset.sum_mul]
            have hri : (∑ j : n, ‖(star U_x * Vm) i j‖ ^ 2) = 1 := hrow i
            rw [hri, one_mul]
          simp_rw [hfactor]
          rw [h_vn (ρ x) hHx, neg_neg]
        have h_part2 : (∑ i : n, ∑ j : n, ‖(star U_x * Vm) i j‖ ^ 2 * lam_x i * Real.log (ν j)) =
            (L_ε * ρ x).trace.re :=
          ((h_trace_conj (ρ x) hHx V (fun j => Real.log (ν j))).2).symm
        rw [h_part1, h_part2]
      linarith [hlog_le, hRHS_simp]
  have hsum_x : (∑ x : ι, ∑ y : o, P x y * Real.log (P x y / (p x * b_ε y))) ≤
      - (∑ x : ι, p x * vnEntropy (ρ x)) - (L_ε * ρ_bar).trace.re := by
    have h1 : (∑ x : ι, ∑ y : o, P x y * Real.log (P x y / (p x * b_ε y))) ≤
        ∑ x : ι, p x * (- vnEntropy (ρ x) - (L_ε * ρ x).trace.re) :=
      Finset.sum_le_sum fun x _ => h_per_x x
    have h2 : (∑ x : ι, p x * (- vnEntropy (ρ x) - (L_ε * ρ x).trace.re)) =
        - (∑ x : ι, p x * vnEntropy (ρ x)) - (L_ε * ρ_bar).trace.re := by
      have hlin : (L_ε * ρ_bar).trace.re = ∑ x : ι, p x * (L_ε * ρ x).trace.re := by
        simp only [ρ_bar, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
          smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
      rw [hlin, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring
    linarith
  have hL_bar_tr : (L_ε * ρ_bar).trace.re = ∑ j : n, μ j * Real.log (μ j + ε) := by
    have htr := (h_trace_conj ρ_bar hH_bar V (fun j => Real.log (ν j))).2
    have hVV : star Vm * Vm = 1 := Unitary.coe_star_mul_self V
    change (L_ε * ρ_bar).trace.re =
      ∑ i : n, ∑ j : n, ‖(star Vm * Vm) i j‖ ^ 2 * μ i * Real.log (ν j) at htr
    rw [hVV] at htr
    rw [htr]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [ν]
    · intro j _ hji
      simp [Matrix.one_apply_ne (Ne.symm hji)]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hbar_mono : - (L_ε * ρ_bar).trace.re ≤ vnEntropy ρ_bar := by
    rw [hL_bar_tr, h_vn ρ_bar hH_bar, neg_le_neg_iff]
    refine Finset.sum_le_sum fun j _ => ?_
    change μ j * Real.log (μ j) ≤ μ j * Real.log (μ j + ε)
    rcases eq_or_lt_of_le (hμ_nn j) with h0 | hpos
    · rw [← h0]; simp
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_log hpos (by linarith)) (hμ_nn j)
  linarith [hsum_x, hbar_mono]

end Leap
