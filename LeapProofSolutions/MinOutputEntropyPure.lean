import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Def 20.4.1 / Ex 20.4.2: minimum output entropy is attained on pure inputs. -/
theorem minOutputEntropy_pure {ι : Type*} [Fintype ι] (K : ι → Matrix n m ℂ)
    (hTP : ∑ i, (K i)ᴴ * K i = 1) (ρ : Matrix m m ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ v : m → ℂ, star v ⬝ᵥ v = 1 ∧
      vnEntropy (kraus K (Matrix.vecMulVec v (star v))) ≤ vnEntropy (kraus K ρ) := by
  let _ := hTP
  
  have h_vnEntropy_eq : ∀ (A : Matrix n n ℂ) (hA : A.IsHermitian),
      vnEntropy A = ∑ k : n, Real.negMulLog (hA.eigenvalues k) := by
    intro A hA
    unfold vnEntropy
    have h1 := hA.spectral_theorem
    have h2 : cfc Real.log A =
        (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary)
          (Matrix.diagonal (RCLike.ofReal ∘ Real.log ∘ hA.eigenvalues)) := by
      rw [hA.cfc_eq Real.log, Matrix.IsHermitian.cfc]
    have hprod : A * cfc Real.log A =
        (hA.eigenvectorUnitary : Matrix n n ℂ) *
          Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ) * (Real.log (hA.eigenvalues k) : ℂ)) *
          star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
      have hmul := congr_arg₂ (· * ·) h1 h2
      rw [← map_mul, Unitary.conjStarAlgAut_apply, Matrix.diagonal_mul_diagonal] at hmul
      simpa [Function.comp_def] using hmul
    have htr_prod : (A * cfc Real.log A).trace =
        ∑ k : n, (hA.eigenvalues k : ℂ) * (Real.log (hA.eigenvalues k) : ℂ) := by
      rw [hprod, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
    rw [htr_prod, Complex.re_sum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      ← Finset.sum_neg_distrib, Real.negMulLog_def, neg_mul]

  
  have hz_nonneg : ∀ z : ℂ, 0 ≤ (star z * z).re := fun z => by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
    exact add_nonneg (mul_self_nonneg z.re) (mul_self_nonneg z.im)
  have h_dephase : ∀ (A : Matrix n n ℂ) (hA : A.PosSemidef) (W : Matrix.unitaryGroup n ℂ),
      ∑ j : n, Real.negMulLog (hA.isHermitian.eigenvalues j) ≤
        ∑ k : n, Real.negMulLog (((star (W : Matrix n n ℂ) * A * (W : Matrix n n ℂ)) k k).re) := by
    intro A hA W
    let hH := hA.isHermitian
    let ν : n → ℝ := hH.eigenvalues
    let U : Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary
    let V : Matrix.unitaryGroup n ℂ := star U * W
    let D : n → n → ℝ := fun k j => (star ((V : Matrix n n ℂ) j k) * (V : Matrix n n ℂ) j k).re
    have hD_nonneg : ∀ k j : n, 0 ≤ D k j := fun k j => hz_nonneg ((V : Matrix n n ℂ) j k)
    have hD_col : ∀ k : n, ∑ j : n, D k j = 1 := by
      intro k
      have hunit : star (V : Matrix n n ℂ) * (V : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self V
      have hkk := congr_arg Complex.re (congr_fun (congr_fun hunit k) k)
      simpa [D, Matrix.mul_apply, Complex.re_sum] using hkk
    have hD_row : ∀ j : n, ∑ k : n, D k j = 1 := by
      intro j
      have hunit : (V : Matrix n n ℂ) * star (V : Matrix n n ℂ) = 1 := by simp
      have hjj := congr_arg Complex.re (congr_fun (congr_fun hunit j) j)
      simpa [D, Matrix.mul_apply, Complex.re_sum, mul_comm] using hjj
    have hWAW : star (W : Matrix n n ℂ) * A * (W : Matrix n n ℂ) =
        star (V : Matrix n n ℂ) * Matrix.diagonal (fun j => (ν j : ℂ)) * (V : Matrix n n ℂ) := by
      have hspec : A = (U : Matrix n n ℂ) * Matrix.diagonal (fun j => (ν j : ℂ)) * star (U : Matrix n n ℂ) := by
        have hs := hH.spectral_theorem
        rw [Unitary.conjStarAlgAut_apply] at hs
        simpa [U, ν, Function.comp_def] using hs
      have hconj := congr_arg (fun X => star (W : Matrix n n ℂ) * X * (W : Matrix n n ℂ)) hspec
      have hV_coe : (V : Matrix n n ℂ) = star (U : Matrix n n ℂ) * (W : Matrix n n ℂ) := by
        simp [V]
      have hV_star : star (V : Matrix n n ℂ) = star (W : Matrix n n ℂ) * (U : Matrix n n ℂ) := by
        rw [hV_coe, star_mul, star_star]
      rw [hconj, hV_star, hV_coe]
      simp only [Matrix.mul_assoc]
    have hdiag_eq : ∀ k : n,
        ((star (W : Matrix n n ℂ) * A * (W : Matrix n n ℂ)) k k).re = ∑ j : n, D k j * ν j := by
      intro k
      rw [hWAW, Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_right_comm (star ((V : Matrix n n ℂ) j k)) (ν j : ℂ) ((V : Matrix n n ℂ) j k),
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have h_jensen : ∀ k : n,
        ∑ j : n, D k j * Real.negMulLog (ν j) ≤
          Real.negMulLog (((star (W : Matrix n n ℂ) * A * (W : Matrix n n ℂ)) k k).re) := by
      intro k
      have hj := Real.concaveOn_negMulLog.le_map_sum
        (t := Finset.univ) (w := fun j => D k j) (p := ν)
        (fun j _ => hD_nonneg k j) (hD_col k) (fun j _ => hA.eigenvalues_nonneg j)
      simp only [smul_eq_mul] at hj
      rwa [← hdiag_eq k] at hj
    calc ∑ j : n, Real.negMulLog (ν j)
        = ∑ j : n, (∑ k : n, D k j) * Real.negMulLog (ν j) := by simp_rw [hD_row, one_mul]
      _ = ∑ j : n, ∑ k : n, D k j * Real.negMulLog (ν j) := by simp_rw [Finset.sum_mul]
      _ = ∑ k : n, ∑ j : n, D k j * Real.negMulLog (ν j) := Finset.sum_comm
      _ ≤ ∑ k : n, Real.negMulLog (((star (W : Matrix n n ℂ) * A * (W : Matrix n n ℂ)) k k).re) :=
          Finset.sum_le_sum fun k _ => h_jensen k

  
  let hρH := hρ.isHermitian
  let p : m → ℝ := hρH.eigenvalues
  let Uρ : Matrix m m ℂ := (hρH.eigenvectorUnitary : Matrix m m ℂ)
  let v : m → m → ℂ := fun a r => Uρ r a
  have hp_nonneg : ∀ a : m, 0 ≤ p a := fun a => hρ.eigenvalues_nonneg a
  have hp_sum : ∑ a : m, p a = 1 := by
    have htr_eig := hρH.trace_eq_sum_eigenvalues
    rw [htr] at htr_eig
    have hre := congr_arg Complex.re htr_eig.symm
    simpa [p, Complex.re_sum] using hre
  have hv_norm : ∀ a : m, star (v a) ⬝ᵥ v a = 1 := by
    intro a
    have hunit : star Uρ * Uρ = 1 := Unitary.coe_star_mul_self hρH.eigenvectorUnitary
    have haa := congr_fun (congr_fun hunit a) a
    simpa [v, dotProduct, Matrix.mul_apply] using haa
  let P : m → Matrix m m ℂ := fun a => Matrix.vecMulVec (v a) (star (v a))
  have hρ_eq : ρ = ∑ a : m, p a • P a := by
    have hspec : ρ = Uρ * Matrix.diagonal (fun a => (p a : ℂ)) * star Uρ := by
      have hs := hρH.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at hs
      simpa [Uρ, p, Function.comp_def] using hs
    ext r c
    have hrc := congr_fun (congr_fun hspec r) c
    rw [hrc, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply,
      Matrix.sum_apply, Matrix.smul_apply, P, Matrix.vecMulVec_apply, v, Pi.star_apply,
      Complex.real_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm (Uρ r a) (p a : ℂ), mul_assoc]

  
  let σ : m → Matrix n n ℂ := fun a => kraus K (P a)
  let B : Matrix n n ℂ := kraus K ρ
  have hσ_psd : ∀ a : m, (σ a).PosSemidef := fun a =>
    Matrix.posSemidef_sum Finset.univ fun i _ =>
      (Matrix.posSemidef_vecMulVec_self_star (v a)).mul_mul_conjTranspose_same (K i)
  have hB_psd : B.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ => hρ.mul_mul_conjTranspose_same (K i)
  have hB_eq : B = ∑ a : m, p a • σ a := by
    change kraus K ρ = ∑ a : m, p a • kraus K (P a)
    unfold kraus
    rw [hρ_eq]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum]

  let hBH := hB_psd.isHermitian
  let W : Matrix.unitaryGroup n ℂ := hBH.eigenvectorUnitary
  let μ : n → ℝ := hBH.eigenvalues
  let q : m → n → ℝ := fun a k =>
    ((star (W : Matrix n n ℂ) * σ a * (W : Matrix n n ℂ)) k k).re
  have hq_nonneg : ∀ (a : m) (k : n), 0 ≤ q a k := by
    intro a k
    have hpsd : (star (W : Matrix n n ℂ) * σ a * (W : Matrix n n ℂ)).PosSemidef := by
      rw [Matrix.star_eq_conjTranspose]
      exact (hσ_psd a).conjTranspose_mul_mul_same (W : Matrix n n ℂ)
    exact (Complex.nonneg_iff.mp hpsd.diag_nonneg).1
  have hμ_eq : ∀ k : n, μ k = ∑ a : m, p a * q a k := by
    intro k
    have hdiagB : star (W : Matrix n n ℂ) * B * (W : Matrix n n ℂ) =
        Matrix.diagonal (fun j => (μ j : ℂ)) := by
      have hd := hBH.conjStarAlgAut_star_eigenvectorUnitary
      rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at hd
      simpa [W, μ, Function.comp_def] using hd
    have hkk := congr_arg Complex.re (congr_fun (congr_fun hdiagB k) k)
    have hsum_k : ((star (W : Matrix n n ℂ) * B * (W : Matrix n n ℂ)) k k).re =
        ∑ a : m, p a * q a k := by
      have hb := congr_arg
        (fun X => ((star (W : Matrix n n ℂ) * X * (W : Matrix n n ℂ)) k k).re) hB_eq
      rw [hb]
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.sum_apply, Matrix.smul_apply, Complex.re_sum, Complex.smul_re, smul_eq_mul, q]
    have hrhs : ((Matrix.diagonal (fun j => (μ j : ℂ))) k k).re = μ k := by
      simp
    exact hrhs.symm.trans (hkk.symm.trans hsum_k)
  have h_upper : ∑ a : m, p a * (∑ k : n, Real.negMulLog (q a k)) ≤ vnEntropy B := by
    have h_jensen_B : ∀ k : n,
        ∑ a : m, p a * Real.negMulLog (q a k) ≤ Real.negMulLog (μ k) := by
      intro k
      have hj := Real.concaveOn_negMulLog.le_map_sum
        (t := Finset.univ) (w := p) (p := fun a => q a k)
        (fun a _ => hp_nonneg a) hp_sum (fun a _ => hq_nonneg a k)
      simp only [smul_eq_mul] at hj
      rwa [← hμ_eq k] at hj
    calc ∑ a : m, p a * (∑ k : n, Real.negMulLog (q a k))
        = ∑ a : m, ∑ k : n, p a * Real.negMulLog (q a k) := by simp_rw [Finset.mul_sum]
      _ = ∑ k : n, ∑ a : m, p a * Real.negMulLog (q a k) := Finset.sum_comm
      _ ≤ ∑ k : n, Real.negMulLog (μ k) := Finset.sum_le_sum fun k _ => h_jensen_B k
      _ = vnEntropy B := (h_vnEntropy_eq B hBH).symm

  
  have h_conc : ∑ a : m, p a * vnEntropy (σ a) ≤ vnEntropy B := by
    refine le_trans (Finset.sum_le_sum fun a _ => ?_) h_upper
    apply mul_le_mul_of_nonneg_left _ (hp_nonneg a)
    rw [h_vnEntropy_eq (σ a) (hσ_psd a).isHermitian]
    exact h_dephase (σ a) (hσ_psd a) W
  have hm_ne : (Finset.univ : Finset m).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have h0 : ∑ a : m, p a = 0 := by simp [hemp]
    linarith
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_min_image Finset.univ (fun a => vnEntropy (σ a)) hm_ne
  refine ⟨v a₀, hv_norm a₀, ?_⟩
  calc vnEntropy (σ a₀)
      = (∑ a : m, p a) * vnEntropy (σ a₀) := by rw [hp_sum, one_mul]
    _ = ∑ a : m, p a * vnEntropy (σ a₀) := Finset.sum_mul _ _ _
    _ ≤ ∑ a : m, p a * vnEntropy (σ a) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ha₀ a (Finset.mem_univ a)) (hp_nonneg a)
    _ ≤ vnEntropy B := h_conc

end Leap
