import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Thm 11.9.2: monotonicity of relative entropy under partial trace
(Lindblad–Uhlmann; needs Lieb concavity). -/
theorem relEnt_ptrace_le (ρ σ : Matrix (m × n) (m × n) ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEnt (ptraceRight ρ) (ptraceRight σ) ≤ relEnt ρ σ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hpt_zero : ∀ M : Matrix (m × n) (m × n) ℂ, ptraceRight M = 0 := by
      intro M; ext i j
      simp [Leap.ptraceRight.eq_def]
    have : IsEmpty (m × n) := isEmpty_prod.mpr (Or.inr hn)
    rw [hpt_zero ρ, hpt_zero σ, Leap.relEnt.eq_def, Leap.relEnt.eq_def]
    simp [Matrix.trace]
  · have htr_eq : (ptraceRight ρ).trace.re = ρ.trace.re := by
      congr 1
      simp only [Matrix.trace, Matrix.diag, Leap.ptraceRight.eq_def, Fintype.sum_prod_type]
    have h_ptrace_posDef : ∀ (M : Matrix (m × n) (m × n) ℂ), M.PosDef → (ptraceRight M).PosDef := by
      intro M hM
      rw [Matrix.posDef_iff_dotProduct_mulVec] at hM ⊢
      obtain ⟨hM_herm, hM_pos⟩ := hM
      refine ⟨?_, ?_⟩
      · ext i j
        simp only [Matrix.conjTranspose_apply, Leap.ptraceRight.eq_def, star_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact congr_fun (congr_fun hM_herm (i, k)) (j, k)
      · intro x hx
        obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
        let y : n → (m × n → ℂ) := fun k ik => if ik.2 = k then x ik.1 else 0
        have hy_ne : ∀ k : n, y k ≠ 0 := by
          intro k hk
          apply hi₀
          have h0 := congr_fun hk (i₀, k)
          simpa [y] using h0
        have hq_pos : ∀ k : n, 0 < star (y k) ⬝ᵥ M.mulVec (y k) := fun k => hM_pos (hy_ne k)
        have hsum_eq : (∑ k : n, star (y k) ⬝ᵥ M.mulVec (y k)) = star x ⬝ᵥ (ptraceRight M).mulVec x := by
          have h_each : ∀ k : n, star (y k) ⬝ᵥ M.mulVec (y k) =
              ∑ i : m, star (x i) * ∑ j : m, M (i, k) (j, k) * x j := by
            intro k
            simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, y, Pi.star_apply]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_eq_single k]
            · simp only [↓reduceIte]
              congr 1
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_eq_single k]
              · simp
              · intro l' _ hl'; simp [hl']
              · intro hk_abs; exact False.elim (hk_abs (Finset.mem_univ k))
            · intro l _ hl; simp [hl]
            · intro hk_abs; exact False.elim (hk_abs (Finset.mem_univ k))
          simp_rw [h_each]
          rw [Finset.sum_comm]
          simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Leap.ptraceRight.eq_def]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
        rw [← hsum_eq, Complex.lt_def]
        simp only [Complex.zero_re, Complex.zero_im, Complex.re_sum, Complex.im_sum]
        refine ⟨?_, ?_⟩
        · exact Finset.sum_pos (fun k _ => (Complex.lt_def.mp (hq_pos k)).1) Finset.univ_nonempty
        · symm
          exact Finset.sum_eq_zero fun k _ => ((Complex.lt_def.mp (hq_pos k)).2).symm
    let ρA : Matrix m m ℂ := ptraceRight ρ
    let σA : Matrix m m ℂ := ptraceRight σ
    have hρA : ρA.PosDef := h_ptrace_posDef ρ hρ
    have hσA : σA.PosDef := h_ptrace_posDef σ hσ
    have hsylv_spec_A :
        ∃ (W : Matrix m m ℂ) (lam mu : m → ℝ),
          (∀ i, 0 < lam i) ∧ (∀ i, 0 < mu i) ∧
          relEnt ρA σA = ∑ p : m × m,
            Complex.normSq (W p.1 p.2) * lam p.2 * (Real.log (lam p.2) - Real.log (mu p.1)) ∧
          (∀ u : ℝ, 0 < u → u < 1 →
            ∃ X : Matrix m m ℂ,
              (1 - u) • (X * ρA) + u • (σA * X) = ρA ∧
              (Xᴴ * ρA).trace.re - ρA.trace.re =
                u * ∑ p : m × m,
                  Complex.normSq (W p.1 p.2) *
                    (lam p.2 * (lam p.2 - mu p.1) / ((1 - u) * lam p.2 + u * mu p.1))) := by
      let hAH := hρA.isHermitian
      let hBH := hσA.isHermitian
      let U : Matrix m m ℂ := (hAH.eigenvectorUnitary : Matrix m m ℂ)
      let V : Matrix m m ℂ := (hBH.eigenvectorUnitary : Matrix m m ℂ)
      let lam : m → ℝ := hAH.eigenvalues
      let mu : m → ℝ := hBH.eigenvalues
      let W : Matrix m m ℂ := Vᴴ * U
      have hlam : ∀ i, 0 < lam i := hρA.eigenvalues_pos
      have hmu : ∀ i, 0 < mu i := hσA.eigenvalues_pos
      have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hAH.eigenvectorUnitary.prop
      have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hBH.eigenvectorUnitary.prop
      have hV2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hBH.eigenvectorUnitary.prop
      have hWW : Wᴴ * W = 1 := by
        calc Wᴴ * W = (Uᴴ * V) * (Vᴴ * U) := by simp [W, Matrix.conjTranspose_mul]
          _ = Uᴴ * (V * Vᴴ) * U := by simp only [Matrix.mul_assoc]
          _ = Uᴴ * U := by rw [hV2, Matrix.mul_one]
          _ = 1 := hU1
      have hW_sum : ∀ b : m, ∑ a : m, Complex.normSq (W a b) = 1 := by
        intro b
        have hbb := congr_arg Complex.re (congr_fun (congr_fun hWW b) b)
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
          Complex.one_re, Complex.re_sum] at hbb
        rw [← hbb]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      let Dlam : Matrix m m ℂ := Matrix.diagonal (fun b => (lam b : ℂ))
      let Dmu : Matrix m m ℂ := Matrix.diagonal (fun a => (mu a : ℂ))
      let Dloglam : Matrix m m ℂ := Matrix.diagonal (fun b => (Real.log (lam b) : ℂ))
      let Dlogmu : Matrix m m ℂ := Matrix.diagonal (fun a => (Real.log (mu a) : ℂ))
      have hA_eq : ρA = U * Dlam * Uᴴ := by
        simpa [U, lam, Dlam, Unitary.conjStarAlgAut_apply, Function.comp_def,
          Matrix.star_eq_conjTranspose] using hAH.spectral_theorem
      have hB_eq : σA = V * Dmu * Vᴴ := by
        simpa [V, mu, Dmu, Unitary.conjStarAlgAut_apply, Function.comp_def,
          Matrix.star_eq_conjTranspose] using hBH.spectral_theorem
      have hlogA : cfc Real.log ρA = U * Dloglam * Uᴴ := by
        rw [hAH.cfc_eq, Matrix.IsHermitian.cfc.eq_def]
        simp [U, lam, Dloglam, Unitary.conjStarAlgAut_apply, Function.comp_def,
          Matrix.star_eq_conjTranspose]
      have hlogB : cfc Real.log σA = V * Dlogmu * Vᴴ := by
        rw [hBH.cfc_eq, Matrix.IsHermitian.cfc.eq_def]
        simp [V, mu, Dlogmu, Unitary.conjStarAlgAut_apply, Function.comp_def,
          Matrix.star_eq_conjTranspose]
      have htr_U : ∀ M : Matrix m m ℂ, (U * M * Uᴴ).trace = M.trace := by
        intro M
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
      have hWD : ∀ i j, (W * Dlam) i j = W i j * (lam j : ℂ) := by
        intro i j; simp [Dlam, Matrix.mul_diagonal]
      refine ⟨W, lam, mu, hlam, hmu, ?_, ?_⟩
      · rw [Leap.relEnt.eq_def, mul_sub, Matrix.trace_sub, Complex.sub_re]
        have h1 : (ρA * cfc Real.log ρA).trace.re =
            ∑ a : m, ∑ b : m, Complex.normSq (W a b) * lam b * Real.log (lam b) := by
          have hmul : ρA * cfc Real.log ρA = U * (Dlam * Dloglam) * Uᴴ := by
            calc ρA * cfc Real.log ρA
                = (U * Dlam * Uᴴ) * (U * Dloglam * Uᴴ) := by rw [hlogA, hA_eq]
              _ = U * (Dlam * (Uᴴ * U) * Dloglam) * Uᴴ := by simp only [Matrix.mul_assoc]
              _ = U * (Dlam * Dloglam) * Uᴴ := by rw [hU1, Matrix.mul_one]
          rw [hmul, htr_U]
          simp only [Dlam, Dloglam, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
            Complex.re_sum]
          have hre : (∑ b : m, ((lam b : ℂ) * (Real.log (lam b) : ℂ)).re) =
              ∑ b : m, (∑ a : m, Complex.normSq (W a b)) * (lam b * Real.log (lam b)) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← Complex.ofReal_mul, Complex.ofReal_re, hW_sum b, one_mul]
          rw [hre]
          simp_rw [Finset.sum_mul, mul_assoc]
          rw [Finset.sum_comm]
        have h2 : (ρA * cfc Real.log σA).trace.re =
            ∑ a : m, ∑ b : m, Complex.normSq (W a b) * lam b * Real.log (mu a) := by
          have htr2 : (ρA * cfc Real.log σA).trace = (Dlogmu * ((W * Dlam) * Wᴴ)).trace := by
            calc (ρA * cfc Real.log σA).trace
                = ((U * Dlam * Uᴴ * V) * (Dlogmu * Vᴴ)).trace := by
                    rw [hlogB, hA_eq]; simp only [Matrix.mul_assoc]
              _ = ((Dlogmu * Vᴴ) * (U * Dlam * Uᴴ * V)).trace := Matrix.trace_mul_comm _ _
              _ = (Dlogmu * ((W * Dlam) * Wᴴ)).trace := by
                    simp [W, Matrix.conjTranspose_mul, Matrix.mul_assoc]
          rw [htr2]
          simp only [Matrix.trace, Matrix.diag, Dlogmu, Matrix.diagonal_mul]
          simp only [Matrix.mul_apply, hWD, Matrix.conjTranspose_apply, Complex.re_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Complex.re_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          have hterm : (Real.log (mu a) : ℂ) * (W a b * (lam b : ℂ) * star (W a b)) =
              ((Complex.normSq (W a b) * lam b * Real.log (mu a) : ℝ) : ℂ) := by
            calc (Real.log (mu a) : ℂ) * (W a b * (lam b : ℂ) * star (W a b))
                = (W a b * star (W a b)) * (lam b : ℂ) * (Real.log (mu a) : ℂ) := by ring
              _ = (Complex.normSq (W a b) : ℂ) * (lam b : ℂ) * (Real.log (mu a) : ℂ) := by
                    rw [Complex.star_def, Complex.mul_conj]
              _ = ((Complex.normSq (W a b) * lam b * Real.log (mu a) : ℝ) : ℂ) := by
                    push_cast; ring
          rw [hterm, Complex.ofReal_re]
        rw [h1, h2, Fintype.sum_prod_type (α₁ := m) (α₂ := m), ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      · intro u hu0 hu1
        let d : m → m → ℝ := fun a b => (1 - u) * lam b + u * mu a
        have hd_pos : ∀ a b, 0 < d a b := by
          intro a b; simp only [d]
          have h1 : 0 < 1 - u := sub_pos.mpr hu1
          have hlb : 0 < lam b := hlam b
          have hma : 0 < mu a := hmu a
          positivity
        let H : Matrix m m ℂ := Matrix.of fun a b => W a b * ((lam b / d a b : ℝ) : ℂ)
        let X : Matrix m m ℂ := V * H * Uᴴ
        refine ⟨X, ?_, ?_⟩
        · have hXA : X * ρA = V * (H * Dlam) * Uᴴ := by
            calc X * ρA = (V * H * Uᴴ) * (U * Dlam * Uᴴ) := by rw [hA_eq]
              _ = V * (H * (Uᴴ * U) * Dlam) * Uᴴ := by simp only [Matrix.mul_assoc]
              _ = V * (H * Dlam) * Uᴴ := by rw [hU1, Matrix.mul_one]
          have hBX : σA * X = V * (Dmu * H) * Uᴴ := by
            calc σA * X = (V * Dmu * Vᴴ) * (V * H * Uᴴ) := by rw [hB_eq]
              _ = V * (Dmu * (Vᴴ * V) * H) * Uᴴ := by simp only [Matrix.mul_assoc]
              _ = V * (Dmu * H) * Uᴴ := by rw [hV1, Matrix.mul_one]
          have hmid : (1 - u) • (H * Dlam) + u • (Dmu * H) = W * Dlam := by
            ext a b
            simp only [Matrix.add_apply, Matrix.smul_apply, Dlam, Dmu, Matrix.mul_diagonal,
              Matrix.diagonal_mul, H, Matrix.of_apply, Complex.real_smul]
            have hd_ne : d a b ≠ 0 := ne_of_gt (hd_pos a b)
            have hscalar : (1 - u) * (lam b / d a b) * lam b + u * mu a * (lam b / d a b) = lam b := by
              calc (1 - u) * (lam b / d a b) * lam b + u * mu a * (lam b / d a b)
                  = d a b * (lam b / d a b) := by simp only [d]; ring
                _ = lam b := mul_div_cancel₀ _ hd_ne
            calc ((1 - u : ℝ) : ℂ) * (W a b * ((lam b / d a b : ℝ) : ℂ) * (lam b : ℂ)) +
                  (u : ℂ) * ((mu a : ℂ) * (W a b * ((lam b / d a b : ℝ) : ℂ)))
                = W a b * (((1 - u) * (lam b / d a b) * lam b + u * mu a * (lam b / d a b) : ℝ) : ℂ) := by
                    push_cast; ring
              _ = W a b * (lam b : ℂ) := by rw [hscalar]
          calc (1 - u) • (X * ρA) + u • (σA * X)
              = (1 - u) • (V * (H * Dlam) * Uᴴ) + u • (V * (Dmu * H) * Uᴴ) := by rw [hXA, hBX]
            _ = V * ((1 - u) • (H * Dlam) + u • (Dmu * H)) * Uᴴ := by
                  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
            _ = V * (W * Dlam) * Uᴴ := by rw [hmid]
            _ = (V * Vᴴ) * U * Dlam * Uᴴ := by simp only [W, Matrix.mul_assoc]
            _ = U * Dlam * Uᴴ := by rw [hV2, Matrix.one_mul]
            _ = ρA := hA_eq.symm
        · have htrXA : (Xᴴ * ρA).trace.re =
              ∑ a : m, ∑ b : m, Complex.normSq (W a b) * (lam b ^ 2 / d a b) := by
            have hcyc : (Xᴴ * ρA).trace = (Hᴴ * (W * Dlam)).trace := by
              have hXH : Xᴴ = U * Hᴴ * Vᴴ := by
                simp [X, Matrix.conjTranspose_mul, Matrix.mul_assoc]
              calc (Xᴴ * ρA).trace
                  = ((U * Hᴴ * Vᴴ) * (U * Dlam * Uᴴ)).trace := by rw [hXH, hA_eq]
                _ = (U * (Hᴴ * W * Dlam) * Uᴴ).trace := by simp only [W, Matrix.mul_assoc]
                _ = (Hᴴ * W * Dlam).trace := htr_U _
                _ = (Hᴴ * (W * Dlam)).trace := by rw [Matrix.mul_assoc]
            rw [hcyc]
            simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hWD,
              Matrix.conjTranspose_apply, H, Matrix.of_apply, Complex.re_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => ?_
            refine Finset.sum_congr rfl fun b _ => ?_
            have hterm : star (W a b * ((lam b / d a b : ℝ) : ℂ)) * (W a b * (lam b : ℂ)) =
                ((Complex.normSq (W a b) * (lam b ^ 2 / d a b) : ℝ) : ℂ) := by
              calc star (W a b * ((lam b / d a b : ℝ) : ℂ)) * (W a b * (lam b : ℂ))
                  = (W a b * (starRingEnd ℂ) (W a b)) * (((lam b / d a b) * lam b : ℝ) : ℂ) := by
                      simp; ring
                _ = ((Complex.normSq (W a b) * (lam b ^ 2 / d a b) : ℝ) : ℂ) := by
                      rw [Complex.mul_conj]; push_cast; ring
            rw [hterm, Complex.ofReal_re]
          have htrA : ρA.trace.re = ∑ a : m, ∑ b : m, Complex.normSq (W a b) * lam b := by
            have h1 : ρA.trace = Dlam.trace := by rw [hA_eq, htr_U]
            rw [h1]
            simp only [Dlam, Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
            have h2 : (∑ b : m, lam b) = ∑ b : m, (∑ a : m, Complex.normSq (W a b)) * lam b := by
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [hW_sum b, one_mul]
            rw [h2]
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
          rw [htrXA, htrA, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          have hd_ne : d a b ≠ 0 := ne_of_gt (hd_pos a b)
          have hfrac : lam b ^ 2 / d a b - lam b = u * (lam b * (lam b - mu a) / d a b) := by
            field_simp; simp only [d]; ring
          calc Complex.normSq (W a b) * (lam b ^ 2 / d a b) - Complex.normSq (W a b) * lam b
              = Complex.normSq (W a b) * (lam b ^ 2 / d a b - lam b) := by ring
            _ = Complex.normSq (W a b) * (u * (lam b * (lam b - mu a) / d a b)) := by rw [hfrac]
            _ = u * (Complex.normSq (W a b) * (lam b * (lam b - mu a) / d a b)) := by ring
    have hsylv_spec_AB :
        ∃ (W : Matrix (m × n) (m × n) ℂ) (lam mu : m × n → ℝ),
          (∀ i, 0 < lam i) ∧ (∀ i, 0 < mu i) ∧
          relEnt ρ σ = ∑ p : (m × n) × (m × n),
            Complex.normSq (W p.1 p.2) * lam p.2 * (Real.log (lam p.2) - Real.log (mu p.1)) ∧
          (∀ u : ℝ, 0 < u → u < 1 →
            ∃ Y : Matrix (m × n) (m × n) ℂ,
              (1 - u) • (Y * ρ) + u • (σ * Y) = ρ ∧
              (Yᴴ * ρ).trace.re - ρ.trace.re =
                u * ∑ p : (m × n) × (m × n),
                  Complex.normSq (W p.1 p.2) *
                    (lam p.2 * (lam p.2 - mu p.1) / ((1 - u) * lam p.2 + u * mu p.1))) := by
      let hρH := hρ.isHermitian
      let hσH := hσ.isHermitian
      let U : Matrix (m × n) (m × n) ℂ := (hρH.eigenvectorUnitary : Matrix (m × n) (m × n) ℂ)
      let V : Matrix (m × n) (m × n) ℂ := (hσH.eigenvectorUnitary : Matrix (m × n) (m × n) ℂ)
      let lam : m × n → ℝ := hρH.eigenvalues
      let mu : m × n → ℝ := hσH.eigenvalues
      let W : Matrix (m × n) (m × n) ℂ := Vᴴ * U
      have hlam : ∀ i, 0 < lam i := hρ.eigenvalues_pos
      have hmu : ∀ i, 0 < mu i := hσ.eigenvalues_pos
      have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hρH.eigenvectorUnitary.prop
      have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hσH.eigenvectorUnitary.prop
      have hV2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hσH.eigenvectorUnitary.prop
      have hWW : Wᴴ * W = 1 := by
        calc Wᴴ * W = (Uᴴ * V) * (Vᴴ * U) := by simp [W, Matrix.conjTranspose_mul]
          _ = Uᴴ * (V * Vᴴ) * U := by simp only [Matrix.mul_assoc]
          _ = Uᴴ * U := by rw [hV2, Matrix.mul_one]
          _ = 1 := hU1
      have hW_sum : ∀ b : m × n, ∑ a : m × n, Complex.normSq (W a b) = 1 := by
        intro b
        have hbb := congr_arg Complex.re (congr_fun (congr_fun hWW b) b)
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
          Complex.one_re, Complex.re_sum] at hbb
        rw [← hbb]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      let Dlam : Matrix (m × n) (m × n) ℂ := Matrix.diagonal (fun b => (lam b : ℂ))
      let Dmu : Matrix (m × n) (m × n) ℂ := Matrix.diagonal (fun a => (mu a : ℂ))
      let Dloglam : Matrix (m × n) (m × n) ℂ := Matrix.diagonal (fun b => (Real.log (lam b) : ℂ))
      let Dlogmu : Matrix (m × n) (m × n) ℂ := Matrix.diagonal (fun a => (Real.log (mu a) : ℂ))
      have hρ_eq : ρ = U * Dlam * Uᴴ := by
        simpa [U, lam, Dlam, Unitary.conjStarAlgAut_apply, Function.comp_def,
          Matrix.star_eq_conjTranspose] using hρH.spectral_theorem
      have hσ_eq : σ = V * Dmu * Vᴴ := by
        simpa [V, mu, Dmu, Unitary.conjStarAlgAut_apply, Function.comp_def,
          Matrix.star_eq_conjTranspose] using hσH.spectral_theorem
      have hlogρ : cfc Real.log ρ = U * Dloglam * Uᴴ := by
        rw [hρH.cfc_eq, Matrix.IsHermitian.cfc.eq_def]
        simp [U, lam, Dloglam, Unitary.conjStarAlgAut_apply, Function.comp_def,
          Matrix.star_eq_conjTranspose]
      have hlogσ : cfc Real.log σ = V * Dlogmu * Vᴴ := by
        rw [hσH.cfc_eq, Matrix.IsHermitian.cfc.eq_def]
        simp [V, mu, Dlogmu, Unitary.conjStarAlgAut_apply, Function.comp_def,
          Matrix.star_eq_conjTranspose]
      have htr_U : ∀ M : Matrix (m × n) (m × n) ℂ, (U * M * Uᴴ).trace = M.trace := by
        intro M
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
      have hWD : ∀ i j, (W * Dlam) i j = W i j * (lam j : ℂ) := by
        intro i j; simp [Dlam, Matrix.mul_diagonal]
      refine ⟨W, lam, mu, hlam, hmu, ?_, ?_⟩
      · rw [Leap.relEnt.eq_def, mul_sub, Matrix.trace_sub, Complex.sub_re]
        have h1 : (ρ * cfc Real.log ρ).trace.re =
            ∑ a : m × n, ∑ b : m × n, Complex.normSq (W a b) * lam b * Real.log (lam b) := by
          have hmul : ρ * cfc Real.log ρ = U * (Dlam * Dloglam) * Uᴴ := by
            calc ρ * cfc Real.log ρ
                = (U * Dlam * Uᴴ) * (U * Dloglam * Uᴴ) := by rw [hlogρ, hρ_eq]
              _ = U * (Dlam * (Uᴴ * U) * Dloglam) * Uᴴ := by simp only [Matrix.mul_assoc]
              _ = U * (Dlam * Dloglam) * Uᴴ := by rw [hU1, Matrix.mul_one]
          rw [hmul, htr_U]
          simp only [Dlam, Dloglam, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
            Complex.re_sum]
          have hre : (∑ b : m × n, ((lam b : ℂ) * (Real.log (lam b) : ℂ)).re) =
              ∑ b : m × n, (∑ a : m × n, Complex.normSq (W a b)) * (lam b * Real.log (lam b)) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← Complex.ofReal_mul, Complex.ofReal_re, hW_sum b, one_mul]
          rw [hre]
          simp_rw [Finset.sum_mul, mul_assoc]
          rw [Finset.sum_comm]
        have h2 : (ρ * cfc Real.log σ).trace.re =
            ∑ a : m × n, ∑ b : m × n, Complex.normSq (W a b) * lam b * Real.log (mu a) := by
          have htr2 : (ρ * cfc Real.log σ).trace = (Dlogmu * ((W * Dlam) * Wᴴ)).trace := by
            calc (ρ * cfc Real.log σ).trace
                = ((U * Dlam * Uᴴ * V) * (Dlogmu * Vᴴ)).trace := by
                    rw [hlogσ, hρ_eq]; simp only [Matrix.mul_assoc]
              _ = ((Dlogmu * Vᴴ) * (U * Dlam * Uᴴ * V)).trace := Matrix.trace_mul_comm _ _
              _ = (Dlogmu * ((W * Dlam) * Wᴴ)).trace := by
                    simp [W, Matrix.conjTranspose_mul, Matrix.mul_assoc]
          rw [htr2]
          simp only [Matrix.trace, Matrix.diag, Dlogmu, Matrix.diagonal_mul]
          simp only [Matrix.mul_apply, hWD, Matrix.conjTranspose_apply, Complex.re_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Complex.re_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          have hterm : (Real.log (mu a) : ℂ) * (W a b * (lam b : ℂ) * star (W a b)) =
              ((Complex.normSq (W a b) * lam b * Real.log (mu a) : ℝ) : ℂ) := by
            calc (Real.log (mu a) : ℂ) * (W a b * (lam b : ℂ) * star (W a b))
                = (W a b * star (W a b)) * (lam b : ℂ) * (Real.log (mu a) : ℂ) := by ring
              _ = (Complex.normSq (W a b) : ℂ) * (lam b : ℂ) * (Real.log (mu a) : ℂ) := by
                    rw [Complex.star_def, Complex.mul_conj]
              _ = ((Complex.normSq (W a b) * lam b * Real.log (mu a) : ℝ) : ℂ) := by
                    push_cast; ring
          rw [hterm, Complex.ofReal_re]
        rw [h1, h2, Fintype.sum_prod_type (α₁ := m × n) (α₂ := m × n), ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      · intro u hu0 hu1
        let d : m × n → m × n → ℝ := fun a b => (1 - u) * lam b + u * mu a
        have hd_pos : ∀ a b, 0 < d a b := by
          intro a b; simp only [d]
          have h1 : 0 < 1 - u := sub_pos.mpr hu1
          have hlb : 0 < lam b := hlam b
          have hma : 0 < mu a := hmu a
          positivity
        let H : Matrix (m × n) (m × n) ℂ :=
          Matrix.of fun a b => W a b * ((lam b / d a b : ℝ) : ℂ)
        let Y : Matrix (m × n) (m × n) ℂ := V * H * Uᴴ
        refine ⟨Y, ?_, ?_⟩
        · have hYρ : Y * ρ = V * (H * Dlam) * Uᴴ := by
            calc Y * ρ = (V * H * Uᴴ) * (U * Dlam * Uᴴ) := by rw [hρ_eq]
              _ = V * (H * (Uᴴ * U) * Dlam) * Uᴴ := by simp only [Matrix.mul_assoc]
              _ = V * (H * Dlam) * Uᴴ := by rw [hU1, Matrix.mul_one]
          have hσY : σ * Y = V * (Dmu * H) * Uᴴ := by
            calc σ * Y = (V * Dmu * Vᴴ) * (V * H * Uᴴ) := by rw [hσ_eq]
              _ = V * (Dmu * (Vᴴ * V) * H) * Uᴴ := by simp only [Matrix.mul_assoc]
              _ = V * (Dmu * H) * Uᴴ := by rw [hV1, Matrix.mul_one]
          have hmid : (1 - u) • (H * Dlam) + u • (Dmu * H) = W * Dlam := by
            ext a b
            simp only [Matrix.add_apply, Matrix.smul_apply, Dlam, Dmu, Matrix.mul_diagonal,
              Matrix.diagonal_mul, H, Matrix.of_apply, Complex.real_smul]
            have hd_ne : d a b ≠ 0 := ne_of_gt (hd_pos a b)
            have hscalar : (1 - u) * (lam b / d a b) * lam b + u * mu a * (lam b / d a b) = lam b := by
              calc (1 - u) * (lam b / d a b) * lam b + u * mu a * (lam b / d a b)
                  = d a b * (lam b / d a b) := by simp only [d]; ring
                _ = lam b := mul_div_cancel₀ _ hd_ne
            calc ((1 - u : ℝ) : ℂ) * (W a b * ((lam b / d a b : ℝ) : ℂ) * (lam b : ℂ)) +
                  (u : ℂ) * ((mu a : ℂ) * (W a b * ((lam b / d a b : ℝ) : ℂ)))
                = W a b * (((1 - u) * (lam b / d a b) * lam b + u * mu a * (lam b / d a b) : ℝ) : ℂ) := by
                    push_cast; ring
              _ = W a b * (lam b : ℂ) := by rw [hscalar]
          calc (1 - u) • (Y * ρ) + u • (σ * Y)
              = (1 - u) • (V * (H * Dlam) * Uᴴ) + u • (V * (Dmu * H) * Uᴴ) := by rw [hYρ, hσY]
            _ = V * ((1 - u) • (H * Dlam) + u • (Dmu * H)) * Uᴴ := by
                  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
            _ = V * (W * Dlam) * Uᴴ := by rw [hmid]
            _ = (V * Vᴴ) * U * Dlam * Uᴴ := by simp only [W, Matrix.mul_assoc]
            _ = U * Dlam * Uᴴ := by rw [hV2, Matrix.one_mul]
            _ = ρ := hρ_eq.symm
        · have htrYρ : (Yᴴ * ρ).trace.re =
              ∑ a : m × n, ∑ b : m × n, Complex.normSq (W a b) * (lam b ^ 2 / d a b) := by
            have hcyc : (Yᴴ * ρ).trace = (Hᴴ * (W * Dlam)).trace := by
              have hYH : Yᴴ = U * Hᴴ * Vᴴ := by
                simp [Y, Matrix.conjTranspose_mul, Matrix.mul_assoc]
              calc (Yᴴ * ρ).trace
                  = ((U * Hᴴ * Vᴴ) * (U * Dlam * Uᴴ)).trace := by rw [hYH, hρ_eq]
                _ = (U * (Hᴴ * W * Dlam) * Uᴴ).trace := by simp only [W, Matrix.mul_assoc]
                _ = (Hᴴ * W * Dlam).trace := htr_U _
                _ = (Hᴴ * (W * Dlam)).trace := by rw [Matrix.mul_assoc]
            rw [hcyc]
            simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hWD,
              Matrix.conjTranspose_apply, H, Matrix.of_apply, Complex.re_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => ?_
            refine Finset.sum_congr rfl fun b _ => ?_
            have hterm : star (W a b * ((lam b / d a b : ℝ) : ℂ)) * (W a b * (lam b : ℂ)) =
                ((Complex.normSq (W a b) * (lam b ^ 2 / d a b) : ℝ) : ℂ) := by
              calc star (W a b * ((lam b / d a b : ℝ) : ℂ)) * (W a b * (lam b : ℂ))
                  = (W a b * (starRingEnd ℂ) (W a b)) * (((lam b / d a b) * lam b : ℝ) : ℂ) := by
                      simp; ring
                _ = ((Complex.normSq (W a b) * (lam b ^ 2 / d a b) : ℝ) : ℂ) := by
                      rw [Complex.mul_conj]; push_cast; ring
            rw [hterm, Complex.ofReal_re]
          have htrρ : ρ.trace.re = ∑ a : m × n, ∑ b : m × n, Complex.normSq (W a b) * lam b := by
            have h1 : ρ.trace = Dlam.trace := by rw [hρ_eq, htr_U]
            rw [h1]
            simp only [Dlam, Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
            have h2 : (∑ b : m × n, lam b) =
                ∑ b : m × n, (∑ a : m × n, Complex.normSq (W a b)) * lam b := by
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [hW_sum b, one_mul]
            rw [h2]
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
          rw [htrYρ, htrρ, Fintype.sum_prod_type (α₁ := m × n) (α₂ := m × n), Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          have hd_ne : d a b ≠ 0 := ne_of_gt (hd_pos a b)
          have hfrac : lam b ^ 2 / d a b - lam b = u * (lam b * (lam b - mu a) / d a b) := by
            field_simp; simp only [d]; ring
          calc Complex.normSq (W a b) * (lam b ^ 2 / d a b) - Complex.normSq (W a b) * lam b
              = Complex.normSq (W a b) * (lam b ^ 2 / d a b - lam b) := by ring
            _ = Complex.normSq (W a b) * (u * (lam b * (lam b - mu a) / d a b)) := by rw [hfrac]
            _ = u * (Complex.normSq (W a b) * (lam b * (lam b - mu a) / d a b)) := by ring
    obtain ⟨W_A, lam_A, mu_A, hlam_A, hmu_A, hrel_A, hsylv_A⟩ := hsylv_spec_A
    obtain ⟨W, lam, mu, hlam, hmu, hrel_AB, hsylv_AB⟩ := hsylv_spec_AB
    change relEnt ρA σA ≤ relEnt ρ σ
    rw [hrel_A, hrel_AB]
    let w₁ : m × m → ℝ := fun p => Complex.normSq (W_A p.1 p.2)
    let a₁ : m × m → ℝ := fun p => lam_A p.2
    let b₁ : m × m → ℝ := fun p => mu_A p.1
    let w₂ : (m × n) × (m × n) → ℝ := fun q => Complex.normSq (W q.1 q.2)
    let a₂ : (m × n) × (m × n) → ℝ := fun q => lam q.2
    let b₂ : (m × n) × (m × n) → ℝ := fun q => mu q.1
    have ha₁ : ∀ p, 0 < a₁ p := fun p => hlam_A p.2
    have hb₁ : ∀ p, 0 < b₁ p := fun p => hmu_A p.1
    have ha₂ : ∀ q, 0 < a₂ q := fun q => hlam q.2
    have hb₂ : ∀ q, 0 < b₂ q := fun q => hmu q.1
    have h_deriv : ∀ u : ℝ, 0 < u → u < 1 →
        (∑ p : m × m, w₁ p * (a₁ p * (a₁ p - b₁ p) / ((1 - u) * a₁ p + u * b₁ p))) ≤
        (∑ q : (m × n) × (m × n), w₂ q * (a₂ q * (a₂ q - b₂ q) / ((1 - u) * a₂ q + u * b₂ q))) := by
      intro u hu0 hu1
      obtain ⟨X, hX_eq, hX_tr⟩ := hsylv_A u hu0 hu1
      obtain ⟨Y, hY_eq, hY_tr⟩ := hsylv_AB u hu0 hu1
      have hquad_le : (Xᴴ * ρA).trace.re ≤ (Yᴴ * ρ).trace.re := by
        let lift : Matrix m m ℂ → Matrix (m × n) (m × n) ℂ :=
          fun A => Matrix.of fun ik jl => if ik.2 = jl.2 then A ik.1 jl.1 else 0
        have hlift_conj : ∀ A : Matrix m m ℂ, (lift A)ᴴ = lift (Aᴴ) := by
          intro A; ext ik jl
          simp only [lift, Matrix.conjTranspose_apply, Matrix.of_apply]
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd h1.symm h2
          · exact absurd h2.symm h1
          · exact star_zero _
        have hlift_mul : ∀ A B : Matrix m m ℂ, lift A * lift B = lift (A * B) := by
          intro A B; ext ik jl
          simp only [lift, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
          have hinner : ∀ r : m,
              (∑ s : n, (if ik.2 = s then A ik.1 r else 0) * (if s = jl.2 then B r jl.1 else 0)) =
              if ik.2 = jl.2 then A ik.1 r * B r jl.1 else 0 := by
            intro r
            rw [Finset.sum_eq_single ik.2]
            · simp only [↓reduceIte, mul_ite, mul_zero]
            · intro s _ hs; simp [hs.symm]
            · intro h_abs; exact False.elim (h_abs (Finset.mem_univ ik.2))
          simp_rw [hinner]
          split_ifs with h
          · rfl
          · simp
        have hlift_tr : ∀ (A : Matrix m m ℂ) (M : Matrix (m × n) (m × n) ℂ),
            (lift A * M).trace = (A * ptraceRight M).trace := by
          intro A M
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, lift, Matrix.of_apply,
            Fintype.sum_prod_type, Leap.ptraceRight.eq_def]
          refine Finset.sum_congr rfl fun i _ => ?_
          have h1 : ∀ k : n, ∀ j : m,
              (∑ l : n, (if k = l then A i j else 0) * M (j, l) (i, k)) =
                A i j * M (j, k) (i, k) := by
            intro k j
            rw [Finset.sum_eq_single k]
            · simp
            · intro l _ hl; simp [hl.symm]
            · intro h_abs; exact False.elim (h_abs (Finset.mem_univ k))
          simp_rw [h1]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum]
        let Xhat := lift X
        let Z := Y - Xhat
        let MXhat := (1 - u) • (Xhat * ρ) + u • (σ * Xhat)
        let MZ := (1 - u) • (Z * ρ) + u • (σ * Z)
        have hMZ_nonneg : 0 ≤ (Zᴴ * MZ).trace.re := by
          have hexp : Zᴴ * MZ = (1 - u) • (Zᴴ * (Z * ρ)) + u • (Zᴴ * (σ * Z)) := by
            simp only [MZ, Matrix.mul_add, Matrix.mul_smul]
          rw [hexp, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
            Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
          have ht1 : 0 ≤ (Zᴴ * (Z * ρ)).trace.re := by
            rw [Matrix.trace_mul_comm]
            exact (Complex.le_def.mp (hρ.posSemidef.mul_mul_conjTranspose_same Z).trace_nonneg).1
          have ht2 : 0 ≤ (Zᴴ * (σ * Z)).trace.re := by
            rw [← Matrix.mul_assoc]
            exact (Complex.le_def.mp (hσ.posSemidef.conjTranspose_mul_mul_same Z).trace_nonneg).1
          have hu0' : 0 ≤ u := hu0.le
          have hu1' : 0 ≤ 1 - u := sub_nonneg.mpr hu1.le
          positivity
        have hMZ_eq : MZ = ρ - MXhat := by
          have hdiff : ((1 - u) • (Y * ρ) + u • (σ * Y)) - MXhat = MZ := by
            simp only [MZ, MXhat, Z, Matrix.sub_mul, Matrix.mul_sub, smul_sub, sub_add_sub_comm]
          rw [← hdiff, hY_eq]
        have htr3 : (Xhatᴴ * ρ).trace = (Xᴴ * ρA).trace := by
          rw [hlift_conj, hlift_tr]
        have htr4 : (Xhatᴴ * MXhat).trace = (Xᴴ * ρA).trace := by
          have hp1 : (Xhatᴴ * (Xhat * ρ)).trace = (Xᴴ * (X * ρA)).trace := by
            rw [← Matrix.mul_assoc, hlift_conj, hlift_mul, hlift_tr, Matrix.mul_assoc]
          have hp2 : (Xhatᴴ * (σ * Xhat)).trace = (Xᴴ * (σA * X)).trace := by
            calc (Xhatᴴ * (σ * Xhat)).trace
                = ((Xhatᴴ * σ) * Xhat).trace := by rw [Matrix.mul_assoc]
              _ = (Xhat * (Xhatᴴ * σ)).trace := Matrix.trace_mul_comm _ _
              _ = ((Xhat * Xhatᴴ) * σ).trace := by rw [Matrix.mul_assoc]
              _ = (lift (X * Xᴴ) * σ).trace := by rw [hlift_conj, hlift_mul]
              _ = ((X * Xᴴ) * σA).trace := hlift_tr _ _
              _ = (X * (Xᴴ * σA)).trace := by rw [Matrix.mul_assoc]
              _ = ((Xᴴ * σA) * X).trace := Matrix.trace_mul_comm _ _
              _ = (Xᴴ * (σA * X)).trace := by rw [Matrix.mul_assoc]
          calc (Xhatᴴ * MXhat).trace
              = (1 - u) • (Xhatᴴ * (Xhat * ρ)).trace + u • (Xhatᴴ * (σ * Xhat)).trace := by
                  simp only [MXhat, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
                    Matrix.trace_smul]
            _ = (1 - u) • (Xᴴ * (X * ρA)).trace + u • (Xᴴ * (σA * X)).trace := by rw [hp1, hp2]
            _ = (Xᴴ * ((1 - u) • (X * ρA) + u • (σA * X))).trace := by
                  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul]
            _ = (Xᴴ * ρA).trace := by rw [hX_eq]
        have htr2 : (Yᴴ * MXhat).trace = star ((Xᴴ * ρA).trace) := by
          have hsmul_conj : ∀ (r : ℝ) (M : Matrix (m × n) (m × n) ℂ), (r • M)ᴴ = r • Mᴴ := by
            intro r M; ext p q; simp [Complex.real_smul]
          have hq1 : (Yᴴ * (Xhat * ρ)).trace = ((Y * ρ)ᴴ * Xhat).trace := by
            calc (Yᴴ * (Xhat * ρ)).trace
                = ((Yᴴ * Xhat) * ρ).trace := by rw [Matrix.mul_assoc]
              _ = (ρ * (Yᴴ * Xhat)).trace := Matrix.trace_mul_comm _ _
              _ = ((ρᴴ * Yᴴ) * Xhat).trace := by rw [hρ.isHermitian.eq, Matrix.mul_assoc]
              _ = ((Y * ρ)ᴴ * Xhat).trace := by rw [Matrix.conjTranspose_mul]
          have hq2 : (Yᴴ * (σ * Xhat)).trace = ((σ * Y)ᴴ * Xhat).trace := by
            calc (Yᴴ * (σ * Xhat)).trace
                = ((Yᴴ * σ) * Xhat).trace := by rw [Matrix.mul_assoc]
              _ = ((Yᴴ * σᴴ) * Xhat).trace := by rw [hσ.isHermitian.eq]
              _ = ((σ * Y)ᴴ * Xhat).trace := by rw [Matrix.conjTranspose_mul]
          have hconj_eq : (((1 - u) • (Y * ρ) + u • (σ * Y))ᴴ * Xhat).trace =
              (1 - u) • ((Y * ρ)ᴴ * Xhat).trace + u • ((σ * Y)ᴴ * Xhat).trace := by
            rw [Matrix.conjTranspose_add, hsmul_conj, hsmul_conj, Matrix.add_mul,
              Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
              Matrix.trace_smul]
          calc (Yᴴ * MXhat).trace
              = (1 - u) • (Yᴴ * (Xhat * ρ)).trace + u • (Yᴴ * (σ * Xhat)).trace := by
                  simp only [MXhat, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
                    Matrix.trace_smul]
            _ = (1 - u) • ((Y * ρ)ᴴ * Xhat).trace + u • ((σ * Y)ᴴ * Xhat).trace := by
                  rw [hq1, hq2]
            _ = (((1 - u) • (Y * ρ) + u • (σ * Y))ᴴ * Xhat).trace := hconj_eq.symm
            _ = (ρᴴ * Xhat).trace := by rw [hY_eq]
            _ = ((Xhatᴴ * ρ)ᴴ).trace := by simp [Matrix.conjTranspose_mul]
            _ = star ((Xhatᴴ * ρ).trace) := Matrix.trace_conjTranspose _
            _ = star ((Xᴴ * ρA).trace) := by rw [htr3]
        have htr_total : (Zᴴ * MZ).trace = (Yᴴ * ρ).trace - star ((Xᴴ * ρA).trace) := by
          have hexp : Zᴴ * MZ = Yᴴ * ρ - Yᴴ * MXhat - Xhatᴴ * ρ + Xhatᴴ * MXhat := by
            rw [hMZ_eq]
            simp only [Z, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
            abel
          rw [hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, htr2, htr3, htr4]
          abel
        have hre_total : (Zᴴ * MZ).trace.re = (Yᴴ * ρ).trace.re - (Xᴴ * ρA).trace.re := by
          rw [htr_total, Complex.sub_re, Complex.star_def, Complex.conj_re]
        linarith
      have htr_ρA : ρA.trace.re = ρ.trace.re := htr_eq
      have hmul_le :
          u * (∑ p : m × m, w₁ p * (a₁ p * (a₁ p - b₁ p) / ((1 - u) * a₁ p + u * b₁ p))) ≤
          u * (∑ q : (m × n) × (m × n), w₂ q * (a₂ q * (a₂ q - b₂ q) / ((1 - u) * a₂ q + u * b₂ q))) := by
        simp only [w₁, a₁, b₁, w₂, a₂, b₂]
        linarith
      exact le_of_mul_le_mul_left hmul_le hu0
    have hconv_pos : ∀ {a b u : ℝ}, 0 < a → 0 < b → 0 ≤ u → u ≤ 1 → 0 < (1 - u) * a + u * b := by
      intro a b u ha hb hu0 hu1
      rcases eq_or_lt_of_le hu0 with rfl | hu0'
      · simpa using ha
      · have h1 : 0 ≤ (1 - u) * a := mul_nonneg (sub_nonneg.mpr hu1) ha.le
        have h2 : 0 < u * b := mul_pos hu0' hb
        linarith
    let F₁ : ℝ → ℝ := fun u => ∑ i : m × m, w₁ i * (-a₁ i * Real.log ((1 - u) * a₁ i + u * b₁ i))
    let F₂ : ℝ → ℝ := fun u =>
      ∑ j : (m × n) × (m × n), w₂ j * (-a₂ j * Real.log ((1 - u) * a₂ j + u * b₂ j))
    let Φ : ℝ → ℝ := fun u => F₂ u - F₁ u
    let g₁ : ℝ → ℝ := fun u =>
      ∑ i : m × m, w₁ i * (a₁ i * (a₁ i - b₁ i) / ((1 - u) * a₁ i + u * b₁ i))
    let g₂ : ℝ → ℝ := fun u =>
      ∑ j : (m × n) × (m × n), w₂ j * (a₂ j * (a₂ j - b₂ j) / ((1 - u) * a₂ j + u * b₂ j))
    have hcont₁ : ContinuousOn F₁ (Set.Icc 0 1) := by
      refine continuousOn_finsetSum Finset.univ fun i _ => ?_
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
      refine ContinuousOn.log ?_ (fun u hu => ne_of_gt (hconv_pos (ha₁ i) (hb₁ i) hu.1 hu.2))
      fun_prop
    have hcont₂ : ContinuousOn F₂ (Set.Icc 0 1) := by
      refine continuousOn_finsetSum Finset.univ fun j _ => ?_
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
      refine ContinuousOn.log ?_ (fun u hu => ne_of_gt (hconv_pos (ha₂ j) (hb₂ j) hu.1 hu.2))
      fun_prop
    have hterm_deriv : ∀ (w a b u : ℝ), 0 < a → 0 < b → 0 < u → u < 1 →
        HasDerivAt (fun t => w * (-a * Real.log ((1 - t) * a + t * b)))
          (w * (a * (a - b) / ((1 - u) * a + u * b))) u := by
      intro w a b u ha hb hu0 hu1
      have hd_ne : (1 - u) * a + u * b ≠ 0 := ne_of_gt (hconv_pos ha hb hu0.le hu1.le)
      have hlin := (((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).mul_const a).add
        ((hasDerivAt_id u).mul_const b)
      have hlin' : HasDerivAt (fun t => (1 - t) * a + t * b) ((0 - 1) * a + 1 * b) u := by
        convert hlin using 1
        ext t; simp
      have hlog := hlin'.log hd_ne
      have hmul := (hlog.const_mul (-a)).const_mul w
      convert hmul using 1; ring
    have hΦ_deriv : ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt Φ (g₂ u - g₁ u) u := by
      intro u hu
      have hd₁ : HasDerivAt F₁ (g₁ u) u := by
        convert HasDerivAt.sum (u := Finset.univ)
          (fun i _ => hterm_deriv (w₁ i) (a₁ i) (b₁ i) u (ha₁ i) (hb₁ i) hu.1 hu.2) using 1
        ext t; simp [F₁]
      have hd₂ : HasDerivAt F₂ (g₂ u) u := by
        convert HasDerivAt.sum (u := Finset.univ)
          (fun j _ => hterm_deriv (w₂ j) (a₂ j) (b₂ j) u (ha₂ j) (hb₂ j) hu.1 hu.2) using 1
        ext t; simp [F₂]
      exact hd₂.sub hd₁
    obtain ⟨c, hc, hc_eq⟩ := exists_hasDerivAt_eq_slope Φ (fun u => g₂ u - g₁ u) zero_lt_one
      (hcont₂.sub hcont₁) hΦ_deriv
    have hc_nonneg : 0 ≤ g₂ c - g₁ c := sub_nonneg.mpr (h_deriv c hc.1 hc.2)
    have hΦ_diff : 0 ≤ Φ 1 - Φ 0 := by
      rw [sub_zero, div_one] at hc_eq
      linarith
    have hF₁_eval : F₁ 1 - F₁ 0 =
        ∑ i : m × m, w₁ i * a₁ i * (Real.log (a₁ i) - Real.log (b₁ i)) := by
      simp only [F₁, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp; ring
    have hF₂_eval : F₂ 1 - F₂ 0 =
        ∑ j : (m × n) × (m × n), w₂ j * a₂ j * (Real.log (a₂ j) - Real.log (b₂ j)) := by
      simp only [F₂, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp; ring
    have hΦ_expand : Φ 1 - Φ 0 = (F₂ 1 - F₂ 0) - (F₁ 1 - F₁ 0) := by simp only [Φ]; ring
    change (∑ i : m × m, w₁ i * a₁ i * (Real.log (a₁ i) - Real.log (b₁ i))) ≤
      (∑ j : (m × n) × (m × n), w₂ j * a₂ j * (Real.log (a₂ j) - Real.log (b₂ j)))
    linarith

end Leap
