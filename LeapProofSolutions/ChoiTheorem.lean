import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Ex 4.4.1 / Thm 4.4.1: Choi's theorem and Kraus representation. -/
theorem choi_theorem (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) :
    (IsCP Φ ↔ (choi Φ).PosSemidef) ∧
      (IsCP Φ ↔ ∃ K : m × n → Matrix n m ℂ, ∀ X, Φ X = kraus K X) := by
  have h1 : IsCP Φ → (choi Φ).PosSemidef := by
    intro hCP
    let k := Fintype.card m
    let e : m ≃ Fin k := Fintype.equivFin m
    let V : Matrix (Fin k × m) Unit ℂ :=
      fun p _ => if e.symm p.1 = p.2 then 1 else 0
    let X : Matrix (Fin k × m) (Fin k × m) ℂ := V * Vᴴ
    have hX : X.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
    have hAmp : (ampliate (Fin k) Φ X).PosSemidef := hCP k X hX
    let f : m × n → Fin k × n := fun p => (e p.1, p.2)
    have hSub : ((ampliate (Fin k) Φ X).submatrix f f).PosSemidef := hAmp.submatrix f
    suffices hEq : (ampliate (Fin k) Φ X).submatrix f f = choi Φ by
      rwa [hEq] at hSub
    ext ⟨a, c⟩ ⟨b, d⟩
    have hBlock : (fun a' b' => X (e a, a') (e b, b')) = Matrix.single a b (1 : ℂ) := by
      ext a' b'
      change (V * Vᴴ) (e a, a') (e b, b') = Matrix.single a b (1 : ℂ) a' b'
      rw [Matrix.mul_apply, Matrix.single_apply, Fintype.sum_unique, Matrix.conjTranspose_apply]
      simp only [V, Equiv.symm_apply_apply]
      by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]
    simp only [Matrix.submatrix_apply, f, ampliate, choi, hBlock]
  have h2 : (choi Φ).PosSemidef → ∃ B : Matrix (m × n) (m × n) ℂ, choi Φ = B * Bᴴ := by
    intro hJ
    let hH := hJ.isHermitian
    let U : Matrix (m × n) (m × n) ℂ := (hH.eigenvectorUnitary : Matrix (m × n) (m × n) ℂ)
    let d : m × n → ℂ := fun r => ((Real.sqrt (hH.eigenvalues r) : ℝ) : ℂ)
    let D : Matrix (m × n) (m × n) ℂ := Matrix.diagonal d
    refine ⟨U * D, ?_⟩
    have hDH : Dᴴ = D := by
      rw [Matrix.diagonal_conjTranspose]
      congr 1
      ext r
      simp [d]
    have hDD : D * D = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      ext r
      simp only [d, Function.comp_apply]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hJ.eigenvalues_nonneg r)]
      rfl
    calc choi Φ
      _ = U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Uᴴ := by
          simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hH.spectral_theorem
      _ = U * (D * D) * Uᴴ := by rw [← hDD]
      _ = U * (D * Dᴴ) * Uᴴ := by rw [hDH]
      _ = (U * D) * (U * D)ᴴ := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h3 : ∀ B : Matrix (m × n) (m × n) ℂ, choi Φ = B * Bᴴ →
      ∀ X : Matrix m m ℂ, Φ X = kraus (fun r c a => B (a, c) r) X := by
    intro B hB X
    let K : m × n → Matrix n m ℂ := fun r c a => B (a, c) r
    have hX_sum : X = ∑ a : m, ∑ b : m, X a b • Matrix.single a b (1 : ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    ext c d
    have hLHS : Φ X c d = ∑ a : m, ∑ b : m, ∑ r : m × n, X a b * (B (a, c) r * star (B (b, d) r)) := by
      conv_lhs => rw [hX_sum]
      simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have hChoi : Φ (Matrix.single a b 1) c d = ∑ r : m × n, B (a, c) r * star (B (b, d) r) := by
        change choi Φ (a, c) (b, d) = _
        rw [hB]
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [hChoi, Finset.mul_sum]
    have hRHS : kraus K X c d = ∑ a : m, ∑ b : m, ∑ r : m × n, B (a, c) r * X a b * star (B (b, d) r) := by
      calc kraus K X c d
        _ = ∑ r : m × n, ∑ b : m, ∑ a : m, B (a, c) r * X a b * star (B (b, d) r) := by
            simp only [kraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
            rfl
        _ = ∑ b : m, ∑ r : m × n, ∑ a : m, B (a, c) r * X a b * star (B (b, d) r) := by
            rw [Finset.sum_comm]
        _ = ∑ b : m, ∑ a : m, ∑ r : m × n, B (a, c) r * X a b * star (B (b, d) r) := by
            exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
        _ = ∑ a : m, ∑ b : m, ∑ r : m × n, B (a, c) r * X a b * star (B (b, d) r) := by
            rw [Finset.sum_comm]
    rw [hLHS, hRHS]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  have h4 : ∀ K : m × n → Matrix n m ℂ, (∀ X, Φ X = kraus K X) → IsCP Φ := by
    intro K hK k X hX
    let L : m × n → Matrix (Fin k × n) (Fin k × m) ℂ :=
      fun r p q => if p.1 = q.1 then K r p.2 q.2 else 0
    have hAmpEq : ampliate (Fin k) Φ X = ∑ r : m × n, L r * X * (L r)ᴴ := by
      ext ⟨i, c⟩ ⟨j, d⟩
      let X_ij : Matrix m m ℂ := fun a b => X (i, a) (j, b)
      trans kraus K X_ij c d
      · exact congr_fun (congr_fun (hK X_ij) c) d
      · simp only [kraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
        refine Finset.sum_congr rfl fun r _ => ?_
        symm
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hOuter : ∀ j' : Fin k,
            (∑ p : Fin k × m, L r (i, c) p * X p (j', b)) * star (L r (j, d) (j', b)) =
            if j = j' then (∑ a : m, K r c a * X (i, a) (j', b)) * star (K r d b) else 0 := by
          intro j'
          have hInner : ∑ p : Fin k × m, L r (i, c) p * X p (j', b) = ∑ a : m, K r c a * X (i, a) (j', b) := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => ?_
            simp only [L, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          rw [hInner]
          by_cases hj : j = j' <;> simp [L, hj]
        simp_rw [hOuter]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        rfl
    rw [hAmpEq]
    exact Matrix.posSemidef_sum Finset.univ fun r _ => hX.mul_mul_conjTranspose_same (L r)
  have h23 : (choi Φ).PosSemidef → ∃ K : m × n → Matrix n m ℂ, ∀ X, Φ X = kraus K X := by
    intro hJ
    obtain ⟨B, hB⟩ := h2 hJ
    exact ⟨fun r c a => B (a, c) r, h3 B hB⟩
  have h4' : (∃ K : m × n → Matrix n m ℂ, ∀ X, Φ X = kraus K X) → IsCP Φ := by
    rintro ⟨K, hK⟩
    exact h4 K hK
  exact ⟨⟨h1, fun hJ => h4' (h23 hJ)⟩, ⟨fun hCP => h23 (h1 hCP), h4'⟩⟩

end Leap
