import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Def 12.3.2: every rotated Petz map recovers σ, is trace-preserving on the
support, and is completely positive (has a Kraus form). -/
theorem rotatedPetz_props {ι : Type*} [Fintype ι] (K : ι → Matrix n m ℂ)
    (hTP : ∑ i, (K i)ᴴ * K i = 1) (σ : Matrix m m ℂ) (hσ : σ.PosSemidef) (t : ℝ) :
    rotatedPetz K σ t (kraus K σ) = σ ∧
      (∀ X : Matrix n n ℂ, (rotatedPetz K σ t X).trace = (rpowS (kraus K σ) 0 * X).trace) ∧
      ∃ L : ι → Matrix m n ℂ, ∀ X, rotatedPetz K σ t X = kraus L X := by
  let ω : Matrix n n ℂ := kraus K σ
  let S : Matrix m m ℂ := rpowS σ (1 / 2)
  let W : Matrix n n ℂ := rpowS ω (-1 / 2)
  let P : Matrix n n ℂ := rpowS ω 0
  have hω : ω.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun i _ => hσ.mul_mul_conjTranspose_same (K i))
  
  have hS_conj : Sᴴ = S := by
    dsimp only [S, rpowS]
    rw [← Matrix.star_eq_conjTranspose]
    exact (IsSelfAdjoint.cfc (f := fun x : ℝ => if x = 0 then 0 else x ^ (1 / 2 : ℝ)) (a := σ)).star_eq
  have hW_conj : Wᴴ = W := by
    dsimp only [W, rpowS]
    rw [← Matrix.star_eq_conjTranspose]
    exact (IsSelfAdjoint.cfc (f := fun x : ℝ => if x = 0 then 0 else x ^ (-1 / 2 : ℝ)) (a := ω)).star_eq
  have hP_conj : Pᴴ = P := by
    dsimp only [P, rpowS]
    rw [← Matrix.star_eq_conjTranspose]
    exact (IsSelfAdjoint.cfc (f := fun x : ℝ => if x = 0 then 0 else x ^ (0 : ℝ)) (a := ω)).star_eq
  have hipow_σ_conj : (ipowS σ t)ᴴ = ipowS σ (-t) := by
    unfold ipowS
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
    have hc : (cfc (fun x : ℝ => if x = 0 then 0 else Real.cos (t * Real.log x)) σ)ᴴ =
        cfc (fun x : ℝ => if x = 0 then 0 else Real.cos ((-t) * Real.log x)) σ := by
      rw [← Matrix.star_eq_conjTranspose, (IsSelfAdjoint.cfc (a := σ)).star_eq]
      congr 1; funext x
      by_cases hx : x = 0
      · simp [hx]
      · simp [hx, neg_mul, Real.cos_neg]
    have hs : (cfc (fun x : ℝ => if x = 0 then 0 else Real.sin (t * Real.log x)) σ)ᴴ =
        cfc (fun x : ℝ => if x = 0 then 0 else Real.sin (t * Real.log x)) σ := by
      rw [← Matrix.star_eq_conjTranspose]
      exact (IsSelfAdjoint.cfc (a := σ)).star_eq
    have hI : star Complex.I = -Complex.I := Complex.conj_I
    rw [hc, hs, hI, neg_smul, ← smul_neg, ← cfc_neg]
    have hfn : (fun x : ℝ => -(if x = 0 then 0 else Real.sin (t * Real.log x))) =
        (fun x : ℝ => if x = 0 then 0 else Real.sin ((-t) * Real.log x)) := by
      funext x
      by_cases hx : x = 0
      · simp [hx]
      · simp [hx, neg_mul, Real.sin_neg]
    rw [hfn]
  have hipow_ω_conj : (ipowS ω (-t))ᴴ = ipowS ω t := by
    unfold ipowS
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
    have hc : (cfc (fun x : ℝ => if x = 0 then 0 else Real.cos ((-t) * Real.log x)) ω)ᴴ =
        cfc (fun x : ℝ => if x = 0 then 0 else Real.cos (t * Real.log x)) ω := by
      rw [← Matrix.star_eq_conjTranspose, (IsSelfAdjoint.cfc (a := ω)).star_eq]
      congr 1; funext x
      by_cases hx : x = 0
      · simp [hx]
      · simp [hx, neg_mul, Real.cos_neg]
    have hs : (cfc (fun x : ℝ => if x = 0 then 0 else Real.sin ((-t) * Real.log x)) ω)ᴴ =
        cfc (fun x : ℝ => if x = 0 then 0 else Real.sin ((-t) * Real.log x)) ω := by
      rw [← Matrix.star_eq_conjTranspose]
      exact (IsSelfAdjoint.cfc (a := ω)).star_eq
    have hI : star Complex.I = -Complex.I := Complex.conj_I
    rw [hc, hs, hI, neg_smul, ← smul_neg, ← cfc_neg]
    have hfn : (fun x : ℝ => -(if x = 0 then 0 else Real.sin ((-t) * Real.log x))) =
        (fun x : ℝ => if x = 0 then 0 else Real.sin (t * Real.log x)) := by
      funext x
      by_cases hx : x = 0
      · simp [hx]
      · simp [hx, neg_mul, Real.sin_neg]
    rw [hfn]
  
  let L : ι → Matrix m n ℂ := fun i => ipowS σ t * S * (K i)ᴴ * W * ipowS ω (-t)
  have hL_adj : ∀ i : ι, (L i)ᴴ = ipowS ω t * W * K i * S * ipowS σ (-t) := by
    intro i
    dsimp only [L]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hS_conj, hW_conj, hipow_σ_conj, hipow_ω_conj, Matrix.mul_assoc]
  have h_kraus : ∀ X : Matrix n n ℂ, rotatedPetz K σ t X = kraus L X := by
    intro X
    change ipowS σ t * (S * (∑ i, (K i)ᴴ * (W * (ipowS ω (-t) * X * ipowS ω t) * W) * K i) * S) * ipowS σ (-t) =
      ∑ i, L i * X * (L i)ᴴ
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hL_adj i]
    dsimp only [L]
    simp only [Matrix.mul_assoc]
  
  have hHσ : σ.IsHermitian := hσ.isHermitian
  have hσ_self : σ = (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) hHσ.eigenvectorUnitary)
      (Matrix.diagonal (fun j => (hHσ.eigenvalues j : ℂ))) := hHσ.spectral_theorem
  have hσ_cfc : ∀ f : ℝ → ℝ, cfc f σ = (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) hHσ.eigenvectorUnitary)
      (Matrix.diagonal (fun j => (f (hHσ.eigenvalues j) : ℂ))) := by
    intro f; rw [Matrix.IsHermitian.cfc_eq hHσ, Matrix.IsHermitian.cfc]; rfl
  have hσ_rpow : ∀ s : ℝ, rpowS σ s = (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) hHσ.eigenvectorUnitary)
      (Matrix.diagonal (fun j => ((if hHσ.eigenvalues j = 0 then 0 else (hHσ.eigenvalues j) ^ s : ℝ) : ℂ))) :=
    fun s => hσ_cfc _
  have hσ_ipow : ∀ u : ℝ, ipowS σ u = (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) hHσ.eigenvectorUnitary)
      (Matrix.diagonal (fun j =>
        ((if hHσ.eigenvalues j = 0 then 0 else Real.cos (u * Real.log (hHσ.eigenvalues j)) : ℝ) : ℂ) +
        Complex.I * ((if hHσ.eigenvalues j = 0 then 0 else Real.sin (u * Real.log (hHσ.eigenvalues j)) : ℝ) : ℂ))) := by
    intro u; unfold ipowS
    rw [hσ_cfc, hσ_cfc, ← map_smul, ← map_add, ← Matrix.diagonal_smul, ← Matrix.diagonal_add]; rfl
  have hσ_ipow_mul_neg : ∀ u : ℝ, ipowS σ u * ipowS σ (-u) = rpowS σ 0 := by
    intro u
    rw [hσ_ipow u, hσ_ipow (-u), hσ_rpow 0, ← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2; funext j
    by_cases hj : hHσ.eigenvalues j = 0
    · simp [hj]
    · simp only [hj, ↓reduceIte, neg_mul, Real.cos_neg, Real.sin_neg, Real.rpow_zero,
        Complex.ofReal_neg, Complex.ofReal_one]
      set c : ℝ := Real.cos (u * Real.log (hHσ.eigenvalues j))
      set s : ℝ := Real.sin (u * Real.log (hHσ.eigenvalues j))
      calc ((c : ℂ) + Complex.I * (s : ℂ)) * ((c : ℂ) + Complex.I * -(s : ℂ))
          = (c : ℂ) ^ 2 - Complex.I ^ 2 * (s : ℂ) ^ 2 := by ring
        _ = (c : ℂ) ^ 2 + (s : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
        _ = ((c ^ 2 + s ^ 2 : ℝ) : ℂ) := by push_cast; ring
        _ = 1 := by rw [Real.cos_sq_add_sin_sq]; simp
  have hσ_comm : ipowS σ t * σ = σ * ipowS σ t := by
    refine (congrArg₂ (· * ·) (hσ_ipow t) hσ_self).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· * ·) hσ_self (hσ_ipow t)).symm
    rw [← map_mul, ← map_mul, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2; funext j; ring
  have hσ_mul_rpow0 : σ * rpowS σ 0 = σ := by
    refine (congrArg₂ (· * ·) hσ_self (hσ_rpow 0)).trans ?_
    refine Eq.trans ?_ hσ_self.symm
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2; funext j
    by_cases hj : hHσ.eigenvalues j = 0 <;> simp [hj, Real.rpow_zero]
  have hS_mul_rpow0 : S * rpowS σ 0 = S := by
    dsimp only [S]
    rw [hσ_rpow (1 / 2), hσ_rpow 0, ← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2; funext j
    by_cases hj : hHσ.eigenvalues j = 0 <;> simp [hj, Real.rpow_zero]
  have hS_sq : S * S = σ := by
    dsimp only [S]
    refine (congrArg₂ (· * ·) (hσ_rpow (1 / 2)) (hσ_rpow (1 / 2))).trans ?_
    refine Eq.trans ?_ hσ_self.symm
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2; funext j
    by_cases hj : hHσ.eigenvalues j = 0
    · simp [hj]
    · have hpos : 0 < hHσ.eigenvalues j := lt_of_le_of_ne (hσ.eigenvalues_nonneg j) (Ne.symm hj)
      simp only [hj, ↓reduceIte, ← Complex.ofReal_mul, ← Real.rpow_add hpos]
      norm_num
  have hσ_rot : ipowS σ t * σ * ipowS σ (-t) = σ := by
    rw [hσ_comm, Matrix.mul_assoc, hσ_ipow_mul_neg t, hσ_mul_rpow0]
  have hS_rot : S * ipowS σ (-t) * ipowS σ t * S = σ := by
    have ht : ipowS σ (-t) * ipowS σ t = rpowS σ 0 := by
      simpa [neg_neg] using hσ_ipow_mul_neg (-t)
    calc S * ipowS σ (-t) * ipowS σ t * S
        = (S * (ipowS σ (-t) * ipowS σ t)) * S := by simp only [Matrix.mul_assoc]
      _ = (S * rpowS σ 0) * S := by rw [ht]
      _ = S * S := by rw [hS_mul_rpow0]
      _ = σ := hS_sq
  
  have hHω : ω.IsHermitian := hω.isHermitian
  have hω_self : ω = (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hHω.eigenvectorUnitary)
      (Matrix.diagonal (fun j => (hHω.eigenvalues j : ℂ))) := hHω.spectral_theorem
  have hω_cfc : ∀ f : ℝ → ℝ, cfc f ω = (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hHω.eigenvectorUnitary)
      (Matrix.diagonal (fun j => (f (hHω.eigenvalues j) : ℂ))) := by
    intro f; rw [Matrix.IsHermitian.cfc_eq hHω, Matrix.IsHermitian.cfc]; rfl
  have hω_rpow : ∀ s : ℝ, rpowS ω s = (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hHω.eigenvectorUnitary)
      (Matrix.diagonal (fun j => ((if hHω.eigenvalues j = 0 then 0 else (hHω.eigenvalues j) ^ s : ℝ) : ℂ))) :=
    fun s => hω_cfc _
  have hω_ipow : ∀ u : ℝ, ipowS ω u = (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hHω.eigenvectorUnitary)
      (Matrix.diagonal (fun j =>
        ((if hHω.eigenvalues j = 0 then 0 else Real.cos (u * Real.log (hHω.eigenvalues j)) : ℝ) : ℂ) +
        Complex.I * ((if hHω.eigenvalues j = 0 then 0 else Real.sin (u * Real.log (hHω.eigenvalues j)) : ℝ) : ℂ))) := by
    intro u; unfold ipowS
    rw [hω_cfc, hω_cfc, ← map_smul, ← map_add, ← Matrix.diagonal_smul, ← Matrix.diagonal_add]; rfl
  have hω_ipow_mul_neg : ∀ u : ℝ, ipowS ω u * ipowS ω (-u) = P := by
    intro u; dsimp only [P]
    rw [hω_ipow u, hω_ipow (-u), hω_rpow 0, ← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2; funext j
    by_cases hj : hHω.eigenvalues j = 0
    · simp [hj]
    · simp only [hj, ↓reduceIte, neg_mul, Real.cos_neg, Real.sin_neg, Real.rpow_zero,
        Complex.ofReal_neg, Complex.ofReal_one]
      set c : ℝ := Real.cos (u * Real.log (hHω.eigenvalues j))
      set s : ℝ := Real.sin (u * Real.log (hHω.eigenvalues j))
      calc ((c : ℂ) + Complex.I * (s : ℂ)) * ((c : ℂ) + Complex.I * -(s : ℂ))
          = (c : ℂ) ^ 2 - Complex.I ^ 2 * (s : ℂ) ^ 2 := by ring
        _ = (c : ℂ) ^ 2 + (s : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
        _ = ((c ^ 2 + s ^ 2 : ℝ) : ℂ) := by push_cast; ring
        _ = 1 := by rw [Real.cos_sq_add_sin_sq]; simp
  have hω_comm : ∀ u : ℝ, ipowS ω u * ω = ω * ipowS ω u := by
    intro u
    refine (congrArg₂ (· * ·) (hω_ipow u) hω_self).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· * ·) hω_self (hω_ipow u)).symm
    rw [← map_mul, ← map_mul, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2; funext j; ring
  have hP_ω : P * ω = ω := by
    dsimp only [P]
    refine (congrArg₂ (· * ·) (hω_rpow 0) hω_self).trans ?_
    refine Eq.trans ?_ hω_self.symm
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2; funext j
    by_cases hj : hHω.eigenvalues j = 0 <;> simp [hj, Real.rpow_zero]
  have hω_P : ω * P = ω := by
    dsimp only [P]
    refine (congrArg₂ (· * ·) hω_self (hω_rpow 0)).trans ?_
    refine Eq.trans ?_ hω_self.symm
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2; funext j
    by_cases hj : hHω.eigenvalues j = 0 <;> simp [hj, Real.rpow_zero]
  have hP_sq : P * P = P := by
    dsimp only [P]
    rw [hω_rpow 0, ← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2; funext j
    by_cases hj : hHω.eigenvalues j = 0 <;> simp [hj, Real.rpow_zero]
  have hipow_ω_P : ipowS ω t * P = ipowS ω t := by
    dsimp only [P]
    rw [hω_ipow t, hω_rpow 0, ← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2; funext j
    by_cases hj : hHω.eigenvalues j = 0 <;> simp [hj, Real.rpow_zero]
  have hW_ω_W : W * ω * W = P := by
    dsimp only [W, P]
    refine (congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (hω_rpow (-1 / 2)) hω_self)
      (hω_rpow (-1 / 2))).trans ?_
    refine Eq.trans ?_ (hω_rpow 0).symm
    rw [← map_mul, ← map_mul, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2; funext j
    by_cases hj : hHω.eigenvalues j = 0
    · simp [hj]
    · have hpos : 0 < hHω.eigenvalues j := lt_of_le_of_ne (hω.eigenvalues_nonneg j) (Ne.symm hj)
      simp only [hj, ↓reduceIte, ← Complex.ofReal_mul]
      congr 1
      calc (hHω.eigenvalues j) ^ (-1 / 2 : ℝ) * hHω.eigenvalues j * (hHω.eigenvalues j) ^ (-1 / 2 : ℝ)
          = (hHω.eigenvalues j) ^ (-1 / 2 : ℝ) * (hHω.eigenvalues j) ^ (1 : ℝ) * (hHω.eigenvalues j) ^ (-1 / 2 : ℝ) := by
              rw [Real.rpow_one]
        _ = (hHω.eigenvalues j) ^ ((-1 / 2 : ℝ) + 1 + (-1 / 2)) := by
              rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
        _ = (hHω.eigenvalues j) ^ (0 : ℝ) := by norm_num
  have hω_rot : ipowS ω (-t) * ω * ipowS ω t = ω := by
    have ht : ipowS ω (-t) * ipowS ω t = P := by
      simpa [neg_neg] using hω_ipow_mul_neg (-t)
    rw [hω_comm (-t), Matrix.mul_assoc, ht, hω_P]
  have hW_rot : ipowS ω t * (W * ω * W) * ipowS ω (-t) = P := by
    rw [hW_ω_W, hipow_ω_P, hω_ipow_mul_neg t]
  
  have hL_sum : ∑ i, (L i)ᴴ * L i = P := by
    have hterm : ∀ i : ι, (L i)ᴴ * L i =
        (ipowS ω t * W) * (K i * σ * (K i)ᴴ) * (W * ipowS ω (-t)) := by
      intro i
      rw [hL_adj i]
      dsimp only [L]
      calc (ipowS ω t * W * K i * S * ipowS σ (-t)) * (ipowS σ t * S * (K i)ᴴ * W * ipowS ω (-t))
          = (ipowS ω t * W) * (K i * (S * ipowS σ (-t) * ipowS σ t * S) * (K i)ᴴ) * (W * ipowS ω (-t)) := by
              simp only [Matrix.mul_assoc]
        _ = (ipowS ω t * W) * (K i * σ * (K i)ᴴ) * (W * ipowS ω (-t)) := by
              rw [hS_rot]
    calc ∑ i, (L i)ᴴ * L i
        = ∑ i, (ipowS ω t * W) * (K i * σ * (K i)ᴴ) * (W * ipowS ω (-t)) :=
            Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (ipowS ω t * W) * (∑ i, K i * σ * (K i)ᴴ) * (W * ipowS ω (-t)) := by
            simp only [Matrix.mul_sum, Matrix.sum_mul]
      _ = ipowS ω t * (W * ω * W) * ipowS ω (-t) := by
            change (ipowS ω t * W) * ω * (W * ipowS ω (-t)) = _
            simp only [Matrix.mul_assoc]
      _ = P := hW_rot
  have h_trace : ∀ X : Matrix n n ℂ, (rotatedPetz K σ t X).trace = (P * X).trace := by
    intro X
    rw [h_kraus X]
    unfold kraus
    calc (∑ i, L i * X * (L i)ᴴ).trace
        = ∑ i, ((L i * X) * (L i)ᴴ).trace := Matrix.trace_sum _ _
      _ = ∑ i, ((L i)ᴴ * (L i * X)).trace :=
            Finset.sum_congr rfl (fun i _ => Matrix.trace_mul_comm (L i * X) (L i)ᴴ)
      _ = ∑ i, (((L i)ᴴ * L i) * X).trace :=
            Finset.sum_congr rfl (fun i _ => congrArg Matrix.trace (Matrix.mul_assoc (L i)ᴴ (L i) X).symm)
      _ = ((∑ i, (L i)ᴴ * L i) * X).trace := by
            rw [← Matrix.trace_sum, ← Matrix.sum_mul]
      _ = (P * X).trace := by rw [hL_sum]
  
  let M : ι → Matrix n m ℂ := fun i => (1 - P) * K i * S
  have h1P_conj : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_conj]
  have hM_sum : ∑ i, M i * (M i)ᴴ = 0 := by
    have hM_term : ∀ i : ι, M i * (M i)ᴴ = (1 - P) * (K i * σ * (K i)ᴴ) * (1 - P) := by
      intro i
      dsimp only [M]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS_conj, h1P_conj, ← hS_sq]
      simp only [Matrix.mul_assoc]
    calc ∑ i, M i * (M i)ᴴ
        = ∑ i, (1 - P) * (K i * σ * (K i)ᴴ) * (1 - P) :=
            Finset.sum_congr rfl (fun i _ => hM_term i)
      _ = (1 - P) * ω * (1 - P) := by
            change _ = (1 - P) * (∑ i, K i * σ * (K i)ᴴ) * (1 - P)
            simp only [Matrix.mul_sum, Matrix.sum_mul]
      _ = 0 := by
            rw [Matrix.sub_mul, Matrix.one_mul, hP_ω, sub_self, Matrix.zero_mul]
  have hPKS : ∀ i : ι, P * K i * S = K i * S := by
    intro i
    have htr : ∑ j, (M j * (M j)ᴴ).trace = 0 := by
      rw [← Matrix.trace_sum, hM_sum, Matrix.trace_zero]
    have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ (M j * (M j)ᴴ).trace := by
      intro j _
      exact (Matrix.posSemidef_self_mul_conjTranspose (M j)).trace_nonneg
    have hi : (M i * (M i)ᴴ).trace = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htr i (Finset.mem_univ i)
    have hMi : M i = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hi
    dsimp only [M] at hMi
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, sub_eq_zero] at hMi
    exact hMi.symm
  have h_petz : petz K σ ω = σ := by
    change S * (∑ i, (K i)ᴴ * (W * ω * W) * K i) * S = σ
    rw [hW_ω_W]
    have hterm : ∀ i : ι, S * ((K i)ᴴ * P * K i) * S = S * ((K i)ᴴ * K i) * S := by
      intro i
      calc S * ((K i)ᴴ * P * K i) * S
          = S * ((K i)ᴴ * (Pᴴ * P) * K i) * S := by rw [hP_conj, hP_sq]
        _ = (P * K i * S)ᴴ * (P * K i * S) := by
              simp only [Matrix.conjTranspose_mul, hS_conj, Matrix.mul_assoc]
        _ = (K i * S)ᴴ * (K i * S) := by rw [hPKS i]
        _ = S * ((K i)ᴴ * K i) * S := by
              simp only [Matrix.conjTranspose_mul, hS_conj, Matrix.mul_assoc]
    calc S * (∑ i, (K i)ᴴ * P * K i) * S
        = ∑ i, S * ((K i)ᴴ * P * K i) * S := by simp only [Matrix.mul_sum, Matrix.sum_mul]
      _ = ∑ i, S * ((K i)ᴴ * K i) * S := Finset.sum_congr rfl (fun i _ => hterm i)
      _ = S * (∑ i, (K i)ᴴ * K i) * S := by simp only [Matrix.mul_sum, Matrix.sum_mul]
      _ = S * 1 * S := by rw [hTP]
      _ = σ := by rw [Matrix.mul_one, hS_sq]
  have h_recover : rotatedPetz K σ t ω = σ := by
    change ipowS σ t * petz K σ (ipowS ω (-t) * ω * ipowS ω t) * ipowS σ (-t) = σ
    rw [hω_rot, h_petz, hσ_rot]
  exact ⟨h_recover, h_trace, L, h_kraus⟩

end Leap
