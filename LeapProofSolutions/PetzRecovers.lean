import LeapProofObligations.Definitions

open scoped Matrix BigOperators ComplexOrder

namespace Leap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Wilde Def 12.3.1, book form for singular σ: Petz recovers σ exactly and is
trace-preserving on the support of `N(σ)` (`rpowS _ 0` is the support projector). -/
theorem petz_recovers {ι : Type*} [Fintype ι] (K : ι → Matrix n m ℂ)
    (hTP : ∑ i, (K i)ᴴ * K i = 1) (σ : Matrix m m ℂ) (hσ : σ.PosSemidef) :
    petz K σ (kraus K σ) = σ ∧
      ∀ X : Matrix n n ℂ, (petz K σ X).trace = (rpowS (kraus K σ) 0 * X).trace := by
  let _ : PartialOrder (Matrix m m ℂ) := Matrix.instPartialOrder
  let _ : PartialOrder (Matrix n n ℂ) := Matrix.instPartialOrder
  have _ : IsOrderedAddMonoid (Matrix n n ℂ) := Matrix.instIsOrderedAddMonoid
  have _ : NonnegSpectrumClass ℝ (Matrix m m ℂ) := Matrix.instNonnegSpectrumClass
  have _ : NonnegSpectrumClass ℝ (Matrix n n ℂ) := Matrix.instNonnegSpectrumClass
  let S : Matrix m m ℂ := rpowS σ (1 / 2)
  let τ : Matrix n n ℂ := kraus K σ
  let T : Matrix n n ℂ := rpowS τ (-1 / 2)
  let P : Matrix n n ℂ := rpowS τ 0
  have hτ : τ.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun i _ => hσ.mul_mul_conjTranspose_same (K i))
  have hS_herm : Sᴴ = S := by
    have hsa : IsSelfAdjoint S := by
      dsimp [S]
      unfold rpowS
      exact IsSelfAdjoint.cfc
    simpa only [Matrix.star_eq_conjTranspose] using hsa.star_eq
  have hP_herm : Pᴴ = P := by
    have hsa : IsSelfAdjoint P := by
      dsimp [P]
      unfold rpowS
      exact IsSelfAdjoint.cfc
    simpa only [Matrix.star_eq_conjTranspose] using hsa.star_eq
  have hS_sq : S * S = σ := by
    have hσ_sa : IsSelfAdjoint σ := hσ.isHermitian.isSelfAdjoint
    have hσ_spec : ∀ x ∈ spectrum ℝ σ, 0 ≤ x :=
      spectrum_nonneg_of_nonneg hσ.nonneg
    let f : ℝ → ℝ := fun x => if x = 0 then 0 else x ^ (1 / 2 : ℝ)
    have hf_cont : ContinuousOn f (spectrum ℝ σ) :=
      (Set.toFinite (spectrum ℝ σ)).continuousOn f
    change cfc f σ * cfc f σ = σ
    rw [← cfc_mul f f σ hf_cont hf_cont]
    have h_eq : Set.EqOn (fun x => f x * f x) (fun x => x) (spectrum ℝ σ) := by
      intro x hx
      have hx_nonneg : 0 ≤ x := hσ_spec x hx
      by_cases hx0 : x = 0
      · simp [f, hx0]
      · have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
        simp only [f, hx0, ↓reduceIte]
        have h12 : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
        rw [← Real.rpow_add hx_pos, h12, Real.rpow_one]
    rw [cfc_congr h_eq]
    exact cfc_id' ℝ σ hσ_sa
  have hτ_sa : IsSelfAdjoint τ := hτ.isHermitian.isSelfAdjoint
  have hT_mul : T * τ * T = P := by
    have hτ_spec : ∀ x ∈ spectrum ℝ τ, 0 ≤ x :=
      spectrum_nonneg_of_nonneg hτ.nonneg
    let g : ℝ → ℝ := fun x => if x = 0 then 0 else x ^ (-1 / 2 : ℝ)
    let p₀ : ℝ → ℝ := fun x => if x = 0 then 0 else x ^ (0 : ℝ)
    have hg_cont : ContinuousOn g (spectrum ℝ τ) :=
      (Set.toFinite (spectrum ℝ τ)).continuousOn g
    have hid_cont : ContinuousOn (fun x : ℝ => x) (spectrum ℝ τ) :=
      (Set.toFinite (spectrum ℝ τ)).continuousOn _
    have hgz_cont : ContinuousOn (fun x : ℝ => g x * x) (spectrum ℝ τ) :=
      (Set.toFinite (spectrum ℝ τ)).continuousOn _
    have h_id : cfc (fun x : ℝ => x) τ = τ := cfc_id' ℝ τ hτ_sa
    change cfc g τ * τ * cfc g τ = cfc p₀ τ
    calc
      cfc g τ * τ * cfc g τ
          = cfc g τ * cfc (fun x : ℝ => x) τ * cfc g τ := by rw [h_id]
      _ = cfc (fun x : ℝ => g x * x) τ * cfc g τ := by
            rw [← cfc_mul g (fun x : ℝ => x) τ hg_cont hid_cont]
      _ = cfc (fun x : ℝ => g x * x * g x) τ := by
            rw [← cfc_mul (fun x : ℝ => g x * x) g τ hgz_cont hg_cont]
      _ = cfc p₀ τ := by
            apply cfc_congr
            intro x hx
            have hx_nonneg : 0 ≤ x := hτ_spec x hx
            by_cases hx0 : x = 0
            · simp [g, p₀, hx0]
            · have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
              simp only [g, p₀, hx0, ↓reduceIte]
              calc
                x ^ (-1 / 2 : ℝ) * x * x ^ (-1 / 2 : ℝ)
                    = x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) * x ^ (-1 / 2 : ℝ) := by rw [Real.rpow_one]
                _ = x ^ ((-1 / 2 : ℝ) + 1 + (-1 / 2 : ℝ)) := by
                      rw [← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos]
                _ = x ^ (0 : ℝ) := by
                      have hexp : (-1 / 2 : ℝ) + 1 + (-1 / 2 : ℝ) = 0 := by norm_num
                      rw [hexp]
  let B : ι → Matrix n m ℂ := fun j => K j * S
  have hτ_gram : ∑ j, B j * (B j)ᴴ = τ := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [B]
    calc
      (K j * S) * (K j * S)ᴴ
          = (K j * S) * (S * (K j)ᴴ) := by rw [Matrix.conjTranspose_mul, hS_herm]
      _ = K j * (S * (S * (K j)ᴴ)) := by rw [Matrix.mul_assoc]
      _ = K j * ((S * S) * (K j)ᴴ) := by rw [← Matrix.mul_assoc S S (K j)ᴴ]
      _ = K j * (σ * (K j)ᴴ) := by rw [hS_sq]
      _ = K j * σ * (K j)ᴴ := by rw [← Matrix.mul_assoc]
  let Q : Matrix n n ℂ := 1 - P
  have hQ_herm : Qᴴ = Q := by
    dsimp [Q]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_herm]
  have hQ_mul_τ : Q * τ = 0 := by
    let p₀ : ℝ → ℝ := fun x => if x = 0 then 0 else x ^ (0 : ℝ)
    have h1_cont : ContinuousOn (1 : ℝ → ℝ) (spectrum ℝ τ) :=
      (Set.toFinite (spectrum ℝ τ)).continuousOn _
    have hp0_cont : ContinuousOn p₀ (spectrum ℝ τ) :=
      (Set.toFinite (spectrum ℝ τ)).continuousOn _
    have hsub_cont : ContinuousOn (fun x : ℝ => (1 : ℝ → ℝ) x - p₀ x) (spectrum ℝ τ) :=
      (Set.toFinite (spectrum ℝ τ)).continuousOn _
    have hid_cont : ContinuousOn (fun x : ℝ => x) (spectrum ℝ τ) :=
      (Set.toFinite (spectrum ℝ τ)).continuousOn _
    have h_one : cfc (1 : ℝ → ℝ) τ = 1 := cfc_one ℝ τ hτ_sa
    have h_id : cfc (fun x : ℝ => x) τ = τ := cfc_id' ℝ τ hτ_sa
    have h_fn : (fun x : ℝ => ((1 : ℝ → ℝ) x - p₀ x) * x) = (fun _ : ℝ => 0) := by
      ext x
      by_cases hx0 : x = 0
      · simp [p₀, hx0]
      · simp [p₀, hx0, Real.rpow_zero]
    change (1 - cfc p₀ τ) * τ = 0
    calc
      (1 - cfc p₀ τ) * τ
          = (cfc (1 : ℝ → ℝ) τ - cfc p₀ τ) * cfc (fun x : ℝ => x) τ := by
              rw [h_one, h_id]
      _ = cfc (fun x : ℝ => (1 : ℝ → ℝ) x - p₀ x) τ * cfc (fun x : ℝ => x) τ := by
            rw [← cfc_sub (1 : ℝ → ℝ) p₀ τ h1_cont hp0_cont]
      _ = cfc (fun x : ℝ => ((1 : ℝ → ℝ) x - p₀ x) * x) τ := by
            rw [← cfc_mul (fun x : ℝ => (1 : ℝ → ℝ) x - p₀ x) (fun x : ℝ => x) τ hsub_cont hid_cont]
      _ = cfc (fun _ : ℝ => 0) τ := by rw [h_fn]
      _ = 0 := cfc_const_zero ℝ τ
  let C : ι → Matrix n m ℂ := fun j => Q * B j
  have hC_sum : ∑ j, C j * (C j)ᴴ = 0 := by
    have h_term : ∀ j : ι, C j * (C j)ᴴ = Q * (B j * (B j)ᴴ) * Q := by
      intro j
      dsimp [C]
      calc
        (Q * B j) * (Q * B j)ᴴ
            = (Q * B j) * ((B j)ᴴ * Q) := by rw [Matrix.conjTranspose_mul, hQ_herm]
        _ = Q * (B j * ((B j)ᴴ * Q)) := by rw [Matrix.mul_assoc]
        _ = Q * (B j * (B j)ᴴ * Q) := by rw [← Matrix.mul_assoc (B j) (B j)ᴴ Q]
        _ = Q * (B j * (B j)ᴴ) * Q := by rw [← Matrix.mul_assoc]
    calc
      ∑ j, C j * (C j)ᴴ
          = ∑ j, Q * (B j * (B j)ᴴ) * Q := by
              apply Finset.sum_congr rfl
              intro j _
              exact h_term j
      _ = (∑ j, Q * (B j * (B j)ᴴ)) * Q := by rw [← Matrix.sum_mul]
      _ = (Q * ∑ j, B j * (B j)ᴴ) * Q := by rw [← Matrix.mul_sum]
      _ = (Q * τ) * Q := by rw [hτ_gram]
      _ = 0 * Q := by rw [hQ_mul_τ]
      _ = 0 := zero_mul Q
  have h_abs : ∀ i : ι, P * (K i * S) = K i * S := by
    have hC_nonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ C j * (C j)ᴴ := by
      intro j _
      exact Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_self_mul_conjTranspose (C j))
    have hC_all_zero : ∀ j ∈ (Finset.univ : Finset ι), C j * (C j)ᴴ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hC_nonneg).mp hC_sum
    intro i
    have hCi_sq : C i * (C i)ᴴ = 0 := hC_all_zero i (Finset.mem_univ i)
    have hCi : C i = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp hCi_sq
    dsimp [C, Q, B] at hCi
    rw [Matrix.sub_mul, Matrix.one_mul] at hCi
    exact (sub_eq_zero.mp hCi).symm
  have h_conj1 : petz K σ (kraus K σ) = σ := by
    change S * krausAdj K (T * τ * T) * S = σ
    rw [hT_mul]
    unfold krausAdj
    calc
      S * (∑ i, (K i)ᴴ * P * K i) * S
          = (∑ i, S * ((K i)ᴴ * P * K i)) * S := by rw [Matrix.mul_sum]
      _ = ∑ i, S * ((K i)ᴴ * P * K i) * S := by rw [Matrix.sum_mul]
      _ = ∑ i, S * ((K i)ᴴ * K i) * S := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              S * ((K i)ᴴ * P * K i) * S
                  = S * (((K i)ᴴ * P * K i) * S) := by rw [Matrix.mul_assoc]
              _ = S * ((K i)ᴴ * P * (K i * S)) := by rw [Matrix.mul_assoc ((K i)ᴴ * P) (K i) S]
              _ = S * ((K i)ᴴ * (P * (K i * S))) := by rw [Matrix.mul_assoc (K i)ᴴ P (K i * S)]
              _ = S * ((K i)ᴴ * (K i * S)) := by rw [h_abs i]
              _ = S * ((K i)ᴴ * K i * S) := by rw [← Matrix.mul_assoc (K i)ᴴ (K i) S]
              _ = S * ((K i)ᴴ * K i) * S := by rw [← Matrix.mul_assoc]
      _ = (∑ i, S * ((K i)ᴴ * K i)) * S := by rw [← Matrix.sum_mul]
      _ = S * (∑ i, (K i)ᴴ * K i) * S := by rw [← Matrix.mul_sum]
      _ = S * 1 * S := by rw [hTP]
      _ = S * S := by rw [mul_one]
      _ = σ := hS_sq
  have h_conj2 : ∀ X : Matrix n n ℂ, (petz K σ X).trace = (rpowS (kraus K σ) 0 * X).trace := by
    intro X
    let Y : Matrix n n ℂ := T * X * T
    change (S * krausAdj K Y * S).trace = (P * X).trace
    calc
      (S * krausAdj K Y * S).trace
          = (S * (S * krausAdj K Y)).trace := Matrix.trace_mul_comm (S * krausAdj K Y) S
      _ = ((S * S) * krausAdj K Y).trace := by rw [← Matrix.mul_assoc]
      _ = (krausAdj K Y * (S * S)).trace := Matrix.trace_mul_comm (S * S) (krausAdj K Y)
      _ = (krausAdj K Y * σ).trace := by rw [hS_sq]
      _ = ((∑ i, (K i)ᴴ * Y * K i) * σ).trace := rfl
      _ = (∑ i, (K i)ᴴ * Y * K i * σ).trace := by rw [Matrix.sum_mul]
      _ = ∑ i, ((K i)ᴴ * Y * K i * σ).trace := Matrix.trace_sum Finset.univ _
      _ = ∑ i, (K i * σ * (K i)ᴴ * Y).trace := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              ((K i)ᴴ * Y * K i * σ).trace
                  = (((K i)ᴴ * Y) * (K i * σ)).trace := by rw [Matrix.mul_assoc ((K i)ᴴ * Y) (K i) σ]
              _ = ((K i * σ) * ((K i)ᴴ * Y)).trace := Matrix.trace_mul_comm ((K i)ᴴ * Y) (K i * σ)
              _ = (K i * σ * (K i)ᴴ * Y).trace := by rw [← Matrix.mul_assoc (K i * σ) (K i)ᴴ Y]
      _ = (∑ i, K i * σ * (K i)ᴴ * Y).trace := (Matrix.trace_sum Finset.univ _).symm
      _ = ((∑ i, K i * σ * (K i)ᴴ) * Y).trace := by rw [← Matrix.sum_mul]
      _ = (τ * (T * X * T)).trace := rfl
      _ = ((τ * T * X) * T).trace := by
            have h_assoc : τ * (T * X * T) = (τ * T * X) * T := by
              rw [← Matrix.mul_assoc τ (T * X) T, ← Matrix.mul_assoc τ T X]
            rw [h_assoc]
      _ = (T * (τ * T * X)).trace := Matrix.trace_mul_comm (τ * T * X) T
      _ = ((T * τ * T) * X).trace := by
            have h_assoc2 : T * (τ * T * X) = (T * τ * T) * X := by
              rw [← Matrix.mul_assoc T (τ * T) X, ← Matrix.mul_assoc T τ T]
            rw [h_assoc2]
      _ = (P * X).trace := by rw [hT_mul]
  exact ⟨h_conj1, h_conj2⟩

end Leap
