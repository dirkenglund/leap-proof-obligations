import LeapProofObligations.Definitions

open scoped MatrixOrder

namespace Leap

/-- An increasing chain of effects `0 ≤ fₖ ≤ 1` has a Löwner supremum. -/
theorem loewner_chain_sup {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℕ → Matrix n n ℂ) (hf : Monotone f) (h0 : ∀ k, 0 ≤ f k) (h1 : ∀ k, f k ≤ 1) :
    ∃ S, IsLUB (Set.range f) S ∧ 0 ≤ S ∧ S ≤ 1 := by
  have hq_le : ∀ {A B : Matrix n n ℂ}, A ≤ B → ∀ v : n → ℂ,
      (star v ⬝ᵥ A.mulVec v).re ≤ (star v ⬝ᵥ B.mulVec v).re := by
    intro A B hAB v
    have hpos := Matrix.PosSemidef.re_dotProduct_nonneg (Matrix.le_iff.mp hAB) v
    rw [RCLike.re_to_complex, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at hpos
    linarith
  let q : (n → ℂ) → ℕ → ℝ := fun v k => (star v ⬝ᵥ (f k).mulVec v).re
  let c : (n → ℂ) → ℂ := fun v => ((⨆ k, q v k : ℝ) : ℂ)
  have hc : ∀ v : n → ℂ,
      Filter.Tendsto (fun k => star v ⬝ᵥ (f k).mulVec v) Filter.atTop (nhds (c v)) := by
    intro v
    have hmono : Monotone (q v) := fun j k hjk => hq_le (hf hjk) v
    have hbdd : BddAbove (Set.range (q v)) := by
      refine ⟨(star v ⬝ᵥ (1 : Matrix n n ℂ).mulVec v).re, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact hq_le (h1 k) v
    have hreal : Filter.Tendsto (q v) Filter.atTop (nhds (⨆ k, q v k)) :=
      tendsto_atTop_ciSup hmono hbdd
    have hcomp : Filter.Tendsto (fun k => ((q v k : ℝ) : ℂ)) Filter.atTop (nhds (c v)) :=
      (Complex.continuous_ofReal.tendsto _).comp hreal
    refine hcomp.congr fun k => ?_
    have hHerm : (f k).IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (h0 k)).1
    have him : (star v ⬝ᵥ (f k).mulVec v).im = 0 := by
      simpa only [RCLike.im_to_complex] using hHerm.im_star_dotProduct_mulVec_self v
    have hre := Complex.re_add_im (star v ⬝ᵥ (f k).mulVec v)
    rw [him, Complex.ofReal_zero, zero_mul, add_zero] at hre
    exact hre
  have hpol : ∀ (M : Matrix n n ℂ) (i j : n),
      (1 / 4 : ℂ) *
        ((star (Pi.single i 1 + Pi.single j 1) ⬝ᵥ M.mulVec (Pi.single i 1 + Pi.single j 1) -
          star (Pi.single i 1 - Pi.single j 1) ⬝ᵥ M.mulVec (Pi.single i 1 - Pi.single j 1)) -
         Complex.I *
          (star (Pi.single i 1 + Complex.I • Pi.single j 1) ⬝ᵥ
             M.mulVec (Pi.single i 1 + Complex.I • Pi.single j 1) -
           star (Pi.single i 1 - Complex.I • Pi.single j 1) ⬝ᵥ
             M.mulVec (Pi.single i 1 - Complex.I • Pi.single j 1))) = M i j := by
    intro M i j
    have hdiff : ∀ u w : n → ℂ,
        star (u + w) ⬝ᵥ M.mulVec (u + w) - star (u - w) ⬝ᵥ M.mulVec (u - w) =
          2 * (star u ⬝ᵥ M.mulVec w) + 2 * (star w ⬝ᵥ M.mulVec u) := by
      intro u w
      simp only [star_add, star_sub, Matrix.mulVec_add, Matrix.mulVec_sub,
        add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
      ring
    let u : n → ℂ := Pi.single i 1
    let w : n → ℂ := Pi.single j 1
    have h1_diff := hdiff u w
    have h2_diff := hdiff u (Complex.I • w)
    have hIw_r : star u ⬝ᵥ M.mulVec (Complex.I • w) = Complex.I * (star u ⬝ᵥ M.mulVec w) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    have hIw_l : star (Complex.I • w) ⬝ᵥ M.mulVec u = -Complex.I * (star w ⬝ᵥ M.mulVec u) := by
      rw [star_smul, Complex.star_def, Complex.conj_I, smul_dotProduct, smul_eq_mul]
    have heval : star u ⬝ᵥ M.mulVec w = M i j := by
      change star (Pi.single i (1 : ℂ)) ⬝ᵥ M.mulVec (Pi.single j 1) = M i j
      rw [← Pi.single_star, star_one, Matrix.mulVec_single_one, single_dotProduct,
        one_mul, Matrix.col_apply]
    change (1 / 4 : ℂ) *
      ((star (u + w) ⬝ᵥ M.mulVec (u + w) - star (u - w) ⬝ᵥ M.mulVec (u - w)) -
       Complex.I *
        (star (u + Complex.I • w) ⬝ᵥ M.mulVec (u + Complex.I • w) -
         star (u - Complex.I • w) ⬝ᵥ M.mulVec (u - Complex.I • w))) = M i j
    rw [h1_diff, h2_diff, hIw_r, hIw_l, heval]
    calc (1 / 4 : ℂ) * ((2 * M i j + 2 * (star w ⬝ᵥ M.mulVec u)) -
           Complex.I * (2 * (Complex.I * M i j) + 2 * (-Complex.I * (star w ⬝ᵥ M.mulVec u))))
        = (1 / 4 : ℂ) * ((2 - 2 * (Complex.I * Complex.I)) * M i j +
           (2 + 2 * (Complex.I * Complex.I)) * (star w ⬝ᵥ M.mulVec u)) := by ring
      _ = M i j := by rw [Complex.I_mul_I]; ring
  let e : n → n → ℂ := fun i => Pi.single i 1
  let S : Matrix n n ℂ := Matrix.of fun i j =>
    (1 / 4 : ℂ) *
      ((c (e i + e j) - c (e i - e j)) -
       Complex.I * (c (e i + Complex.I • e j) - c (e i - Complex.I • e j)))
  have hS_entry : ∀ i j : n, Filter.Tendsto (fun k => f k i j) Filter.atTop (nhds (S i j)) := by
    intro i j
    have ht : Filter.Tendsto (fun k =>
        (1 / 4 : ℂ) *
          ((star (e i + e j) ⬝ᵥ (f k).mulVec (e i + e j) -
            star (e i - e j) ⬝ᵥ (f k).mulVec (e i - e j)) -
           Complex.I *
            (star (e i + Complex.I • e j) ⬝ᵥ (f k).mulVec (e i + Complex.I • e j) -
             star (e i - Complex.I • e j) ⬝ᵥ (f k).mulVec (e i - Complex.I • e j))))
        Filter.atTop (nhds (S i j)) := by
      simp only [S, Matrix.of_apply]
      exact (((hc (e i + e j)).sub (hc (e i - e j))).sub
        (((hc (e i + Complex.I • e j)).sub (hc (e i - Complex.I • e j))).const_mul
          Complex.I)).const_mul (1 / 4 : ℂ)
    exact ht.congr fun k => hpol (f k) i j
  have h_pi : Filter.Tendsto (fun k i j => f k i j) Filter.atTop (nhds fun i j => S i j) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hS_entry i j
  have h_cont : Continuous (Matrix.of : (n → n → ℂ) → Matrix n n ℂ) :=
    continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)
  have hS_tendsto : Filter.Tendsto f Filter.atTop (nhds S) :=
    (h_cont.tendsto (fun i j => S i j)).comp h_pi
  have hLUB : IsLUB (Set.range f) S := isLUB_of_tendsto_atTop hf hS_tendsto
  refine ⟨S, hLUB, (h0 0).trans (hLUB.1 ⟨0, rfl⟩), hLUB.2 ?_⟩
  rintro _ ⟨k, rfl⟩
  exact h1 k

end Leap
