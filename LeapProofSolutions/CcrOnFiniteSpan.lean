import LeapProofObligations.Definitions

namespace Leap

/-- Canonical commutation relation on finitely supported number-basis vectors. -/
theorem ccr_on_finite_span : annihilate ∘ₗ create - create ∘ₗ annihilate = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro n
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, Finsupp.lsingle_apply]
  have annihilate_create_single :
      annihilate (create (Finsupp.single n 1)) = Finsupp.single n ((n : ℂ) + 1) := by
    rw [create, Finsupp.linearCombination_single, one_smul,
        annihilate, Finsupp.linearCombination_single, if_neg (Nat.succ_ne_zero n),
        Nat.add_sub_cancel, Finsupp.smul_single']
    congr 1
    push_cast
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  have create_annihilate_single :
      create (annihilate (Finsupp.single n 1)) = Finsupp.single n (n : ℂ) := by
    cases n with
    | zero =>
      simp [annihilate]
    | succ k =>
      rw [annihilate, Finsupp.linearCombination_single, one_smul,
          if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel,
          create, Finsupp.linearCombination_single, Finsupp.smul_single']
      congr 1
      push_cast
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast
      ring
  rw [annihilate_create_single, create_annihilate_single, ← Finsupp.single_sub]
  ring_nf

end Leap
