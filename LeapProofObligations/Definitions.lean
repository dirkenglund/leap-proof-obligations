import Mathlib

/-!
Shared definitions for the proof obligations in this repository.

This file contains no `sorry`. Every obligation lives in its own module
and ends in a single `sorry`.
-/

open Complex Complex.HadamardThreeLines MeasureTheory
open scoped Real Matrix BigOperators ComplexOrder MatrixOrder
open Filter Topology Matrix TensorProduct

namespace Leap

/-! ## Typicality (Wilde, *Quantum Information Theory*, 2nd ed., §15.2) -/

/-- Number of occurrences of letter `a` in a word `x`. -/
def count {α : Type*} [DecidableEq α] {k : ℕ} (x : Fin k → α) (a : α) : ℕ :=
  (Finset.univ.filter fun i => x i = a).card

/-- Number of positions where `(x i, y i) = (a, b)`. -/
def pairCount {α β : Type*} [DecidableEq α] [DecidableEq β] {k : ℕ}
    (x : Fin k → α) (y : Fin k → β) (a : α) (b : β) : ℕ :=
  (Finset.univ.filter fun i => x i = a ∧ y i = b).card

/-- Strongly δ-typical words of length `k` for the distribution `p`. -/
noncomputable def strongTypical {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (δ : ℝ) (k : ℕ) : Finset (Fin k → α) :=
  Finset.univ.filter fun x => ∀ a, |(count x a : ℝ) / k - p a| ≤ δ ∧ (p a = 0 → count x a = 0)

/-- i.i.d. probability of a set of words. -/
def iidProb {α : Type*} [Fintype α] (p : α → ℝ) {k : ℕ} (S : Finset (Fin k → α)) : ℝ :=
  ∑ x ∈ S, ∏ i, p (x i)

/-- Conditionally strongly δ-typical output words given input word `x`, channel `W`. -/
noncomputable def condTypical {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (W : α → β → ℝ) (δ : ℝ) {k : ℕ} (x : Fin k → α) : Finset (Fin k → β) :=
  Finset.univ.filter fun y => ∀ a b,
    |(pairCount x y a b : ℝ) / k - W a b * (count x a : ℝ) / k| ≤ δ ∧
      (W a b = 0 → pairCount x y a b = 0)

/-- Probability of a set of output words given input word `x` through memoryless `W`. -/
def condProb {α β : Type*} [Fintype β] (W : α → β → ℝ) {k : ℕ}
    (x : Fin k → α) (S : Finset (Fin k → β)) : ℝ :=
  ∑ y ∈ S, ∏ i, W (x i) (y i)

/-- Shannon entropy in nats (`Real.log 0 = 0` gives `0 log 0 = 0`). -/
noncomputable def entropy {β : Type*} [Fintype β] (q : β → ℝ) : ℝ :=
  -∑ b, q b * Real.log (q b)

/-! ## Channels and recovery maps (Wilde §§4, 9, 11, 12, 13, 20) -/

/-- Kraus-form map `X ↦ ∑ Kᵢ X Kᵢ†`. -/
def kraus {m n ι : Type*} [Fintype m] [Fintype ι] (K : ι → Matrix n m ℂ) (X : Matrix m m ℂ) :
    Matrix n n ℂ :=
  ∑ i, K i * X * (K i)ᴴ

/-- Heisenberg-picture adjoint `Y ↦ ∑ Kᵢ† Y Kᵢ`. -/
def krausAdj {m n ι : Type*} [Fintype n] [Fintype ι] (K : ι → Matrix n m ℂ) (Y : Matrix n n ℂ) :
    Matrix m m ℂ :=
  ∑ i, (K i)ᴴ * Y * K i

/-- Real power on the support (0 on the kernel, Wilde's convention), by the CFC. -/
noncomputable def rpowS {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (s : ℝ) :
    Matrix n n ℂ :=
  cfc (fun x : ℝ => if x = 0 then 0 else x ^ s) A

/-- Imaginary power `A^{it}` on the support (0 on the kernel). -/
noncomputable def ipowS {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (t : ℝ) :
    Matrix n n ℂ :=
  (cfc (fun x : ℝ => if x = 0 then 0 else Real.cos (t * Real.log x)) A) +
    Complex.I • cfc (fun x : ℝ => if x = 0 then 0 else Real.sin (t * Real.log x)) A

/-- Petz recovery map `R_{σ,N}` (Wilde Def 12.3.1). -/
noncomputable def petz {m n ι : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype ι] (K : ι → Matrix n m ℂ) (σ : Matrix m m ℂ) (X : Matrix n n ℂ) : Matrix m m ℂ :=
  rpowS σ (1 / 2) *
    krausAdj K (rpowS (kraus K σ) (-1 / 2) * X * rpowS (kraus K σ) (-1 / 2)) * rpowS σ (1 / 2)

/-- Rotated Petz map `R^t = U_{σ,t} ∘ R_{σ,N} ∘ U_{N(σ),-t}` (Wilde Def 12.3.2). -/
noncomputable def rotatedPetz {m n ι : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Fintype ι]
    (K : ι → Matrix n m ℂ) (σ : Matrix m m ℂ) (t : ℝ) (X : Matrix n n ℂ) : Matrix m m ℂ :=
  ipowS σ t * petz K σ (ipowS (kraus K σ) (-t) * X * ipowS (kraus K σ) t) * ipowS σ (-t)

/-- Ampliation `id_k ⊗ Φ` on block matrices indexed by `k × m`. -/
def ampliate {m n : Type*} (k : Type*) (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (X : Matrix (k × m) (k × m) ℂ) : Matrix (k × n) (k × n) ℂ :=
  fun p q => Φ (fun a b => X (p.1, a) (q.1, b)) p.2 q.2

/-- Complete positivity, concretely. -/
def IsCP {m n : Type*} [Fintype m] [Fintype n] (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin k × m) (Fin k × m) ℂ),
    X.PosSemidef → (ampliate (Fin k) Φ X).PosSemidef

/-- Choi matrix `∑_{a,b} |a⟩⟨b| ⊗ Φ(|a⟩⟨b|)`. -/
def choi {m n : Type*} [DecidableEq m] (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- Erasure channel on `n` levels; output `Option n`, `none` = erasure flag. -/
def erasure {n : Type*} [Fintype n] (ε : ℝ) (X : Matrix n n ℂ) : Matrix (Option n) (Option n) ℂ :=
  fun i j => match i, j with
    | some a, some b => ((1 - ε : ℝ) : ℂ) * X a b
    | none, none => ((ε : ℝ) : ℂ) * X.trace
    | _, _ => 0

/-- Post-processing that erases the data block with probability `η`, keeping the flag. -/
def reErase {n : Type*} [Fintype n] (η : ℝ) (Y : Matrix (Option n) (Option n) ℂ) :
    Matrix (Option n) (Option n) ℂ :=
  fun i j => match i, j with
    | some a, some b => ((1 - η : ℝ) : ℂ) * Y (some a) (some b)
    | none, none => ((η : ℝ) : ℂ) * (∑ a, Y (some a) (some a)) + Y none none
    | _, _ => 0

/-- Reduced state of a vector `ψ` on `n × r`. -/
def reduced {n r : Type*} [Fintype r] (ψ : n × r → ℂ) : Matrix n n ℂ :=
  fun a b => ∑ k, ψ (a, k) * star (ψ (b, k))

/-- Entanglement fidelity computed from the full output `(N ⊗ id)(|ψ⟩⟨ψ|)`. -/
noncomputable def entFid {n r ι : Type*} [Fintype n] [Fintype r] [Fintype ι]
    (K : ι → Matrix n n ℂ) (ψ : n × r → ℂ) : ℝ :=
  let v : ι → n × r → ℂ := fun i p => ∑ b, K i p.1 b * ψ (b, p.2)
  (∑ i, ‖∑ p, star (ψ p) * v i p‖ ^ 2)

/-- Trace norm `‖A‖₁ = Tr √(A†A)`. -/
noncomputable def traceNorm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  (cfc Real.sqrt (Aᴴ * A)).trace.re

/-- Von Neumann entropy (nats). -/
noncomputable def vnEntropy {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) : ℝ :=
  -(ρ * cfc Real.log ρ).trace.re

/-- Umegaki relative entropy `Tr ρ (log ρ − log σ)`. -/
noncomputable def relEnt {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : ℝ :=
  (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace.re

/-- Partial trace over the right factor. -/
def ptraceRight {m n : Type*} [Fintype n] (X : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  fun i j => ∑ k, X (i, k) (j, k)

/-! ## Hirschman / Stein–Hirschman kernels (Wilde §12.2) -/

/-- Wilde's kernel α_θ(t) = sin(πθ) / (2(1−θ)(cosh(πt) − cos(πθ))). -/
noncomputable def hirschmanAlpha (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * (1 - θ) * (Real.cosh (π * t) - Real.cos (π * θ)))

/-- Wilde's kernel β_θ(t) = sin(πθ) / (2θ(cosh(πt) + cos(πθ))). -/
noncomputable def hirschmanBeta (θ t : ℝ) : ℝ :=
  Real.sin (π * θ) / (2 * θ * (Real.cosh (π * t) + Real.cos (π * θ)))

section Schatten
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

theorem isSymmetric_adjoint_comp_self (T : H →L[ℂ] K) :
    (ContinuousLinearMap.adjoint T ∘L T : H →ₗ[ℂ] H).IsSymmetric := by
  intro x y
  simp [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

/-- Singular values of `T`: square roots of the eigenvalues of `T†T`. -/
noncomputable def singularValues (T : H →L[ℂ] K) : Fin (Module.finrank ℂ H) → ℝ :=
  fun i => Real.sqrt ((isSymmetric_adjoint_comp_self T).eigenvalues rfl i)

/-- Schatten `p`-norm `(∑ sᵢ^p)^{1/p}`. -/
noncomputable def schattenNorm (p : ℝ) (T : H →L[ℂ] K) : ℝ :=
  (∑ i, singularValues T i ^ p) ^ (1 / p)

end Schatten

/-! ## CHSH (Wilde Ex. 3.6.4) -/

noncomputable def phiPlus : Fin 2 × Fin 2 → ℂ :=
  fun p => if p.1 = p.2 then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0

/-- A projective two-outcome strategy: for each question, two orthogonal projectors summing to 1. -/
structure ProjStrategy where
  P : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  herm : ∀ x a, (P x a).IsHermitian
  idem : ∀ x a, P x a * P x a = P x a
  complete : ∀ x, P x 0 + P x 1 = 1

/-- Winning probability of the CHSH game (uniform questions, win iff a ⊕ b = x ∧ y) on |Φ⁺⟩. -/
noncomputable def chshWin (SA SB : ProjStrategy) : ℝ :=
  (1 / 4 : ℝ) * ∑ x : Fin 2, ∑ y : Fin 2, ∑ a : Fin 2, ∑ b : Fin 2,
    if a + b = x * y then
      (star phiPlus ⬝ᵥ (Matrix.kroneckerMap (· * ·) (SA.P x a) (SB.P y b)) *ᵥ phiPlus).re
    else 0

/-! ## Transpose trick (Wilde Ex. 3.7.12 / 3.7.11) -/

noncomputable def maxEnt (d : ℕ) : EuclideanSpace ℂ (Fin d) ⊗[ℂ] EuclideanSpace ℂ (Fin d) :=
  ∑ i, EuclideanSpace.single i (1 : ℂ) ⊗ₜ EuclideanSpace.single i (1 : ℂ)

/-! ## Canonical commutation relations -/

/-- Annihilation operator on finitely supported number-basis vectors: a|n⟩ = √n |n−1⟩. -/
noncomputable def annihilate : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun n =>
    if n = 0 then 0 else Finsupp.single (n - 1) ((Real.sqrt n : ℝ) : ℂ)

/-- Creation operator: a†|n⟩ = √(n+1) |n+1⟩. -/
noncomputable def create : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun n =>
    Finsupp.single (n + 1) ((Real.sqrt (n + 1) : ℝ) : ℂ)

end Leap
