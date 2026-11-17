# Lean 4 proof obligations

Open Lean 4 formalization obligations from Wilde, *Quantum Information Theory* (2nd ed.),
together with related tasks in analysis, atomic, molecular and optical physics, and
quantum programming logic.

Each obligation is a theorem stated over **public Mathlib**
[`56a005855ea17e0b0958f73ec801ae140b0a1679`](https://github.com/leanprover-community/mathlib4/commit/56a005855ea17e0b0958f73ec801ae140b0a1679)
on **Lean v4.35.0**. The statements are written to type-check with `sorry`.
**None is proved.** The statements have been type-checked but have **not** been
independently peer-reviewed. Lean's junk values apply at edge cases (for example
`Real.log 0 = 0`, which only weakens the inequalities that use it).

This repository is maintained by Dirk Englund (MIT Quantum Photonics).

## Success criteria

A proof of a target theorem is accepted when all of the following hold, in a
clean checkout of the pinned commit:

1. `lake build` passes.
2. The target statement, and every definition it depends on in this repository,
   is byte-identical to the specification in this commit (no weakening, no
   change of hypotheses or conclusion).
3. `#print axioms <target>` lists only `propext`, `Classical.choice`, and
   `Quot.sound`. No new `axiom`, no remaining `sorry`, and no
   `native_decide` / `implemented_by` escapes.
4. Grading is re-run in a separate clean sandbox; agent-produced logs are not
   trusted.

## How to build

```bash
elan toolchain install leanprover/lean4:v4.35.0
lake exe cache get
lake build
```

The project is a standard Lake package. Shared definitions (with no `sorry`)
live in [`LeapProofObligations/Definitions.lean`](LeapProofObligations/Definitions.lean).
Each obligation is a separately named theorem in its own file, ending in exactly
one `sorry`.

## SorryDB

The layout is meant to be compatible with [SorryDB](https://github.com/SorryDB/SorryDB),
which indexes `Prop`-valued `sorry`s in public Lean 4 repositories so that
proof agents can pick them up. A machine-readable list of the obligations in
this repository is in [`sorry-index.json`](sorry-index.json), using the field
names from SorryDB's [database format](https://github.com/SorryDB/SorryDB/blob/master/doc/DATABASE.md)
(`repo`, `location`, theorem name). Pretty-printed Lean goals are left for a
full `lake build` plus the Lean REPL, which is how SorryDB itself extracts them.

SorryDB crawls repositories listed on [Reservoir](https://reservoir.lean-lang.org/),
the Lean package registry, not arbitrary GitHub URLs. To have this repository
indexed by SorryDB:

1. Keep the repository **public**, with a GitHub-detected OSI-approved license
   (this repository uses the MIT License) and a root `lake-manifest.json`.
2. Give the repository **at least two GitHub stars** (Reservoir's quality filter).
   Reservoir then typically indexes packages within about a day.
3. Once the package appears on Reservoir, SorryDB's nightly crawler can pick up
   its `Prop`-valued `sorry`s (`lake build` must succeed at the crawled commit).
4. If the package meets Reservoir's
   [inclusion criteria](https://reservoir.lean-lang.org/inclusion-criteria)
   but does not appear after a few days, report it on Reservoir's issue tracker.

Until that crawl happens, agents can already use `sorry-index.json` and the
per-theorem files directly.

## Proof obligations

Every item below is **open**: stated with `sorry`, not proved. The Lean name is
the theorem in the `Leap` namespace. The informal goal is the intended
mathematical claim. The gap notes what is missing and, where the source gives
one, a proof idea or a book result that depends on the claim.

### From Wilde, *Quantum Information Theory* (2nd ed.)

#### 1. Strong typicality concentrates

- **Lean name:** `Leap.strongTypical_prob_tendsto_one`
- **File:** [`LeapProofObligations/StrongTypicalProbTendstoOne.lean`](LeapProofObligations/StrongTypicalProbTendstoOne.lean)
- **Reference:** Wilde Def 15.2.3
- **Goal:** For a distribution `p` on a finite alphabet and `δ > 0`, the i.i.d.
  probability of the strongly `δ`-typical words of length `k` tends to 1.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Weak law of large numbers per letter. Used in the book by
  Prop 15.2.4–15.2.5, Ex 15.2.2, Ex 20.3.3, and the HSW code-pruning chain (Ch 20).
  Difficulty: medium.

#### 2. Petz recovery map, book form for singular `σ`

- **Lean name:** `Leap.petz_recovers`
- **File:** [`LeapProofObligations/PetzRecovers.lean`](LeapProofObligations/PetzRecovers.lean)
- **Reference:** Wilde Def 12.3.1
- **Goal:** For a Kraus channel `N` and PSD `σ`: `R_{σ,N}(N(σ)) = σ`, and
  `Tr R_{σ,N}(X) = Tr(Π_{supp N(σ)} X)`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** `N†(1 − Π_{N(σ)}) ≥ 0` has zero trace against `σ`, so it
  kills `supp σ`. Hence `σ^{1/2} N†(Π) σ^{1/2} = σ`, and the trace on the
  support is `Tr(Π X)`. Used in the book by Prop 12.3.1, Cor 12.5.1, Thm 12.1.1,
  Cor 12.6.1–12.6.5. Difficulty: medium.

#### 3. Rotated Petz maps

- **Lean name:** `Leap.rotatedPetz_props`
- **File:** [`LeapProofObligations/RotatedPetzProps.lean`](LeapProofObligations/RotatedPetzProps.lean)
- **Reference:** Wilde Def 12.3.2
- **Goal:** For every `t`, `R^t_{σ,N}` recovers `σ`, is trace-preserving on the
  support, and has a Kraus form.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Uses the unrotated recovery (item 2). The unitaries commute
  with their own base state, and the Kraus operators are
  `L_i = σ^{it} σ^{1/2} K_i† N(σ)^{−1/2} N(σ)^{−it}`. Used in the book by the
  Ch 12 recoverability chain and Ex 12.3.1. Difficulty: medium–hard.

#### 4. Choi's theorem and Kraus form

- **Lean name:** `Leap.choi_theorem`
- **File:** [`LeapProofObligations/ChoiTheorem.lean`](LeapProofObligations/ChoiTheorem.lean)
- **Reference:** Wilde Ex 4.4.1 / Thm 4.4.1
- **Goal:** A linear map on matrices is completely positive iff its Choi matrix
  is PSD iff it has a Kraus form with `|m|·|n|` operators.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Choi's theorem with `|m|·|n|` Kraus operators (padding by 0).
  Used in the book by Ex 13.4.3, Ex 13.5.4, Prop 13.5.1, Thm 13.6.1,
  Prop 21.6.1–21.6.2. Difficulty: medium.

#### 5. Uniform conditional typicality

- **Lean name:** `Leap.condTypical_prob`
- **File:** [`LeapProofObligations/CondTypicalProb.lean`](LeapProofObligations/CondTypicalProb.lean)
- **Reference:** Wilde Def 15.2.4 / Prop 15.2.5
- **Goal:** For a memoryless channel `W` and `δ, ε > 0` there is `K` such that
  for all `k ≥ K` and every input word `x`, `Pr[Y ∈ T_δ(x) | x] ≥ 1 − ε`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Chebyshev; the variance of `N(a,b) − N(a)W(a,b)` is at most
  `k/4`, so the bound is uniform in `x`. Used in the book by Ex 15.2.2, Ex 20.3.3,
  and the Ch 20 max-error code construction. Difficulty: medium.

#### 6. The erasure channel is degradable for `ε ≤ 1/2`

- **Lean name:** `Leap.erasure_degradable`
- **File:** [`LeapProofObligations/ErasureDegradable.lean`](LeapProofObligations/ErasureDegradable.lean)
- **Reference:** Wilde Ex 13.5.2
- **Goal:** `E_{1−ε} = (re-erasure with η = (1−2ε)/(1−ε)) ∘ E_ε`, with `η ∈ [0,1]`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** `η = (1−2ε)/(1−ε) ∈ [0,1]`; the data coefficient is
  `(1−η)(1−ε) = ε`, and the flag coefficient is `η(1−ε) + ε = 1−ε`. Used in the
  book by Ex 13.5.4 and the erasure (anti)degradability results in Ch 24.
  Difficulty: easy.

#### 7. Entanglement fidelity does not depend on the purification

- **Lean name:** `Leap.entFid_eq`
- **File:** [`LeapProofObligations/EntFidEq.lean`](LeapProofObligations/EntFidEq.lean)
- **Reference:** Wilde Def / Thm 9.5.1
- **Goal:** `F_e(ρ, N) = Σ_i |Tr(K_i ρ)|^2` for any purification `ψ` of `ρ`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Trace cyclicity. Used in the book by Ex 9.5.1–9.5.3,
  Thm 24.3.1, Ex 24.2.1. Difficulty: easy.

#### 8. Minimum output entropy is attained on pure inputs

- **Lean name:** `Leap.minOutputEntropy_pure`
- **File:** [`LeapProofObligations/MinOutputEntropyPure.lean`](LeapProofObligations/MinOutputEntropyPure.lean)
- **Reference:** Wilde Def 20.4.1 / Ex 20.4.2
- **Goal:** For every input state `ρ` there is a unit vector `v` with
  `H(N(|v⟩⟨v|)) ≤ H(N(ρ))`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Spectral decomposition plus concavity of entropy. Used in
  the book by Thm 20.4.3, Ex 20.4.3–20.4.4, Ex 20.5.1. Difficulty: medium.

#### 9. Kraus form of the erasure channel

- **Lean name:** `Leap.erasure_kraus`
- **File:** [`LeapProofObligations/ErasureKraus.lean`](LeapProofObligations/ErasureKraus.lean)
- **Reference:** Wilde Ex 4.7.9
- **Goal:** For `0 ≤ ε ≤ 1` there are `|n|+1` Kraus operators with `Σ K†K = 1`
  realizing `E_ε`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** `K_none = √(1−ε)·embed`, `K_a = √ε |e⟩⟨a|`. Used in the book
  by Ex 5.2.6, Ex 13.5.2, Ex 13.5.4, and the Ch 24 erasure results.
  Difficulty: easy.

#### 10. Hirschman's strip inequality, both kernels

- **Lean name:** `Leap.hirschman_strip`
- **File:** [`LeapProofObligations/HirschmanStrip.lean`](LeapProofObligations/HirschmanStrip.lean)
- **Reference:** Wilde Thm 12.2.2 (Hirschman 1952)
- **Goal:** For bounded holomorphic `f` on the strip,
  `log|f(θ)| ≤ ∫ [α_θ(t) log|f(it)|^{1−θ} + β_θ(t) log|f(1+it)|^θ] dt`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** This is the general two-kernel form. It is the analytic
  input to operator Stein–Hirschman (item 11) and, in the book, to Thm 12.5.1
  and Cor 12.5.1, Cor 12.6.1–12.6.5 (those applications use a special case;
  the general theorem stated here is open). Difficulty: hard (about 2–4 weeks).

#### 11. Operator Stein–Hirschman interpolation, general exponents

- **Lean name:** `Leap.stein_hirschman`
- **File:** [`LeapProofObligations/SteinHirschman.lean`](LeapProofObligations/SteinHirschman.lean)
- **Reference:** Wilde Thm 12.2.3
- **Goal:** The Stein–Hirschman interpolation inequality for a holomorphic
  family of operators, in general Schatten exponents `p₀, p₁`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Given Hirschman's strip inequality (item 10) and Schatten
  Hölder (item 12). Used in the book by the same recoverability results as
  item 10. Difficulty: hard.

#### 12. Schatten Hölder / duality

- **Lean name:** `Leap.schatten_holder`
- **File:** [`LeapProofObligations/SchattenHolder.lean`](LeapProofObligations/SchattenHolder.lean)
- **Reference:** used by Wilde Thm 12.2.3
- **Goal:** `|tr(T X)| ≤ ‖T‖_p ‖X‖_q` for conjugate `p, q`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** SVD / polar decomposition plus the von Neumann trace
  inequality. Feeds item 11. Difficulty: medium–hard (about 1–3 weeks).

#### 13. Trace distance ignores an untouched factor

- **Lean name:** `Leap.traceNorm_kron_state`
- **File:** [`LeapProofObligations/TraceNormKronState.lean`](LeapProofObligations/TraceNormKronState.lean)
- **Reference:** Wilde Def 9.1.3
- **Goal:** `‖A ⊗ ω‖_1 = ‖A‖_1` for every density matrix `ω`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** `‖A ⊗ ω‖_1 = ‖A‖_1 ‖ω‖_1`. Used in the book by Thm 9.1.1,
  Ex 9.1.12–9.1.13, Ex 24.1.1, Ex 24.9.1. Difficulty: easy–medium.

#### 14. Size of the conditionally typical set

- **Lean name:** `Leap.condTypical_card_le`
- **File:** [`LeapProofObligations/CondTypicalCardLe.lean`](LeapProofObligations/CondTypicalCardLe.lean)
- **Reference:** Wilde Prop 15.2.7
- **Goal:** There is `c` with `|T_δ(x)| ≤ exp(k(H(Y|X)_{type(x)} + c δ))` for
  all `k`, `x` and `δ > 0`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Every `y` in `T` has probability at least
  `exp(−k(H + cδ))` with `c = Σ_{W>0} −log W(a,b)`, and the probabilities sum
  to at most 1. Used in the book by Ex 20.3.3 and the Ch 20 code-pruning chain.
  Difficulty: easy–medium.

#### 15. Monotonicity of quantum relative entropy under partial trace

- **Lean name:** `Leap.relEnt_ptrace_le`
- **File:** [`LeapProofObligations/RelEntPtraceLe.lean`](LeapProofObligations/RelEntPtraceLe.lean)
- **Reference:** Wilde Thm 11.9.2
- **Goal:** `D(Tr_B ρ ‖ Tr_B σ) ≤ D(ρ ‖ σ)` for positive definite `ρ, σ`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Lindblad–Uhlmann; holds for positive definite inputs
  without normalization. Needs Lieb concavity. Used in the book by Thm 11.9.1,
  Ex 11.9.1, Thm 11.10.4, and as the input to the Holevo bound (item 18).
  Difficulty: very hard.

#### 16. Classical Pinsker inequality

- **Lean name:** `Leap.pinsker`
- **File:** [`LeapProofObligations/Pinsker.lean`](LeapProofObligations/Pinsker.lean)
- **Reference:** Wilde Thm / Lemma 10.8.1
- **Goal:** `(Σ |p − q|)^2 / 2 ≤ D(p ‖ q)` in nats.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Classical Pinsker in nats. Used in the book by Thm 11.9.1,
  Thm 11.10.4, and the conditional and mutual-information Pinsker bounds.
  Difficulty: medium.

#### 17. Golden–Thompson inequality

- **Lean name:** `Leap.golden_thompson`
- **File:** [`LeapProofObligations/GoldenThompson.lean`](LeapProofObligations/GoldenThompson.lean)
- **Reference:** premise of Wilde Lemma 17.3.3
- **Goal:** `Tr e^{A+B} ≤ Tr e^A e^B` for Hermitian `A, B`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** The Golden–Thompson inequality. Used in the book by the
  operator Chernoff bound and the covering lemma (Ch 17). Difficulty: hard.

#### 18. Holevo bound for a finite-outcome measurement

- **Lean name:** `Leap.holevo_bound`
- **File:** [`LeapProofObligations/HolevoBound.lean`](LeapProofObligations/HolevoBound.lean)
- **Reference:** Wilde Ex 11.9.2 / Thm 11.6.1
- **Goal:** `I(X; Y) ≤ H(Σ p_x ρ_x) − Σ p_x H(ρ_x)`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Follows from monotonicity of relative entropy under
  partial trace (item 15). Used in the book by Ex 11.9.2 (accessible
  information). Difficulty: hard, after item 15.

#### 19. Transpose trick on a genuine tensor product

- **Lean name:** `Leap.transpose_trick`
- **File:** [`LeapProofObligations/TransposeTrick.lean`](LeapProofObligations/TransposeTrick.lean)
- **Reference:** Wilde Ex 3.7.12 / 3.7.11
- **Goal:** `(A ⊗ I)|Γ⟩ = (I ⊗ A^T)|Γ⟩`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** A short identity on the maximally entangled vector; a
  follow-on (same exercise family) is to prove that the `d²` Heisenberg–Weyl
  Bell vectors `(X^x Z^z ⊗ 1)|Φ⟩/√d` form an orthonormal basis (Ex 3.7.11).
  Difficulty: easy.

#### 20. CHSH game: achievability

- **Lean name:** `Leap.chsh_achieves`
- **File:** [`LeapProofObligations/ChshAchieves.lean`](LeapProofObligations/ChshAchieves.lean)
- **Reference:** Wilde Ex 3.6.4
- **Goal:** Some projective strategy on `|Φ⁺⟩` wins with probability `cos²(π/8)`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Exhibit an explicit qubit strategy. Difficulty: easy.

#### 21. CHSH game: qubit Tsirelson bound

- **Lean name:** `Leap.chsh_tsirelson`
- **File:** [`LeapProofObligations/ChshTsirelson.lean`](LeapProofObligations/ChshTsirelson.lean)
- **Reference:** Wilde Ex 3.6.4
- **Goal:** No projective strategy on `|Φ⁺⟩` does better than `cos²(π/8)`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** The qubit Tsirelson bound in this form. An extension
  (not stated here) would allow arbitrary dimension and an arbitrary shared
  state. Difficulty: easy–medium.

### Related obligations

#### 22. Wielandt–Wintner: no bounded representation of `[Q, P] = iħ`

- **Lean name:** `Leap.wielandt`
- **File:** [`LeapProofObligations/Wielandt.lean`](LeapProofObligations/Wielandt.lean)
- **Goal:** No two elements of a nontrivial normed `ℂ`-algebra satisfy
  `[a, b] = 1`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** A standard boundedness obstruction for the canonical
  commutation relation. Warm-up for the oscillator / CCR development below.
  Difficulty: easy–medium.

#### 23. Canonical commutation on the finite-span number basis

- **Lean name:** `Leap.ccr_on_finite_span`
- **File:** [`LeapProofObligations/CcrOnFiniteSpan.lean`](LeapProofObligations/CcrOnFiniteSpan.lean)
- **Goal:** `a ∘ a† − a† ∘ a = id` on finitely supported number-basis vectors,
  with `a|n⟩ = √n |n−1⟩` and `a†|n⟩ = √(n+1) |n+1⟩`.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Direct computation on basis vectors. Larger (unstated)
  follow-on work, from a standard AMO treatment of the quantum harmonic
  oscillator, is to realize `a` and `a†` as densely defined operators on
  `ℓ²(ℕ)`, prove `a† ⊆ adjoint a`, closability, that `N = a†a` is essentially
  self-adjoint with spectrum `ℕ`, and the coherent-state / displacement
  identities. Difficulty: this lemma is easy; the unbounded-operator
  development is hard.

#### 24. Hermitian 2×2 matrices are not a Löwner lattice

- **Lean name:** `Leap.loewner_not_lattice`
- **File:** [`LeapProofObligations/LoewnerNotLattice.lean`](LeapProofObligations/LoewnerNotLattice.lean)
- **Reference:** facts used in [arXiv:2611.09822](https://arxiv.org/abs/2611.09822), App. A
- **Goal:** There exist Hermitian 2×2 matrices with no Hermitian least upper
  bound in the Löwner order.
- **Status:** Open (`sorry`).
- **Gap / sketch:** A standard counter-example in 2×2 Hermitian matrices.
  Difficulty: easy.

#### 25. Increasing chains of effects have a Löwner supremum

- **Lean name:** `Leap.loewner_chain_sup`
- **File:** [`LeapProofObligations/LoewnerChainSup.lean`](LeapProofObligations/LoewnerChainSup.lean)
- **Reference:** [arXiv:2611.09822](https://arxiv.org/abs/2611.09822), App. A
- **Goal:** An increasing chain of effects `0 ≤ f_k ≤ 1` has a Löwner
  supremum, which is again an effect.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Monotone bounded convergence of Hermitian matrices. A
  follow-on (not stated here) is an `OmegaCompletePartialOrder` instance on
  the set of effects. Difficulty: medium.

#### 26. Countability of a finite-variable integer store

- **Lean name:** `Leap.store_countable`
- **File:** [`LeapProofObligations/StoreCountable.lean`](LeapProofObligations/StoreCountable.lean)
- **Reference:** [arXiv:2611.09822](https://arxiv.org/abs/2611.09822), App. A
- **Goal:** If `Var` is finite, then `Var → ℤ` is countable.
- **Status:** Open (`sorry`).
- **Gap / sketch:** Finite product of countable sets. Difficulty: trivial.

### Broader public-ready tasks (no compiled statement in this repository yet)

These are in-scope formalization tasks that do not yet have a single compiled
`sorry` theorem in this repository.

- **Strip-interpolation analysis layer for Mathlib.** Infrastructure behind
  items 10–11: strip harmonic measure / Poisson kernel, the strip↔disc
  conformal map, a log-subharmonic majorant, and boundary log-integrability.
  Success: Mathlib-quality contributions plus a proof of item 10. Difficulty:
  hard, about 2–5 weeks.

- **Expectation / weakest-precondition duality for a small quantum while
  language** (claims in [arXiv:2611.09822](https://arxiv.org/abs/2611.09822)).
  Define a syntax (skip, unitary, measurement with Kraus operators
  `Σ M†M ≤ 1`, sequencing, if, while), a denotation on sub-normalized
  classical-quantum states (loops as ω-suprema, using item 25), and the
  weakest precondition. Prove `expect (⟦c⟧ ρ) Ψ = expect ρ (wp c Ψ)`,
  soundness, and that `wp` is the weakest precondition. Difficulty: hard,
  about 2–4 weeks.

- **End-to-end formalization of a published quantum-networking paper.**
  Every displayed rate and fidelity formula as a theorem, with a ledger of
  proved / not-formalizable rows. Difficulty: medium, about 1–2 weeks per
  paper.

## License

MIT License. See [LICENSE](LICENSE).
