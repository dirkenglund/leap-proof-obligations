import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Leap
open Set

/-- At one operating point, x is angular frequency and z is the magnitude of
the extracted port transimpedance. n and d encode its squared magnitude as
n/d. They may come from a full-order small-signal pencil at that corner's bias.
The positive expansion of 2 n(x) d(0) − n(0) d(x) covers the entire prefix. -/
structure TiaCornerCertificate (z n d : ℝ → ℝ) (gLo gHi lo hi : ℝ) where
  dc_nonneg : 0 ≤ z 0
  denom_pos : ∀ x ∈ Icc 0 hi, 0 < d x
  port_identity : ∀ x ∈ Icc 0 hi, z x ^ 2 * d x = n x
  continuous_power : ContinuousOn (fun x => z x ^ 2) (Icc 0 hi)
  dc_lower : gLo ^ 2 * d 0 ≤ n 0
  dc_upper : n 0 ≤ gHi ^ 2 * d 0
  count : ℕ
  coeff : Fin count → ℝ
  leftDeg : Fin count → ℕ
  rightDeg : Fin count → ℕ
  coeff_nonneg : ∀ i, 0 ≤ coeff i
  margin : ℝ
  margin_pos : 0 < margin
  pass_identity : ∀ x ∈ Icc 0 lo, 2 * n x * d 0 - n 0 * d x =
    margin + ∑ i, coeff i * x ^ leftDeg i * (lo - x) ^ rightDeg i
  stop_test : 2 * n hi * d 0 ≤ n 0 * d hi

/-- Each index denotes one transistor selector and any admitted operating
variables. All fields of its certificate concern the same loaded circuit.
The index type can enumerate discrete selectors or include a continuous box. -/
theorem tia_transistor_corner_gain_bandwidth {C : Type*} [Nonempty C]
    (z n d : C → ℝ → ℝ) (gLo gHi lo hi : ℝ)
    (hg : 0 < gLo) (hgg : gLo ≤ gHi) (hl : 0 < lo) (hh : lo < hi)
    (cert : ∀ c, TiaCornerCertificate (z c) (n c) (d c) gLo gHi lo hi) :
    ∀ c, z c 0 ∈ Icc gLo gHi ∧ ∃ w ∈ Ioc lo hi,
      IsLeast {u : ℝ | 0 ≤ u ∧ z c u ^ 2 = z c 0 ^ 2 / 2} w := by
  sorry

end Leap
