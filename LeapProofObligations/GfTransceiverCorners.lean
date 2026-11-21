import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Leap
open Set

/-- Each scalar stage has a squared small-signal response. Its pass and stop
bounds are relative to its own DC value at the SAME corner as the other stages. -/
structure GfStageBudget (p : ℝ → ℝ) (lo hi dcLo dcHi pass stop : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  dc_positive : 0 < p 0
  dc : p 0 ∈ Icc dcLo dcHi
  passband : ∀ x ∈ Icc 0 lo, pass * p 0 ≤ p x
  stopband : p hi ≤ stop * p 0

/-- End-to-end DC squared gain and first half-power bandwidth for a matched
unidirectional scalar lane. The effective channel includes the coherent
mixing factor. The receive stage includes detection and readout. -/
theorem gf_transceiver_corner_gain_bandwidth {C : Type*} [Nonempty C]
    (tx path rx link : C → ℝ → ℝ) (lo hi : ℝ)
    (tL tU tP tS cL cU cP cS rL rU rP rS : ℝ)
    (hl : 0 < lo) (hh : lo < hi)
    (hne : 0 ≤ tL ∧ 0 ≤ cL ∧ 0 ≤ rL)
    (hpass : 0 ≤ tP ∧ 0 ≤ cP ∧ 0 ≤ rP)
    (pm : 1 / 2 < tP * cP * rP) (sm : tS * cS * rS ≤ 1 / 2)
    (ht : ∀ c, GfStageBudget (tx c) lo hi tL tU tP tS)
    (hc : ∀ c, GfStageBudget (path c) lo hi cL cU cP cS)
    (hr : ∀ c, GfStageBudget (rx c) lo hi rL rU rP rS)
    (cascade : ∀ c, ∀ x ∈ Icc 0 hi, link c x = tx c x * path c x * rx c x)
    (cont : ∀ c, ContinuousOn (link c) (Icc 0 hi)) :
    ∀ c, link c 0 ∈ Icc (tL * cL * rL) (tU * cU * rU) ∧
      ∃ w ∈ Ioc lo hi, IsLeast {u : ℝ | 0 ≤ u ∧ link c u = link c 0 / 2} w := by
  sorry

end Leap
