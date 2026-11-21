import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A finite feed-forward mesh of lossless, phase-matched MZI+crossing cells.
Angles are in radians. The input crossing is ideal. The two centered phase
settings of the internal arms are +t and -t, with t = θ/2. Fixed common phases
and external phase shifters are included in the complex path weights.
See Hamerly, Bandyopadhyay and Englund, Nat. Commun. (2022), Fig. 5. -/
namespace Leap
namespace SandiaMzi
noncomputable section
open Real

/-- Response rows of two splitter-angle errors to the same fabrication vector.
The two residuals are the values for this realization. -/
structure Cell (I : Type*) where
  a : I → ℝ
  b : I → ℝ
  rA : ℝ
  rB : ℝ
  halfPhase : ℝ

def angle {I : Type*} [Fintype I] (row z : I → ℝ) (r : ℝ) : ℝ :=
  (∑ k, row k * z k) + r

/-- With sign +1 this bounds α+β. With sign -1 it bounds α−β.
The residual budget bounds the corresponding signed residual combination. -/
def budget {I : Type*} [Fintype I] (c : Cell I) (radius : I → ℝ)
    (sign residualBudget : ℝ) : ℝ :=
  (∑ k, |c.a k + sign * c.b k| * radius k) + residualBudget

inductive Port where | p00 | p11 | p01 | p10

/-- Entries of B(π/4+β) diag(exp(it),exp(-it)) B(π/4+α) X, where
B(u) has diagonal cos(u) and off-diagonal i sin(u). Rows denote outputs.
p and m are the sum and difference of the splitter errors. -/
def entry (port : Port) (t p m : ℝ) : ℂ :=
  match port with
  | .p00 => ⟨-(sin t * sin m), cos t * cos p⟩
  | .p11 => ⟨sin t * sin m, cos t * cos p⟩
  | .p01 => ⟨-(cos t * sin p), sin t * cos m⟩
  | .p10 => ⟨-(cos t * sin p), -(sin t * cos m)⟩

def atCell {I : Type*} [Fintype I] (c : Cell I) (z : I → ℝ) (port : Port) : ℂ :=
  let α := angle c.a z c.rA
  let β := angle c.b z c.rB
  entry port c.halfPhase (α + β) (α - β)

/-- Paths with the same endpoints are summed coherently. Each visit specifies
the physical cell and its input/output ports. The weight includes fixed phases. -/
structure Path (C : Type*) where
  visits : List (C × Port)
  weight : ℂ

def pathBudget {C : Type*} (e : C → ℝ) (p : Path C) : ℝ :=
  ‖p.weight‖ * (p.visits.map (fun v => e v.1)).sum

def amplitude {C : Type*} (f : C → Port → ℂ) (paths : List (Path C)) : ℂ :=
  (paths.map (fun p => p.weight * (p.visits.map (fun v => f v.1 v.2)).prod)).sum

/-- (Triangle column, adjacent wire pair). Wire k couples to wire k+1.
The input-to-output schedule is one orientation of the Reck triangle. -/
abbrev Gate := ℕ × ℕ

def reck : ℕ → List Gate
  | 0 => []
  | n+1 => reck n ++ (List.range n).reverse.map (fun k => (n,k))

def Port.secondInput : Port → Bool
  | .p00 | .p10 => false
  | .p01 | .p11 => true

/-- Update the two affected wires. Each row is a coherent sum. -/
def scatter {X : Type*} (visit : Gate → Port → X → X) (add : X → X → X)
    (g : Gate) (v : ℕ → X) (j : ℕ) : X :=
  if j = g.2 then add (visit g .p00 (v g.2)) (visit g .p01 (v (g.2+1)))
  else if j = g.2+1 then add (visit g .p10 (v g.2)) (visit g .p11 (v (g.2+1)))
  else v j

/-- A unit launch on one wire. The diagonal input phase screen is fixed. -/
def launch (screen : ℕ → ℂ) (input wire : ℕ) : ℂ :=
  if wire = input then screen wire else 0

/-- Direct propagation of a column of the transfer matrix. The two fixed
complex multipliers per cell input can encode the external phase shifter,
the removed common phase, and their input-port convention. -/
def transfer (f : Gate → Port → ℂ) (phase : Gate → Bool → ℂ)
    (schedule : List Gate) (v : ℕ → ℂ) : ℕ → ℂ :=
  schedule.foldl (fun a g => scatter (fun k p x => f k p * (phase k p.secondInput * x))
    (· + ·) g a) v

def extendPaths (phase : Gate → Bool → ℂ) (g : Gate) (p : Port) :
    List (Path Gate) → List (Path Gate) :=
  List.map (fun path => ⟨(g,p) :: path.visits, phase g p.secondInput * path.weight⟩)

/-- Enumerate the routes implied by the wiring and one input, storing visits
in output-to-input order. Bypassed wires keep their incoming paths. -/
def routes (phase : Gate → Bool → ℂ) (schedule : List Gate)
    (paths : ℕ → List (Path Gate)) : ℕ → List (Path Gate) :=
  schedule.foldl (fun a g => scatter (extendPaths phase) (· ++ ·) g a) paths

def launchPaths (screen : ℕ → ℂ) (input wire : ℕ) : List (Path Gate) :=
  if wire = input then [⟨[], screen wire⟩] else []

/-- Squared Frobenius norm divided by the mode count. -/
def normalizedSquare (n : ℕ) (a : Fin n → Fin n → ℝ) : ℝ :=
  (∑ i, ∑ o, a i o ^ 2) / (n : ℝ)

end
end SandiaMzi
open SandiaMzi Real

/-- For a programmed N-mode Reck triangle, bound the dark-port leakage of a
crossed cell, every transfer-matrix entry, and normalized squared matrix error
for one common fabrication realization. The external phases are fixed. -/
theorem sandia_correlated_mzi_mesh {I : Type*} [Fintype I] (n : ℕ) (hn : 0 < n)
    (cells : Gate → Cell I) (z radius : I → ℝ) (resPlus resMinus : Gate → ℝ)
    (screen : ℕ → ℂ) (phase : Gate → Bool → ℂ)
    (hz : ∀ k, |z k| ≤ radius k)
    (hp : ∀ c, |(cells c).rA + (cells c).rB| ≤ resPlus c)
    (hm : ∀ c, |(cells c).rA - (cells c).rB| ≤ resMinus c) :
    let P := fun c => budget (cells c) radius 1 (resPlus c)
    let M := fun c => budget (cells c) radius (-1) (resMinus c)
    let cost := fun c => |cos (cells c).halfPhase| * P c + |sin (cells c).halfPhase| * M c
    let actual := fun c => atCell (cells c) z
    let nominal := fun c port => entry port (cells c).halfPhase 0 0
    let error := fun (i o : Fin n) =>
      ‖transfer actual phase (reck n) (launch screen i) o -
        transfer nominal phase (reck n) (launch screen i) o‖
    let bound := fun (i o : Fin n) =>
      ((routes phase (reck n) (launchPaths screen i) o).map (pathBudget cost)).sum
    (∀ c, (cells c).halfPhase = π/2 →
      ‖atCell (cells c) z .p00‖ ^ 2 ≤ (M c) ^ 2) ∧
    (∀ i o : Fin n, error i o ≤ bound i o) ∧
    normalizedSquare n error ≤ normalizedSquare n bound := by
  sorry

end Leap
