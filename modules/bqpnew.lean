import Std.Data.Nat.Basic
import Mathlib.Init.Set
import Init.Data.List
import Mathlib.Data.List.Count
import Init.Prelude
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib
import Mathlib.Data.Complex.Exponential
import Std.Data.String
import Mathlib.Data.Polynomial.Basic

namespace complex


structure complex : Type :=
(re : ℝ) (im : ℝ)
noncomputable def magnitude (z : complex) : ℝ :=
Real.sqrt (z.re^2 + z.im^2)

noncomputable def phase (z : complex) : ℝ :=
Real.cos (z.im )

noncomputable def sqrt (z : complex) : complex :=
let r := Real.sqrt (magnitude z);
    let θ := phase z / 2
⟨r * Real.cos θ, r * Real.sin θ⟩


-- Example usage
-- def example_complex : complex := ⟨3, 4⟩
--def example_sqrt : complex := complex.sqrt example_complex

variable (Ayes Ano)
def complex.add (a b : complex) : complex :=
⟨a.re + b.re, a.im + b.im⟩

def complex.mul (a b : complex) : complex :=
⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

def complex.conj (a : complex) : complex :=
⟨a.re, -a.im⟩

def complex.norm (a : complex) : complex :=
⟨a.re,a.im⟩

noncomputable def complex.normalize (a : complex) : complex :=
let w := complex.norm a;
⟨a.re / w.re, a.im / w.re⟩

-- Quantum state is represented by a complex unit vector
structure quantum_state : Type :=
(state : complex)
(norm_eq_one : complex.norm state = ⟨1,0⟩)

-- Quantum gate representing a rotation by angle theta
noncomputable def quantum_gate (θ : ℝ) : complex :=
⟨Real.cos θ , Real.sin θ⟩

-- Hadamard gate
noncomputable def hadamard_gate : complex :=
complex.normalize ⟨1, 1⟩

-- Quantum circuit application
def apply_gate (gate : complex) (state : complex) : complex :=
complex.mul gate state

-- Quantum circuit composed of two gates
noncomputable def quantum_circuit : complex → complex :=
apply_gate hadamard_gate ∘ apply_gate (quantum_gate (3.14 / 4))

-- Define polynomial-time generated family of quantum circuits
structure QuantumCircuitFamily :=
  (Q : ℕ → ℕ → List Bool → Bool)
  (poly_time : ∀ (n : ℕ), ∃ (p : ℕ), ∀ (x : List Bool), (List.length x) ≤ n)


def is_polynomial (p : polynomial ) : Prop :=
  if p == 0 then
     true
    else false

-- Define polynomial-time generated family of quantum circuits
def polynomial_time_generated (Q : QuantumCircuitFamily) : Prop :=
  ∀ (n : ℕ),
    (Q.poly_time n).is_a_polynomial

-- Define probability function Pr
def Pr (b : Bool) : ℝ :=
  if b then 1 else 0

-- Define the BQP complexity class
def BQP (a b : ℕ → ℝ) : Prop :=
  ∃ (Q : ℕ → ℕ → List Bool → Bool),
    (polynomial_time_generated Q) ^
    ∀ (x : List Bool),
      (x ∈ Ayes → (Pr (Q (List.length x) x) ≥  (List.length x))) ∧
      (x ∈ Ano → (Pr (Q (List.length x) x) ≤  (List.length x)))

  (poly_time : ∀ (n : ℕ), ∃ (p : ℕ), ∀ (x : List Bool), (List.length x) ≤ n)



-- Define the BQP complexity class using the QuantumCircuitFamily
def BQP' (a b : ℕ → ℝ) : Prop :=
  ∃ (Q : QuantumCircuitFamily),
    ∀ (x : List Bool),
      (x ∈ Ayes → Pr (Q.Q (List.length x) x) ≥  (List.length x)) ∧
      (x ∈ Ano → Pr (Q.Q (List.length x) x) ≤  (List.length x))
-- The main theorem: Probability amplitude after applying the quantum circuit
theorem quantum_circuit_probability_amplitude (initial_state : complex) :
  complex.norm (quantum_circuit initial_state).normalize = ⟨1,0⟩ := by
  -- sorry
    -- Define the initial quantum state
  let initial_state : complex := ⟨1, 0⟩

  #eval "Initial State: " ++ repr initial_state
  #eval "Hadamard Result: " ++ repr hadamard_result

end complex
