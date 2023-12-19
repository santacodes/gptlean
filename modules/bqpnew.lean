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
structure complex : Type :=
(re : ℝ) (im : ℝ)

variable (Ayes Ano)
def complex.add (a b : complex) : complex :=
⟨a.re + b.re, a.im + b.im⟩

def complex.mul (a b : complex) : complex :=
⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

def complex.conj (a : complex) : complex :=
⟨a.re, -a.im⟩

def complex.norm (a : complex) : complex :=
Real.sqrt(a.re^2 + a.im^2)

def complex.normalize (a : complex) : complex :=
⟨a.re / complex.norm a, a.im / complex.norm a⟩

-- Quantum state is represented by a complex unit vector
structure quantum_state : Type :=
(state : complex)
(norm_eq_one : complex.norm state = ⟨1,0⟩)

-- Quantum gate representing a rotation by angle theta
noncomputable def quantum_gate (θ : ℝ) : complex :=
⟨Real.cos θ , Real.sin θ⟩

-- Hadamard gate
def hadamard_gate : complex :=
complex.normalize ⟨1, 1⟩

-- Quantum circuit application
def apply_gate (gate : complex) (state : complex) : complex :=
complex.mul gate state

-- Quantum circuit composed of two gates
noncomputable def quantum_circuit : complex → complex :=
apply_gate hadamard_gate ∘ apply_gate (quantum_gate (3.14 / 4))


-- Define the promise problem A
structure PromiseProblem :=
  (Ayes Ano : Set string)
  complex.norm (quantum_circuit initial_state).normalize = ⟨1,0⟩ :=

-- Define polynomial-time generated family of quantum circuits
def polynomial_time_generated (Q : QuantumCircuitFamily) : Prop :=
  ∀ (n : ℕ),
    (Q.poly_time n).is_polynomial

-- Define the BQP complexity class
def BQP (a b : ℕ → ℝ) : Prop :=
  ∃ (Q : ℕ → ℕ → List Bool → Bool),
    polynomial_time_generated Q ∧
    ∀ (x : List Bool),
      (x ∈ Ayes → (Pr (Q (List.length x) x) ≥  (List.length x))) ∧
      (x ∈ Ano → (Pr (Q (List.length x) x) ≤  (List.length x)))

-- Define polynomial-time generated family of quantum circuits
structure QuantumCircuitFamily :=
  (Q : ℕ → ℕ → List Bool → Bool)
  (poly_time : ∀ (n : ℕ), ∃ (p : ℕ), ∀ (x : List Bool), p (List.length x) ≤ n)

-- Define probability function Pr
def Pr (b : Bool) : ℝ :=
  if b then 1 else 0


-- Define the BQP complexity class using the QuantumCircuitFamily
def BQP' (a b : ℕ → ℝ) : Prop :=
  ∃ (Q : QuantumCircuitFamily),
    ∀ (x : List Bool),
      (x ∈ Ayes → Pr (Q.Q (List.length x) x) ≥  (List.length x)) ∧
      (x ∈ Ano → Pr (Q.Q (List.length x) x) ≤  (List.length x))

-- The main theorem: Probability amplitude after applying the quantum circuit
theorem quantum_circuit_probability_amplitude (initial_state : complex) :
  complex.norm (quantum_circuit initial_state).normalize = ⟨1,0⟩ := by
  sorry
