-- Import Lean's standard library for mathematical reasoning
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib
import Mathlib.Data.Complex.Exponential



open Real
structure complex : Type :=
(re : ℝ) (im : ℝ)

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

-- The main theorem: Probability amplitude after applying the quantum circuit
theorem quantum_circuit_probability_amplitude (initial_state : complex) :
  complex.norm (quantum_circuit initial_state).normalize = ⟨1,0⟩ :=
-- Proof here
begin
  unfold quantum_circuit
  simp only [apply_gate, hadamard_gate, quantum_gate, complex.mul, complex.normalize],
end
