import Std.Data.Nat.Basic
import Mathlib.Init.Set
import Init.Data.List
import Mathlib.Data.List.Count
variable (Ayes Ano)
-- Define the promise problem A
structure PromiseProblem :=
  (Ayes Ano : Set string)
-- Define polynomial-time generated family of quantum circuits
def polynomial_time_generated (Q : QuantumCircuitFamily) : Prop :=
  ∀ (n : ℕ),
    (Q.poly_time n).is_polynomial

-- Define the BQP complexity class
def BQP (a b : ℕ → ℝ) : Prop :=
  ∃ (Q : ℕ → ℕ → List Bool → Bool),
    polynomial_time_generated Q ∧
    ∀ (x : List Bool),
      (x ∈ Ayes → (Pr (Q (List.length x) x) ≥ a (List.length x))) ∧
      (x ∈ Ano → (Pr (Q (List.length x) x) ≤ b (List.length x)))

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
      (x ∈ Ayes → Pr (Q.Q (List.length x) x) ≥ a (List.length x)) ∧
      (x ∈ Ano → Pr (Q.Q (List.length x) x) ≤ b (List.length x))
