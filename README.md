# GPTLean 
A lean module for formalizing GPTs

Install Mathlib in modules folder and 
Open VSCode from modules folder to contribute while on lean4.

There is a python file to suggest tactics and proofs for your theorems using LeanDojo. Additional tactics can be trained in that model using pytorch.

## Quantum Computational Complexity Classes

To learn more about [Quantum Computational Classes](https://arxiv.org/abs/0804.3401), refer this research paper by John Watrous. 

#### BPP

A language L is in BPP if and only if there exits a probabilistic Turing machine M,such that

- M runs for polynomial time on all inputs
- For all x in L,M outputs 1 with probability greater than or equal to 2/3
- For all x not in L,M outputs 1 with probability less than or equal to 1/3

```lean4
def in_bpp (A : set string) : Prop :=
  ∃ (M : string → bool),
    turing_machine M ∧ ∀ x ∈ A, M x = tt ∧ M.prob_accept ≥ 2/3
    ∧ ∀ x ∉ A, M x = ff ∧ M.prob_accept ≤ 1/3

end bpp

```

#### PSPACE

In computational complexity theory, PSPACE is the set of all decision problems that can be solved by a Turing machine using a polynomial amount of space.
If we denote by SPACE(f(n)), the set of all problems that can be solved by Turing machines using O(f(n)) space for some function f of the input size n, then we can define PSPACE formally as


PSPACE is a strict superset of the set of context-sensitive languages

```
def PSPACE (TM  TuringMachine) (f : TMConfiguration TM → bool) :=
  ∃ (poly  ℕ :ℕ), ∀ (n  ℕ), ∃ (config : TMConfiguration TM),
    config.tape.length ≤ poly n ∧
    (∀ (eps  ℝ), eps  0 → ∃ (k ℕ), Pr[f TM config k] ≥ 1 - eps)

end complexity
```

### BQP

BQP can be viewed as the languages associated with certain bounded-error uniform families of quantum circuits. A language L is in BQP if and only if there exists a polynomial-time uniform family of quantum circuits , such that {Q<sub>n</sub>: n ∈ N}

- For all n ∈ N, Q<sub>n</sub> takes n qubits as input and outputs 1 bit
- For all x in L, Pr(Q<sub>|x|</sub>(x)=1)>=2/3
- For all x not in L, Pr(Q<sub>|x|</sub>(x)=0)>=2/3

```
def BQP (S : set Σ) (Q : Σ → Type*) : Prop :=
  poly_time_generated S Q (λ _, bool)
```

### AWPP

AWPP contains the complexity class BQP (bounded-error quantum polynomial time), which contains the decision problems solvable by a quantum computer in polynomial time, with an error probability of at most 1/3 for all instances. In fact, it is the smallest classical complexity class that upper bounds BQP

```
def AWPP_BGP (P : awpp_protocol → bgp → Prop) :=
  ∀ (ap : awpp_protocol) (bgp : bgp),
    P ap bgp →
    ∃ (poly : ℕ → ℕ), ∀ (n : ℕ),
      let public_coins := list.repeat tt n in
      let ap' := { ap with public_coins := public_coins } in
      ap.verifier.verify n = tt →
      let prob_dist := bgp.prob bgp.prob_space in
      prob_dist {i | (ap'.prover.prover n).state i} ≥ 2/3 ∧ ap.verifier.verify n = ff →
      prob_dist {i | (ap'.prover.prover n).state i} ≤ 1/3
      end awpp
```

### PP

In complexity theory, PP is the class of decision problems solvable by a probabilistic Turing machine in polynomial time, with an error probability of less than 1/2 for all instances. The abbreviation PP refers to probabilistic polynomial time

```
def PP {α : Type} (p : α → Prop) : Prop :=
  ∃ (A : Set α) (time : α → ℕ) (rand : α → ℕ → Bool),
    (isPolyTimeRandAlgorithm A time rand) ∧
    (∀ (x : α), p x ↔ ∃ (y : α →  A), rand x (time x) = tt) ∧
    (∀ (x : α), ¬ p x ↔ ∀ (y : α →  A), rand x (time x) = ff)
```
