--A promise problem A (Ayes Ano) is in BPP if and only if there exists a polynomial-time probabilistic Turing machine M that accepts every string x Ayes with probability at least 2/3, and accepts every string x E Ano with probability at most 1/3.


import Init.Data.List

namespace complexity

structure TuringMachine where
  states : Type                 -- Set of states
  symbols : Type                -- Set of symbols
  blank : symbols                -- Blank symbol not in input alphabet
  transition : states → symbols → states → symbols → List (ℝ × ℝ)  -- Probabilistic transition function

structure TMConfiguration (TM : Type TuringMachine) where
  state  : TM.states
  tape  list : TM.symbols

def PSPACE (TM  TuringMachine) (f : TMConfiguration TM → bool) :=
  ∃ (poly  ℕ :ℕ), ∀ (n  ℕ), ∃ (config : TMConfiguration TM),
    config.tape.length ≤ poly n ∧
    (∀ (eps  ℝ), eps  0 → ∃ (k  ℕ), Pr[f TM config k] ≥ 1 - eps)

end complexity
