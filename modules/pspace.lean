--A promise problem A = (Ayes, Ano) is in PSPACE if and only if there exists a deterministic Turing machine M running in polynomial space that accepts every string x E Ayes and rejects every string x Ano


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
