--A promise problem A=(Ayes,Ano) is in PP if and only if there exist a polynomialtime probabilistic turing machine M that accepts every string x E Ayes with probability strictly greater than 1/2,and accepts every string x E at most 1/2

import Std.Data.Nat.Gcd
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic


-- Define a probabilistic polynomial-time algorithm
def isPolyTimeRandAlgorithm {α : Type} (p : α → Prop) (time : α → ℕ) (rand : α → ℕ → Bool) : Prop :=
  ∃ (poly : ℕ → ℕ),
    (∀ (x : α), time x ≤ poly Nat.Size x) ∧
    ∀ (x : α), p x →
      ∃ (k : ℕ),
        rand x k = tt ∧
        ∀ (k' : ℕ), k' ≥ k → p x → rand x k' =  tt


-- Define the class PP with completeness and soundness
def PP {α : Type} (p : α → Prop) : Prop :=
  ∃ (A : Set α) (time : α → ℕ) (rand : α → ℕ → Bool),
    (isPolyTimeRandAlgorithm A time rand) ∧
    (∀ (x : α), p x ↔ ∃ (y : α →  A), rand x (time x) = tt) ∧
    (∀ (x : α), ¬ p x ↔ ∀ (y : α →  A), rand x (time x) = ff)

-- Prove that PP is closed under union
lemma PP_union_closed {α : Type} {p q : α → Prop} :
  PP p → PP q → PP (λ x => p x ∨ q x) :=
  let hpp hpq
  rcases hpp := ⟨A, time_p, rand_p, poly_time_p, hp, hnp⟩,
  rcases hpq := ⟨B, time_q, rand_q, poly_time_q, hq, hnq⟩,
  use A ∪ B, -- union of A and B
  use (λ x, max (time_p x) (time_q x)), -- max of the two time functions
  use (λ x k, rand_p x k || rand_q x k), -- the randomized algorithm combines the behaviors of rand_p and rand_q
  split,
  {
    -- Show that the union is accepted in polynomial time with a randomized algorithm
    intros x hx,
    cases hx,
    {
      apply poly_time_p,
      assumption,
    },
    {
      apply poly_time_q,
      assumption,
    },
  },
  {
    -- Show that the union condition holds
    intros x,
    split,
    {
      intro h_union,
      cases h_union,
      {
        apply hp,
        assumption,
      },
      {
        apply hq,
        assumption,
      },
    },
    {
      intro h,
      cases h,
      {
        left,
        apply hp.2,
        assumption,
      },
      {
        right,
        apply hq.2,
        assumption,
      },
    },
  },


-- Prove that PP is closed under intersection
theorem PP_intersection_closed {α : Type} {p q : α → Prop} :
  PP p → PP q → PP (λ x => p x ∧ q x) :=
  let hpp hpq
  rcases hpp := ⟨A, time_p, rand_p, poly_time_p, hp, hnp⟩,
  rcases hpq := ⟨B, time_q, rand_q, poly_time_q, hq, hnq⟩,
  use A ∩ B, -- intersection of A and B
  use (λ x, max (time_p x) (time_q x)), -- max of the two time functions
  use (λ x k, rand_p x k && rand_q x k), -- the randomized algorithm combines the behaviors of rand_p and rand_q
  split,
  {
    -- Show that the intersection is accepted in polynomial time with a randomized algorithm
    intros x hx,
    apply poly_time_p,
    apply hx.left,
  },
  {
    -- Show that the intersection condition holds
    intros x,
    split,
    {
      intro h_inter,
      apply and.intro,
      {
        apply hp.2,
        apply h_inter.left,
      },
      {
        apply hq.2,
        apply h_inter.right,
      },
    },
    {
      intro h,
      apply and.intro,
      {
        apply hp.1,
        apply h.left,
      },
      {
        apply hq.1,
        apply h.right,
      },
    },
  },

-- Prove that PP is closed under complement
lemma PP_complement_closed {α : Type} {p : α → Prop} :
  PP p → PP (λ x => ¬ p x) :=

  let hpp
  rcases hpp := ⟨A, time_p, rand_p, poly_time_p, hp, hnp⟩,
  use Aᶜ, -- complement of A
  use time_p,
  use (λ x k, bnot (rand_p x k)), -- complement the behavior of rand_p
  split,
  {
    -- Show that complement is accepted in polynomial time with a randomized algorithm
    intros x hx,
    apply poly_time_p,
    assumption,
  },
  {
    -- Show that the complement condition holds
    intros x,
    split,
    {
      intro h_comp,
      apply hnp.2,
      assumption,
    },
    {
      intro h,
      apply hnp.1,
      assumption,
    },
  },

-- Additional theorems can be proven similarly.
