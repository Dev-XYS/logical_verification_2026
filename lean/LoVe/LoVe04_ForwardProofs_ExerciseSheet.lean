/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
    a → a :=
  assume ha : a
  show a from ha

theorem K (a b : Prop) :
    a → b → b :=
  assume ha : a
  assume hb : b
  show b from hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  assume h : a -> b -> c
  assume hb : b
  assume ha : a
  show c from h ha hb

theorem proj_fst (a : Prop) :
    a → a → a :=
  assume ha1 : a
  assume ha2 : a
  show a from ha1

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  assume ha1 : a
  assume ha2 : a
  show a from ha2

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  assume h1 : a -> b -> c
  assume ha : a
  assume h2 : a -> c
  assume hb : b
  show c from h2 ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  assume h : a -> b
  assume nb : ¬ b
  assume ha : a
  have hb := h ha
  show False from nb hb

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    (assume h : ∀ (x : α), p x ∧ q x
     have hp : ∀ (x : α), p x :=
       (fix x : α
        show p x from (h x).left)
     have hq : ∀ (x : α), q x :=
       (fix x : α
        show q x from (h x).right)
     show (∀ (x : α), p x) ∧ ∀ (x : α), q x from And.intro hp hq)
    (assume h : (∀ (x : α), p x) ∧ ∀ (x : α), q x
     have hp : ∀ (x : α), p x := h.left
     have hq : ∀ (x : α), q x := h.right
     fix x : α
     show p x ∧ q x from And.intro (hp x) (hq x))

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
    (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume h : ∃x, ∀y, p x y
  fix y : α
  match h with  -- Could be better if one could use `obtain`
  | ⟨x, hx⟩ => Exists.intro x (hx y)


/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

theorem binomial_square (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
    (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
      by rw [add_mul]
    _ = a * a + a * b + b * a + b * b :=
      by simp [mul_add, add_assoc]
    _ = a * a + a * b + a * b + b * b :=
      by rw [mul_comm b a]
    _ = a * a + 2 * a * b + b * b :=
      by simp [add_assoc, mul_assoc, <-Nat.two_mul]

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  have eq1 : (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
    by rw [add_mul]
  have eq2 : a * (a + b) + b * (a + b) = a * a + a * b + b * a + b * b :=
    by simp [mul_add, add_assoc]
  have eq3 : a * a + a * b + b * a + b * b = a * a + a * b + a * b + b * b :=
    by rw [mul_comm b a]
  have eq4 : a * a + a * b + a * b + b * b = a * a + 2 * a * b + b * b :=
    by simp [add_assoc, mul_assoc, <-Nat.two_mul]
  show _
    by simp [eq1, eq2, eq3, eq4]


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
    False :=
  by
    let P := fun x : Nat => True
    have h : ∀x : Nat, x = 0 ∧ P x := Iff.mpr (All.one_point_wrong 0 P) True.intro
    have habsurd : 1 = 0 := (h 1).left
    injection habsurd

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
    False :=
  by
    let P := fun x : Nat => False
    have h : 1 = 0 -> False := (by intro eq; injection eq)
    have h : ∃x : Nat, x = 0 -> P x := Exists.intro 1 h
    exact Iff.mp (Exists.one_point_wrong 0 P) h

end LoVe
