import Mathlib
import Mathlib.Tactic

example (x : U)(A: Set U)(h: x ∈ A): x ∈ A := by
  exact h


example (x: U) (A B: Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  apply h1
  exact h2

example  (x : U)(A B C : Set U) (h1 : A ⊆ B) (h2: B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  have h4: x ∈ B := h1 h3
  exact h2 h4


example {x: U} {A B C : Set U}(h1: A ⊆ B) (h2 : x ∈ B→ x ∈ C): x ∈ A → x ∈ C := by
  intro h
  have h4: x ∈ B := h1 h
  exact h2 h4



theorem my_refl (A:Set U) : A ⊆ A := by
  intro x h
  exact h

theorem my_trans {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x h
  have h4: x ∈ B := h1 h
  exact h2 h4

