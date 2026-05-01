import Mathlib

example (x : U)(A B : Set U) (h: x ∈ A): x ∈ A ∨ x ∈ B := by
  left
  exact h


example (x : U)(A B : Set U) (h: x ∈ A): x ∈ A ∨ x ∈ B := by
  apply Or.inl h


theorem my_mem_union (x : U)(A B : Set U): x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  rfl

example (A B : Set U): B ⊆ A ∪ B := by
  intro x hx
  rw [my_mem_union]
  apply Or.inr hx



example (A B  : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C): A ∪ B ⊆ C := by
  intro x hx
  rw [my_mem_union] at hx
  cases hx with 
  | inl hl =>
    exact h1 hl
  | inr hr =>
    exact h2 hr

example (A B : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C): A ∪ B ⊆ C := by
  intro x hx
  rw [my_mem_union] at hx
  rcases hx with hl | hr
  exact h1 hl
  exact h2 hr

theorem my_union_subset_swap (A B : Set U): A ∪ B ⊆ B ∪ A := by
  intro x hx
  rw [my_mem_union]
  rw [my_mem_union] at hx
  rcases hx with hl | hr
  apply Or.inr hl
  apply Or.inl hr

theorem my_union_comm (A B : Set U): A ∪ B = B ∪ A := by
  apply Set.Subset.antisymm
  apply my_union_subset_swap
  apply my_union_subset_swap


theorem my_union_assoc (A B C : Set U): A ∪ B ∪ C = A ∪ (B ∪ C) := by
  apply Set.Subset.antisymm
  intro x hx
  rw [my_mem_union,my_mem_union] at hx
  rw [my_mem_union, my_mem_union]
  cases hx with
  | inl hl => 
    rcases hl with hll | hlr
    apply Or.inl hll
    right
    apply Or.inl hlr
  | inr hr =>
    right
    apply Or.inr hr
  intro x hx
  cases hx with 
  | inl hl =>
    left
    apply Or.inl hl
  | inr hr =>
    rw [my_mem_union] at hr
    rcases hr with hrl | hrr
    left
    apply  Or.inr hrl
    right
    exact hrr



