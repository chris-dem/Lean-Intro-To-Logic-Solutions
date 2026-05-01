import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

example {A B :Set U} {x : U}(h1 : x ∈ A) (h2 : x ∉ B) : ¬ A ⊆ B := by
  by_contra h
  have h4: x ∈ B := h h1
  exact h2 h4


theorem my_mem_compl_iff (A : Set U) (x : U) : x ∈ Aᶜ ↔  x ∉ A := by
  rfl

theorem my_compl_subset_compl_of_subset {A  B: Set U}(h1 : A ⊆ B): Bᶜ ⊆ Aᶜ := by
  intro x hm
  rw [my_mem_compl_iff A x]
  rw [my_mem_compl_iff B x] at hm
  intro h
  have hp: x ∈ B := h1 h
  exact hm hp

theorem my_compl_compl (A : Set U): Aᶜᶜ = A:= by
  apply Set.Subset.antisymm 
  intro h₁ hp
  rw [my_mem_compl_iff, my_mem_compl_iff] at hp
  push Not at hp
  exact hp
  intro  h h1
  rw [my_mem_compl_iff, my_mem_compl_iff]
  push Not
  exact h1


example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro
  intro h1
  apply my_compl_subset_compl_of_subset h1
  intro h1
  apply my_compl_subset_compl_of_subset at h1
  rw [my_compl_compl A, my_compl_compl B] at h1
  exact h1

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  constructor
  intro h1
  apply my_compl_subset_compl_of_subset h1
  intro h1
  apply my_compl_subset_compl_of_subset at h1
  rw [my_compl_compl A, my_compl_compl B] at h1
  exact h1


