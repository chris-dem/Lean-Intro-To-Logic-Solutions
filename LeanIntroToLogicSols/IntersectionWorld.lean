import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

example (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left

theorem my_mem_inter_iff (x : U)(A B : Set U):  x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B  := by
  rfl

theorem my_mem_inter_right (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  rw [my_mem_inter_iff] at h
  exact h.right


theorem my_mem_inter_left (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ A := by
  rw [my_mem_inter_iff] at h
  exact h.left


example (A B : Set U) : A ∩ B ⊆ A := by
  intro h ha
  rw [my_mem_inter_iff] at ha
  exact ha.left

example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  rw [my_mem_inter_iff]
  constructor 
  exact h1
  exact h2

example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  apply And.intro h1 h2


example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro p ha
  have hl: p ∈ B := h1 ha
  have hr: p ∈ C := h2 ha
  apply And.intro hl hr

theorem my_inter_subset_swap (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro a ha
  rw [my_mem_inter_iff] at ha
  apply And.intro ha.right ha.left

theorem inter_comm (A B : Set U) : A ∩ B = B ∩ A := by
  apply Set.Subset.antisymm
  apply my_inter_subset_swap
  apply my_inter_subset_swap


theorem my_inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  constructor
  intro hm
  rw [my_mem_inter_iff] at hm
  have hl : x ∈ A := hm.left.left
  have hr : x ∈ B ∩ C := by
    apply And.intro hm.left.right hm.right
  apply And.intro hl hr
  intro hm
  rw [my_mem_inter_iff] at hm
  have hl : x ∈ A ∩ B := by
    apply And.intro hm.left hm.right.left
  have hr : x ∈  C := hm.right.right
  apply And.intro hl hr


