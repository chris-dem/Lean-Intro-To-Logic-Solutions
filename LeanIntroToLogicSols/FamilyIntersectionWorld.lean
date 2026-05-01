import Mathlib
import LeanIntroToLogicSols.CombinationWorld
import LeanIntroToLogicSols.ComplementWorld
import LeanIntroToLogicSols.IntersectionWorld
import LeanIntroToLogicSols.UnionWorld

theorem my_mem_sInter {x: U} {S: Set (Set U)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t := by
  rfl

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  intro x hx
  rw [my_mem_sInter] at hx
  specialize hx A
  exact hx h1


example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by 
  intro x hx
  rw [my_mem_sInter] 
  rw [my_mem_sInter]  at hx
  intro t ht
  have hp : t ∈ G := by
    exact h1 ht
  exact (hx t)  hp


theorem my_mem_pair  {U}(t A B: U) : t ∈ ({A, B} : Set U) ↔ t = A ∨ t = B   := by
  rfl

example (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  apply Set.Subset.antisymm
  intro x hx
  rw [my_mem_inter_iff]  at hx
  rw [my_mem_sInter]
  intro m hm
  rw [my_mem_pair] at hm
  rcases hx with ⟨ hxl, hxr ⟩ 
  rcases hm with hl | hr
  rw [hl]
  exact hxl
  rw [hr]
  exact hxr
  intro x hx
  rw [my_mem_sInter] at hx
  rw [my_mem_inter_iff]
  have hxA : x ∈ A := by
    apply hx A
    rw [my_mem_pair]
    left
    rfl
  have hxB: x ∈ B := by
    apply hx B
    rw [my_mem_pair]
    right
    rfl
  apply And.intro hxA hxB

example (F G : Set (Set U)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  apply Set.Subset.antisymm
  -- Left to Right
  intro x hx
  rw [my_mem_inter_iff]
  rw [my_mem_sInter] at hx
  constructor
  -- Case 1
  rw [my_mem_sInter]
  intro g hg
  apply hx
  apply Or.inl hg
  -- Case 1
  rw [my_mem_sInter]
  intro g hg
  apply hx
  apply Or.inr hg
  -- Right to Left
  intro x hx
  rw [my_mem_sInter]
  intro p hp
  rw [my_mem_inter_iff] at hx
  rcases hx with ⟨ hl, hr ⟩ 
  rw [my_mem_sInter] at hl
  rw [my_mem_sInter] at hr
  rcases hp with hpl | hpr
  apply hl at hpl
  exact hpl
  apply hr at hpr
  exact hpr


example (A : Set U) (F : Set (Set U)) : A ⊆ ⋂₀ F ↔ ∀ s ∈ F, A ⊆ s := by
  constructor
  -- Left to right
  intro h
  intro m hm p hp
  have hpP: p ∈ ⋂₀ F := h hp
  rw [my_mem_sInter] at hpP
  apply hpP
  exact hm
  -- Right to Left
  intro hm p hp
  rw [my_mem_sInter]
  intro f hf
  apply hm at hf
  exact hf hp


example (A : Set U) (F G : Set (Set U)) (h1 : ∀ s ∈ F, A ∪ s ∈ G) : ⋂₀ G ⊆ A ∪ (⋂₀ F) := by
  intro m hm
  rw [my_mem_sInter] at hm
  rw [my_mem_union]
  rw [my_mem_sInter]
  by_cases hp: m ∈ A
  left 
  exact hp
  right
  intro f hf
  have hpP: m ∈ A ∪ f := by
    apply hm
    apply h1
    exact hf
  rw [my_mem_union] at hpP
  rcases hpP with hl | hr
  apply hp at hl
  trivial
  exact hr


  
