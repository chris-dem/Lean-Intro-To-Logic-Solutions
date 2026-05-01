import Mathlib
import LeanIntroToLogicSols.CombinationWorld
import LeanIntroToLogicSols.ComplementWorld
import LeanIntroToLogicSols.IntersectionWorld
import LeanIntroToLogicSols.FamilyIntersectionWorld
import LeanIntroToLogicSols.UnionWorld

example (A : Set U) : ∃ s, s ⊆ A := by
  use A

theorem my_mem_sUnion (x : U) (F: Set (Set U)): x ∈ ⋃₀ F ↔ ∃ t, t ∈ F ∧ x ∈ t := by
  rfl

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x hx
  rw [my_mem_sUnion] 
  apply Exists.intro A
  apply And.intro h1 hx

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x hx
  rw [my_mem_sUnion]  at hx
  rw [my_mem_sUnion]
  obtain ⟨w, hw⟩ := hx
  have hG: w ∈ G := h1 hw.left
  use w
  apply And.intro hG hw.right

example (A B : Set U) : A ∪ B = ⋃₀ {A, B} := by
  apply Set.Subset.antisymm
  -- L to R
  intro x hx
  rw [my_mem_union] at hx
  rw [my_mem_sUnion]
  rcases hx with hl | hr
  use A
  rw [my_mem_pair]
  constructor
  left
  rfl
  exact hl
  use B
  constructor
  right
  rfl
  exact hr
  intro m hm
  rw [my_mem_sUnion] at hm
  rw [my_mem_union]
  obtain ⟨w, hw ⟩ := hm
  rw [my_mem_pair] at hw
  rcases hw with ⟨ hor, h ⟩
  rcases hor with  hol| hor
  left
  rw [← hol]
  exact h
  right
  rw [← hor]
  exact h


example (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  apply Set.Subset.antisymm
  intro x hx
  rw [my_mem_sUnion] at hx
  obtain ⟨w, hw ⟩  := hx
  rcases hw with ⟨ hwl, hwr⟩
  rw [my_mem_union]
  rw [my_mem_union] at hwl
  rcases hwl with hl | hr 
  left
  rw [my_mem_sUnion]
  apply Exists.intro w
  apply And.intro hl hwr
  right
  rw [my_mem_sUnion]
  apply Exists.intro w
  apply And.intro hr hwr
  -- R to L
  intro x hx
  rw [my_mem_union] at hx
  rcases hx with hl | hr
  obtain ⟨w, hw⟩  := hl
  use w
  rcases hw with ⟨ hF, hW⟩ 
  have hp: w ∈ F ∪ G := by
    apply Or.inl hF
  apply And.intro hp hW
  obtain ⟨w, hw⟩  := hr
  use w
  rcases hw with ⟨hF, hW⟩ 
  have hp: w ∈ F ∪ G := by
    apply Or.inr hF
  apply And.intro hp hW

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  constructor
  intro hm P hp x hx
  apply hm
  rw [my_mem_sUnion]
  use P
  intro hm x hp
  obtain ⟨w, hw⟩ := hp
  rcases hw with  ⟨ hF, hw⟩ 
  apply hm at hF
  exact hF hw

example (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {s | ∃ u ∈ F, s = A ∩ u} := by
  apply Set.Subset.antisymm
  intro m hm
  rw [Set.mem_sUnion]
  rw [Set.mem_inter_iff] at hm
  rcases hm with ⟨ hA, hUf⟩
  obtain ⟨f, hUf⟩ :=  hUf
  rcases hUf with ⟨hiF, hmf ⟩ 
  use f ∩ A
  constructor
  rw [Set.mem_setOf]
  use f
  constructor
  exact hiF
  rw [Set.inter_comm]
  exact And.intro  hmf hA
  intro x hx
  obtain ⟨ w, hw ⟩ := hx
  obtain ⟨ hl, hr ⟩ := hw
  rw [Set.mem_setOf] at hl
  obtain ⟨ p, hp ⟩ := hl
  obtain ⟨ hp1, hp2 ⟩ := hp
  have hP2 : x ∈ A ∩ p := by
    rw [← hp2]
    exact hr 
  constructor
  apply hP2.left
  rw [Set.mem_sUnion]
  use p
  apply And.intro hp1 hP2.right

