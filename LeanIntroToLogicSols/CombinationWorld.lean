import MathLib
import LeanIntroToLogicSols.ComplementWorld
import LeanIntroToLogicSols.UnionWorld
import LeanIntroToLogicSols.IntersectionWorld

theorem my_compl_union (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  apply Set.Subset.antisymm
  intro x hx
  rw [my_mem_inter_iff]
  rw [my_mem_compl_iff] at hx
  rw [my_mem_compl_iff,my_mem_compl_iff]
  constructor
  by_contra h
  have hp : x ∈ A ∪ B := by
    rw [my_mem_union]
    apply Or.inl h
  exact hx hp
  by_contra h
  have hp : x ∈ A ∪ B := by
    rw [my_mem_union]
    apply Or.inr h
  exact hx hp
  intro x hx
  rw [my_mem_inter_iff] at hx
  rw [my_mem_compl_iff] 
  rw [my_mem_compl_iff,my_mem_compl_iff] at hx
  by_contra h
  rw [my_mem_union] at h
  rcases h with hl | hr
  exact hx.left hl
  exact hx.right hr

example (A B: Set U): (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  apply Set.Subset.antisymm
  intro x hx
  rw [my_mem_inter_iff]
  rw [my_mem_compl_iff] at hx
  rw [my_mem_union] at hx
  push Not at hx
  exact hx
  intro x hx
  rw [my_mem_compl_iff]
  rw [my_mem_union]
  push Not
  exact hx
  

theorem my_compl_iter(A B : Set U): (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw [← compl_compl (Aᶜ  ∪ Bᶜ), my_compl_union, compl_compl, compl_compl]

theorem my_inter_distrib_left(A B C: Set U): A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply Set.Subset.antisymm
  intro x hx
  rw [my_mem_inter_iff,my_mem_union] at hx
  rw [my_mem_union, my_mem_inter_iff,my_mem_inter_iff] 
  rcases hx with ⟨ al, ar ⟩ 
  rcases ar with  ol|  or
  apply Or.inl (And.intro al ol)
  apply Or.inr (And.intro al or)
  intro x hx
  rw [my_mem_union, my_mem_inter_iff,my_mem_inter_iff]  at hx
  rw [my_mem_inter_iff,my_mem_union] 
  rcases hx with hl | hr
  rcases hl with ⟨ al, ar ⟩ 
  apply And.intro al (Or.inl ar)
  rcases hr with ⟨ al, ar ⟩ 
  apply And.intro al (Or.inr ar)


theorem union_distrib_left (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  rw [← compl_compl (A ∪ B ∩ C),my_compl_union, my_compl_iter B,my_inter_distrib_left]
  rw [my_compl_union, my_compl_iter,my_compl_iter]
  repeat rw [compl_compl]
  
example (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x hx
  have hAC : x ∈ A ∪ C := by
    rw [my_mem_union]
    apply Or.inl hx
  have hBC: x ∈ B ∪ C := by
    apply h1
    exact hAC
  rw [my_mem_union] at hAC
  rw [my_mem_union] at hBC
  rcases hAC with hlAC | hrAC
  rcases hBC with hlBC | hrBC 
  exact hlBC
  have haBC : x ∈ B ∩ C := by
    apply h2
    rw [my_mem_inter_iff]
    apply And.intro hx hrBC
  rw [my_mem_inter_iff] at haBC
  exact haBC.left
  have haBC : x ∈ B ∩ C := by
      apply h2
      rw [my_mem_inter_iff]
      apply And.intro hx hrAC
  rw [my_mem_inter_iff] at haBC
  exact haBC.left


