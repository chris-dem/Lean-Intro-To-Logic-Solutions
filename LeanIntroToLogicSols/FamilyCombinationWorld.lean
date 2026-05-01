import Mathlib
import LeanIntroToLogicSols.CombinationWorld
import LeanIntroToLogicSols.ComplementWorld
import LeanIntroToLogicSols.IntersectionWorld
import LeanIntroToLogicSols.FamilyIntersectionWorld
import LeanIntroToLogicSols.FamilyUnionWorld
import LeanIntroToLogicSols.UnionWorld

example (F : Set (Set U)) : (⋃₀ F)ᶜ = ⋂₀ {s | sᶜ ∈ F} := by
  apply Set.Subset.antisymm
  intro x hx
  rw [my_mem_sInter]
  intro m hm
  rw [Set.mem_compl_iff]  at hx
  rw [Set.mem_sUnion]  at hx
  push Not at hx
  rw [Set.mem_setOf] at hm
  apply hx at hm
  rw [Set.mem_compl_iff]  at hm
  push Not at hm
  exact hm
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_sUnion]
  push Not
  intro p hp
  rw [Set.mem_sInter] at hx
  rw [← Set.mem_compl_iff] 
  apply hx
  rw [Set.mem_setOf, my_compl_compl]
  exact hp

example (F : Set (Set U)) : (⋂₀ F)ᶜ = ⋃₀ {s | sᶜ ∈ F} := by
  apply Set.Subset.antisymm
  intro x hx
  rw [Set.mem_sUnion]
  rw [Set.mem_compl_iff] at hx
  rw [Set.mem_sInter] at hx
  push Not at hx
  obtain ⟨p, hp⟩  := hx
  obtain ⟨hF, hT⟩  := hp
  apply Exists.intro (pᶜ)
  rw [← Set.mem_compl_iff] at hT
  constructor
  rw [Set.mem_setOf, my_compl_compl]
  exact hF
  exact hT
  intro x hx
  rw [Set.mem_sUnion] at hx
  obtain ⟨ p, hp ⟩  := hx
  obtain ⟨ hS, hV ⟩  := hp
  rw [Set.mem_setOf] at hS
  rw [Set.mem_compl_iff, Set.mem_sInter]
  push Not
  use pᶜ
  constructor
  apply hS
  rw [Set.mem_compl_iff]
  push Not
  exact hV

example (F G : Set (Set U)) (h1 : ∀ s ∈ F, ∃ t ∈ G, s ⊆ t) (h2 : ∃ s ∈ F, ∀ t ∈ G, t ⊆ s) : ∃ u, u ∈ F ∩ G := by
  obtain ⟨p, hp⟩ := h2
  apply Exists.intro p
  rw [Set.mem_inter_iff]
  constructor
  apply hp.left
  obtain ⟨hf, hE⟩ :=  hp
  apply h1 at hf
  obtain ⟨m, hm⟩ := hf
  obtain ⟨hG, hpm⟩ := hm 
  have heq : p = m := by
    apply Set.Subset.antisymm
    exact hpm
    apply hE at hG
    exact hG
  rw [heq]
  exact hG

example (F G H : Set (Set U)) (h1 : ∀ s ∈ F, ∃ u ∈ G, s ∩ u ∈ H) : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
  intro x hx
  rw [Set.mem_sUnion]
  rw [Set.mem_inter_iff] at hx
  obtain ⟨hF, hG⟩  := hx
  rw [Set.mem_sUnion] at hF
  rw [Set.mem_sInter] at hG
  obtain ⟨h, hF⟩:= hF
  obtain ⟨hF, hP⟩ := hF
  apply h1 at hF
  obtain ⟨m, hr⟩ := hF
  obtain ⟨hgG,hC⟩ := hr
  apply hG at hgG
  use h ∩ m
  have h1 : x ∈ h ∩ m := by
    apply And.intro hP hgG
  apply And.intro hC h1

example (F G : Set (Set U)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  intro x hx
  rw [Set.mem_sUnion]
  rw [Set.mem_inter_iff] at hx
  obtain ⟨ hfU, hnU⟩ := hx
  rw [Set.mem_sUnion] at hfU
  obtain ⟨p, hp ⟩ := hfU
  obtain ⟨hpF, hxp ⟩ := hp
  rw [Set.mem_compl_iff, Set.mem_sUnion] at hnU
  push Not at hnU
  have hp : p ∈ Gᶜ := by
   by_contra hn
   rw [Set.mem_compl_iff] at hn
   push Not at hn
   apply hnU at hn
   exact hn hxp
  use p
  constructor
  apply And.intro hpF hp
  exact hxp


example (F G : Set (Set U)) (h1 : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ) : (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) := by
  by_contra h
  have h: ¬ ∀ p ∈ ⋃₀ F ∩ ⋃₀ G, p ∈  ⋃₀ (F ∩ G) := by
    exact h
  push Not at h
  obtain ⟨p, hp⟩  := h
  obtain ⟨hl, hr⟩  := hp
  obtain ⟨hF, hG⟩  := hl
  rw [Set.mem_sUnion] at hr
  push_neg  at hr
  rw [Set.mem_sUnion] at hF
  obtain ⟨q, hq⟩ := hF
  obtain ⟨hq, hqF⟩ := hq
  rw [Set.mem_sUnion] at hG
  have h : ∃ t ∈ F ∩ Gᶜ, p ∈ t :=  by
    use q
    constructor
    constructor
    exact hq
    by_contra hCn
    rw [Set.mem_compl_iff] at hCn
    push Not at hCn
    have hFQ: q ∈ F ∩ G := And.intro hq hCn 
    apply hr at hFQ
    exact hFQ hqF
    exact hqF
  rw [← Set.mem_sUnion] at h
  apply h1 at h
  rw [Set.mem_inter_iff] at h
  obtain ⟨ hL, hR ⟩ := h
  rw [Set.mem_compl_iff, Set.mem_sUnion] at hR
  exact hR hG


example (F G : Set (Set U)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ {s | ∃ u ∈ F, ∃ v ∈ G, s = u ∩ vᶜ} := by
  intro x hx
  rw [Set.mem_sUnion]
  rw [Set.mem_inter_iff] at hx
  obtain ⟨hf, hr⟩  :=  hx
  rw [Set.mem_sUnion] at hf
  rw [Set.mem_compl_iff, Set.mem_sInter] at hr
  push_neg at hr
  obtain ⟨fS, hfS ⟩ := hf
  obtain ⟨gS, hgS ⟩ := hr
  use fS ∩ gSᶜ 
  constructor
  rw [Set.mem_setOf]
  use fS
  constructor
  exact hfS.left
  use gS
  constructor
  exact hgS.left
  rfl
  rw [Set.mem_inter_iff]
  constructor
  exact hfS.right
  exact hgS.right


example (A : Set U) (h1 : ∀ F : (Set (Set U)), (⋃₀ F = A → A ∈ F)) : ∃ x, A = {x} := by
  have h2 := h1 { s | ∃ x, s = {x} ∧  x ∈ A  }
  rw [Set.mem_setOf] at h2
  have h : (∃ x , A = {x}) ↔ ∃x, A ={x} ∧ x ∈  A := by
    constructor
    intro hm
    obtain ⟨ p, hp⟩ := hm
    use p
    constructor
    exact hp
    rw [hp]
    rw [Set.mem_singleton_iff]
    intro hm
    obtain ⟨ p, hp⟩ := hm
    use p
    apply hp.left
  rw [h]
  apply h2
  apply Set.Subset.antisymm
  intro m hm
  rw [Set.mem_sUnion] at hm
  obtain ⟨p, hp⟩  :=hm
  obtain ⟨hl, hr⟩  :=hp
  rw [Set.mem_setOf] at hl
  obtain ⟨b, hPG⟩  := hl
  obtain ⟨hPGL, hPGR⟩  := hPG
  rw [hPGL, Set.mem_singleton_iff] at hr
  rw [←hr] at hPGR
  exact hPGR
  intro m hm
  rw [Set.mem_sUnion]
  use {m}
  constructor
  rw [Set.mem_setOf]
  use m
  rw [Set.mem_singleton_iff]





  
