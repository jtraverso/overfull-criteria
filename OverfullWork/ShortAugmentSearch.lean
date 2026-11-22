module

public import OverfullWork.AlternatingFive

@[expose] public section


/-! # Finding the five-edge alternating pattern from neighbourhood sizes -/

namespace OverfullWork.ShortAugmentSearch

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Six vertices arranged in two parts give an embedding of the short
alternating path. The unmatched endpoints are outside the eligible sets. -/
theorem six_embedding (A B EA EB : Finset V) (u v b₁ b₂ a₂ a₁ : V)
    (hdis : Disjoint A B) (hEA : EA⊆A) (hEB : EB⊆B)
    (hu : u∈A) (hv : v∈B) (huE : u∉EA) (hvE : v∉EB)
    (hb₁ : b₁∈EB) (hb₂ : b₂∈EB) (ha₂ : a₂∈EA) (ha₁ : a₁∈EA)
    (hb : b₁≠b₂) (ha : a₂≠a₁) :
    ∃ p : Fin 6 ↪ V,p 0=u ∧ p 1=b₁ ∧ p 2=b₂ ∧ p 3=a₂ ∧ p 4=a₁ ∧ p 5=v := by
  have hcross : ∀ a∈A,∀ b∈B,a≠b := by
    intro a ha b hb he
    subst b
    exact (disjoint_left.mp hdis) ha hb
  have hneqU1 : u≠a₁ := fun h => huE (h ▸ ha₁)
  have hneqU2 : u≠a₂ := fun h => huE (h ▸ ha₂)
  have hneqV1 : b₁≠v := fun h => hvE (h ▸ hb₁)
  have hneqV2 : b₂≠v := fun h => hvE (h ▸ hb₂)
  have hc₁:=hcross u hu b₁ (hEB hb₁)
  have hc₂:=hcross u hu b₂ (hEB hb₂)
  have hc₃:=hcross u hu v hv
  have hc₄:=hcross a₁ (hEA ha₁) b₁ (hEB hb₁)
  have hc₅:=hcross a₂ (hEA ha₂) b₁ (hEB hb₁)
  have hc₆:=hcross a₁ (hEA ha₁) b₂ (hEB hb₂)
  have hc₇:=hcross a₂ (hEA ha₂) b₂ (hEB hb₂)
  have hc₈:=hcross a₁ (hEA ha₁) v hv
  have hc₉:=hcross a₂ (hEA ha₂) v hv
  let f : Fin 6 → V:=![u,b₁,b₂,a₂,a₁,v]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f,Ne.symm]
  exact ⟨⟨f,hf⟩,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- A counting argument finds the two matching edges and the three
available crossing edges. `τ` is the matching-partner permutation. -/
theorem exists_five_pattern (A B EA EB : Finset V) (u v : V)
    (τ : Equiv.Perm V) (hτ : ∀ z,τ (τ z)=z)
    (hdis : Disjoint A B) (hEA : EA⊆A) (hEB : EB⊆B)
    (hu : u∈A) (hv : v∈B) (huE : u∉EA) (hvE : v∉EB)
    (hAclosed : ∀ a∈EA,τ a∈EA) (hBclosed : ∀ b∈EB,τ b∈EB)
    (hAne : ∀ a∈EA,τ a≠a) (hBne : ∀ b∈EB,τ b≠b)
    (N : V → V → Prop) [DecidableRel N]
    (hfirst : (EB.filter (N u)).Nonempty)
    (hlarge : ∀ b∈EB,EA.card<(EA.filter (N v)).card+(EA.filter (N b)).card) :
    ∃ p : Fin 6 ↪ V,p 0=u ∧ p 5=v ∧
      p 1∈EB ∧ p 2=τ (p 1) ∧ p 3∈EA ∧ p 4=τ (p 3) ∧
      N (p 0) (p 1) ∧ N (p 2) (p 3) ∧ N (p 5) (p 4) := by
  classical
  obtain ⟨b₁,hb₁⟩:=hfirst
  obtain ⟨hb₁,hub⟩:=mem_filter.mp hb₁
  let b₂:=τ b₁
  have hb₂ : b₂∈EB:=hBclosed b₁ hb₁
  let T:=(EA.filter (N v)).image τ
  let U:=EA.filter (N b₂)
  have hT : T⊆EA := by
    intro a ha
    obtain ⟨z,hz,rfl⟩:=mem_image.mp ha
    exact hAclosed z (mem_filter.mp hz).1
  have hU : U⊆EA:=filter_subset _ _
  have hTU : (T∩U).Nonempty := by
    have ht : T.card=(EA.filter (N v)).card:=card_image_of_injective _ τ.injective
    have hle : (T∪U).card≤EA.card:=card_le_card (union_subset hT hU)
    have hid:=card_union_add_card_inter T U
    have hbig:=hlarge b₂ hb₂
    by_contra hn
    have he : T∩U=∅:=not_nonempty_iff_eq_empty.mp hn
    rw [he,card_empty,add_zero,ht] at hid
    dsimp only [U] at hid hle
    omega
  obtain ⟨a₂,ha₂⟩:=hTU
  obtain ⟨ha₂T,ha₂U⟩:=mem_inter.mp ha₂
  obtain ⟨a₁,ha₁,heq⟩:=mem_image.mp ha₂T
  obtain ⟨ha₁,hva⟩:=mem_filter.mp ha₁
  have ha₂ : a₂∈EA:=(mem_filter.mp ha₂U).1
  have hba : N b₂ a₂:=(mem_filter.mp ha₂U).2
  have hpa : τ a₂=a₁ := by rw [←heq,hτ]
  obtain ⟨p,hp0,hp1,hp2,hp3,hp4,hp5⟩:=six_embedding A B EA EB u v b₁ b₂ a₂ a₁
    hdis hEA hEB hu hv huE hvE hb₁ hb₂ ha₂ ha₁
    (Ne.symm (hBne b₁ hb₁)) (by simpa only [hpa] using (hAne a₂ ha₂).symm)
  refine ⟨p,hp0,hp5,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp only [hp0,hp1,hp2,hp3,hp4,hp5]
  · exact hb₁
  · rfl
  · exact ha₂
  · exact hpa.symm
  · exact hub
  · exact hba
  · exact hva

end OverfullWork.ShortAugmentSearch
