module

public import OverfullWork.CMSOperation41AuxiliarySpokes
public import OverfullWork.CMSOperation41ExactRecords

@[expose] public section


/-! The actual prescribed graph of S2.5, with its two incidence
columns retained. In the empty-active branches these paths supply
all the projected exceptional vertices. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowVertexMatchingAbsorption
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1300000 in
theorem exists_spoke_prescription (G : SimpleGraph V) [DecidableRel G.Adj]
    (B U F : Finset V) (hBU : B ⊆ U) (hUF : U ⊆ F)
    (hDegree : ∀ v ∈ B,F.card+2*B.card ≤ G.degree v) :
    ∃ (e : (↥B × Bool) ↪ ↥(Fᶜ : Finset V)) (P : SimpleGraph V),
      P ≤ G ∧ (∀ x y,P.Adj x y → x ∈ U ∨ y ∈ U) ∧
      (∀ v ∈ B,P.degree v = 2) ∧ (∀ v ∈ U,v ∉ B → P.degree v = 0) ∧
      (∀ v,v ∉ B → P.degree v ≤ 1) ∧
      (∀ z : B,G.Adj z.val (e (z,false)).val ∧ G.Adj z.val (e (z,true)).val) ∧
      ∀ x y,P.Adj x y ↔ ∃ z : B,∃ j : Bool,
        (x = z.val ∧ y = (e (z,j)).val) ∨ (y = z.val ∧ x = (e (z,j)).val) := by
  obtain ⟨e,hAdj⟩ := exists_two_distinct_projection_neighbours G B F hDegree
  let f (j : Bool) (z : B) : ↥(Bᶜ : Finset V) :=
    ⟨(e (z,j)).val,mem_compl.mpr (fun hz => mem_compl.mp (e (z,j)).property (hUF (hBU hz)))⟩
  let P₀ := selectionGraph B (f false)
  let P₁ := selectionGraph B (f true)
  let P := P₀ ⊔ P₁
  have hP₀ : P₀ ≤ G := selectionGraph_le B (f false) (fun z => hAdj z false)
  have hP₁ : P₁ ≤ G := selectionGraph_le B (f true) (fun z => hAdj z true)
  have hSupport (x y : V) : P.Adj x y ↔ ∃ z : B,∃ j : Bool,
      (x = z.val ∧ y = (e (z,j)).val) ∨ (y = z.val ∧ x = (e (z,j)).val) := by
    change (P₀.Adj x y ∨ P₁.Adj x y) ↔ _
    constructor
    · rintro (h|h)
      · rcases h with ⟨z,hx,hy⟩|⟨z,hy,hx⟩
        · exact ⟨z,false,Or.inl ⟨hx,hy⟩⟩
        · exact ⟨z,false,Or.inr ⟨hy,hx⟩⟩
      · rcases h with ⟨z,hx,hy⟩|⟨z,hy,hx⟩
        · exact ⟨z,true,Or.inl ⟨hx,hy⟩⟩
        · exact ⟨z,true,Or.inr ⟨hy,hx⟩⟩
    · rintro ⟨z,j,he⟩
      cases j
      · exact Or.inl (he.elim (fun h => Or.inl ⟨z,h.1,h.2⟩) (fun h => Or.inr ⟨z,h.1,h.2⟩))
      · exact Or.inr (he.elim (fun h => Or.inl ⟨z,h.1,h.2⟩) (fun h => Or.inr ⟨z,h.1,h.2⟩))
  have hAvoid (z : B) (j : Bool) : (e (z,j)).val ∉ U := fun h =>
    mem_compl.mp (e (z,j)).property (hUF h)
  refine ⟨e,P,sup_le hP₀ hP₁,?_,?_,?_,?_,fun z => ⟨hAdj z false,hAdj z true⟩,hSupport⟩
  · intro x y h
    obtain ⟨z,_,h|h⟩ := (hSupport x y).mp h
    · exact Or.inl (h.1 ▸ hBU z.property)
    · exact Or.inr (h.1 ▸ hBU z.property)
  · intro v hv
    let z : B := ⟨v,hv⟩
    let a := (e (z,false)).val
    let b := (e (z,true)).val
    have hab : a ≠ b := by
      intro h
      cases congrArg Prod.snd (e.injective (Subtype.ext h))
    have hE : P.neighborFinset v = {a,b} := by
      ext x
      rw [mem_neighborFinset,hSupport,mem_insert,mem_singleton]
      constructor
      · rintro ⟨w,j,h|h⟩
        · have he : w = z := Subtype.ext h.1.symm
          subst w
          cases j
          · exact Or.inl h.2
          · exact Or.inr h.2
        · exact (hAvoid w j (h.2 ▸ hBU hv)).elim
      · rintro (rfl|rfl)
        · exact ⟨z,false,Or.inl ⟨rfl,rfl⟩⟩
        · exact ⟨z,true,Or.inl ⟨rfl,rfl⟩⟩
    rw [←card_neighborFinset_eq_degree,hE,card_pair hab]
  · intro v hv hn
    by_contra hnD
    obtain ⟨x,hx⟩ := (P.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hnD)
    obtain ⟨z,j,h|h⟩ := (hSupport v x).mp hx
    · exact hn (h.1 ▸ z.property)
    · exact hAvoid z j (h.2 ▸ hv)
  · intro v hv
    rw [←card_neighborFinset_eq_degree]
    apply card_le_one.mpr
    intro a ha b hb
    have endpoint (x : V) (hx : x ∈ P.neighborFinset v) :
        ∃ z : B,∃ j : Bool,x = z.val ∧ v = (e (z,j)).val := by
      obtain ⟨z,j,h|h⟩ := (hSupport v x).mp ((mem_neighborFinset _ _ _).mp hx)
      · exact (hv (h.1 ▸ z.property)).elim
      · exact ⟨z,j,h⟩
    obtain ⟨z,j,ha',hz⟩ := endpoint a ha
    obtain ⟨w,k,hb',hw⟩ := endpoint b hb
    have he := congrArg Prod.fst (e.injective (Subtype.ext (hz.symm.trans hw)))
    exact ha'.trans ((congrArg Subtype.val he).trans hb'.symm)

end OverfullWork.CMSTrimmingRound
