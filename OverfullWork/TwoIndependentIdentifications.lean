module

public import OverfullWork.EdgeImageFibreDegree

@[expose] public section


/-! The actual two identifications in CMS §4, Subcase 2.4.
Original edges remain distinct labelled copies, including parallel images.
The two exceptional groups are subsets of one independent set. -/
namespace OverfullWork.TwoIndependentIdentifications
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

abbrev Outside (Z : Finset V) := {v : V // v ∉ Z}
abbrev Vertices (Z : Finset V) := Sum Bool (Outside Z)

def vertexMap (Z A : Finset V) (v : V) : Vertices Z :=
  if hz : v ∈ Z then Sum.inl (if v ∈ A then false else true) else Sum.inr ⟨v,hz⟩

def part (Z A : Finset V) (i : Bool) : Finset V := if i then Z\A else A

omit [Fintype V] in
@[simp] theorem map_eq_inl (Z A : Finset V) (hA : A ⊆ Z) (v : V) (i : Bool) :
    vertexMap Z A v=Sum.inl i ↔ v ∈ part Z A i := by
  have hh : v ∈ A → v ∈ Z := fun h => hA h
  cases i <;> by_cases hz : v ∈ Z <;> by_cases ha : v ∈ A <;>
    simp_all [vertexMap,part]

omit [Fintype V] in
@[simp] theorem map_eq_inr (Z A : Finset V) (v : V) (x : Outside Z) :
    vertexMap Z A v=Sum.inr x ↔ v=x.val := by
  rcases x with ⟨x,hx⟩
  by_cases hz : v ∈ Z
  · have hvx : v ≠ x := fun h => hx (h ▸ hz)
    simp [vertexMap,hz,hvx]
  · simp [vertexMap,hz]

omit [Fintype V] in
theorem part_subset (Z A : Finset V) (hA : A ⊆ Z) (i : Bool) : part Z A i ⊆ Z := by
  cases i
  · exact hA
  · exact sdiff_subset

omit [Fintype V] in
theorem map_loopless (G : SimpleGraph V) (Z A : Finset V) (hA : A ⊆ Z)
    (hind : G.IsIndepSet (Z:Set V)) :
    ∀ a b, G.Adj a b → vertexMap Z A a ≠ vertexMap Z A b := by
  intro a b hab he
  by_cases ha : a ∈ Z
  · have hb : b ∈ Z := by
      by_contra hb
      simp only [vertexMap,dif_pos ha,dif_neg hb,Sum.inl_ne_inr] at he
    exact hind ha hb hab.ne hab
  · have hb : b ∉ Z := by
      intro hb
      simp only [vertexMap,dif_neg ha,dif_pos hb,Sum.inr_ne_inl] at he
    have hab' : a=b := by
      simpa only [vertexMap,dif_neg ha,dif_neg hb,Sum.inr.injEq,Subtype.mk.injEq] using he
    exact hab.ne hab'

noncomputable def graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V)) : MultiGraph (Vertices Z) :=
  EdgeImage.graph G (vertexMap Z A) (map_loopless G Z A hA hind)

theorem degree_inl (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V)) (i : Bool) :
    (graph G Z A hA hind).degree (Sum.inl i)=∑ v ∈ part Z A i, G.degree v :=
  EdgeImage.degree_of_fibre G (vertexMap Z A) (map_loopless G Z A hA hind)
    (Sum.inl i) (part Z A i) (fun v => map_eq_inl Z A hA v i)

theorem degree_inr (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V)) (x : Outside Z) :
    (graph G Z A hA hind).degree (Sum.inr x)=G.degree x.val := by
  rw [graph,EdgeImage.degree_eq,←PairIdentification.source_incidence_card G x.val]
  congr 1
  ext e
  simp only [mem_filter,mem_univ,true_and,Sym2.mem_map,map_eq_inr]
  exact ⟨fun ⟨a,ha,he⟩ => he ▸ ha,fun h => ⟨x.val,h,rfl⟩⟩

theorem colourable_of_identifications (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V)) {D : ℕ}
    (C : (graph G Z A hA hind).EdgeColoring D) : G.EdgeColorable D :=
  EdgeImage.colourable_of_image_colouring G (vertexMap Z A) (map_loopless G Z A hA hind) C

theorem card_vertices (Z : Finset V) : Fintype.card (Vertices Z)=Zᶜ.card+2 := by
  have e : Outside Z ≃ ↥(Zᶜ : Finset V) :=
    { toFun:=fun x=>⟨x.val,mem_compl.mpr x.property⟩
      invFun:=fun x=>⟨x.val,mem_compl.mp x.property⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  have hc : Fintype.card (Outside Z)=Zᶜ.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  rw [Fintype.card_sum,Fintype.card_bool,hc]
  omega

theorem even_card_vertices (Z : Finset V) (heven : Even Zᶜ.card) :
    Even (Fintype.card (Vertices Z)) := by
  rw [card_vertices]
  obtain ⟨k,hk⟩ := heven
  exact ⟨k+1,by omega⟩

end OverfullWork.TwoIndependentIdentifications
