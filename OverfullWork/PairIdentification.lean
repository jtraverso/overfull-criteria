module

public import OverfullWork.EdgeImageMultigraph
public import OverfullWork.CentreControl

@[expose] public section


/-! # Identifying two nonadjacent vertices

The removed vertex is mapped to the retained vertex. The auxiliary object
is the actual fibre-count multigraph, on one fewer vertex. Degrees and
colouring transfer are proved from its construction.
-/
namespace OverfullWork.PairIdentification
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

abbrev Vertices (v : V) := {w : V // w≠v}

def centre (u v : V) (huv : u≠v) : Vertices v := ⟨u,huv⟩

def vertexMap (u v : V) (huv : u≠v) (a : V) : Vertices v :=
  if h : a=v then ⟨u,huv⟩ else ⟨a,h⟩

@[simp] theorem map_eq_centre (u v : V) (huv : u≠v) (a : V) :
    vertexMap u v huv a=centre u v huv ↔ a=u ∨ a=v := by
  by_cases ha : a=v <;> simp [vertexMap,centre,ha]

theorem map_eq_other (u v : V) (huv : u≠v) (a : V) (w : Vertices v)
    (hw : w.val≠u) : vertexMap u v huv a=w ↔ a=w.val := by
  rcases w with ⟨w,hwv⟩
  by_cases ha : a=v
  · simp [vertexMap,ha,Ne.symm hw,Ne.symm hwv]
  · simp [vertexMap,ha]

theorem map_loopless (G : SimpleGraph V) (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) :
    ∀a b,G.Adj a b → vertexMap u v huv a≠vertexMap u v huv b := by
  intro a b hab he
  by_cases ha : a=v
  · subst a
    have hb : b=u ∨ b=v := (map_eq_centre u v huv b).mp (by simpa [vertexMap,centre] using he.symm)
    rcases hb with rfl|rfl
    · exact hnon hab.symm
    · exact G.ne_of_adj hab rfl
  · by_cases hb : b=v
    · subst b
      have hh : a=u ∨ a=v := (map_eq_centre u v huv a).mp (by simpa [vertexMap,centre] using he)
      rcases hh with rfl|hh
      · exact hnon hab
      · exact ha hh
    · have hab' : a=b := by simpa only [vertexMap,dif_neg ha,dif_neg hb,Subtype.mk.injEq] using he
      exact (G.ne_of_adj hab) hab'

noncomputable def graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) : MultiGraph (Vertices v) :=
  EdgeImage.graph G (vertexMap u v huv) (map_loopless G u v huv hnon)

theorem source_incidence_card (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) :
    (univ.filter fun e : G.edgeSet => a∈e.val).card=G.degree a := by
  rw [←G.card_incidenceFinset_eq_degree a]
  apply card_bij (fun e _ => e.val)
  · intro e he
    exact (G.mem_incidenceFinset a e.val).mpr
      ((G.edge_mem_incidenceSet_iff).mpr (mem_filter.mp he).2)
  · intro e _ f _ hef
    exact Subtype.ext hef
  · intro e he
    have hi : e∈G.incidenceSet a:=(G.mem_incidenceFinset a e).mp he
    exact ⟨⟨e,hi.1⟩,mem_filter.mpr ⟨mem_univ _,hi.2⟩,rfl⟩

theorem degree_centre (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) :
    (graph G u v huv hnon).degree (centre u v huv)=G.degree u+G.degree v := by
  rw [graph,EdgeImage.degree_eq]
  have heq : (univ.filter fun a : G.edgeSet => centre u v huv∈Sym2.map (vertexMap u v huv) a.val)=
      (univ.filter fun a : G.edgeSet => u∈a.val)∪(univ.filter fun a : G.edgeSet => v∈a.val) := by
    ext a
    simp only [mem_filter,mem_univ,true_and,mem_union,Sym2.mem_map,map_eq_centre]
    constructor
    · rintro ⟨b,hb,hbu|hbv⟩ <;> subst b <;> tauto
    · rintro (hu|hv)
      · exact ⟨u,hu,Or.inl rfl⟩
      · exact ⟨v,hv,Or.inr rfl⟩
  have hdis : Disjoint (univ.filter fun a : G.edgeSet => u∈a.val)
      (univ.filter fun a : G.edgeSet => v∈a.val) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hai : a.val∈G.incidenceSet u:=⟨a.property,(mem_filter.mp ha).2⟩
    have hbi : a.val∈G.incidenceSet v:=⟨a.property,(mem_filter.mp hb).2⟩
    exact hnon (G.adj_of_mem_incidenceSet huv hai hbi)
  rw [heq,card_union_of_disjoint hdis,source_incidence_card,source_incidence_card]

theorem degree_other (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) (w : Vertices v) (hw : w.val≠u) :
    (graph G u v huv hnon).degree w=G.degree w.val := by
  rw [graph,EdgeImage.degree_eq,←source_incidence_card G w.val]
  congr 1
  ext a
  simp only [mem_filter,mem_univ,true_and,Sym2.mem_map,map_eq_other u v huv _ w hw]
  exact ⟨fun ⟨b,hb,he⟩ => he ▸ hb,fun h => ⟨w.val,h,rfl⟩⟩

/-- The sum-degree condition is precisely what is needed at the merged
vertex; all remaining degrees are unchanged. -/
theorem degree_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) (D : ℕ)
    (hdegree : ∀w,G.degree w≤D) (hsum : G.degree u+G.degree v≤D) :
    ∀w,(graph G u v huv hnon).degree w≤D := by
  intro w
  by_cases hw : w.val=u
  · have he : w=centre u v huv:=Subtype.ext hw
    rw [he,degree_centre]
    exact hsum
  · rw [degree_other G u v huv hnon w hw]
    exact hdegree w.val

theorem colourable_of_identification (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) {D : ℕ}
    (C : (graph G u v huv hnon).EdgeColoring D) : G.EdgeColorable D :=
  EdgeImage.colourable_of_image_colouring G (vertexMap u v huv) (map_loopless G u v huv hnon) C

theorem card_vertices (v : V) : Fintype.card (Vertices v)+1=Fintype.card V := by
  have hcard : Fintype.card (Vertices v)=(univ.erase v).card := by
    have e : Vertices v ≃ ↥(univ.erase v : Finset V) :=
      { toFun := fun w => ⟨w.val,by simp [w.property]⟩
        invFun := fun w => ⟨w.val,by simpa using (mem_erase.mp w.property).1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  rw [hcard,card_erase_of_mem (mem_univ v),card_univ]
  have hn : 0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨v⟩
  omega

end OverfullWork.PairIdentification
