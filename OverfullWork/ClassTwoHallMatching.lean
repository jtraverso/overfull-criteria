module

public import OverfullWork.PaperFirstRoundAboveHalf

@[expose] public section


/-! # Matching across an independent cut from restored Hall inequalities

Only the actual neighbour counts, independence and positive selected
degrees are used. No criticality assumption is made. Isolated vertices
of the complementary set are allowed and are not assigned partners.
-/
namespace OverfullWork.ClassTwoHallMatching
open SimpleGraph Finset PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem exists_transversal_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (hInd : G.IsIndepSet (W:Set V))
    (hPos : ∀w∈W,0<G.degree w)
    (hHall : ∀w∈W,∀v,G.Adj w v → neighboursIn G W v<G.degree w)
    (x : V) (hx : x∉W) :
    ∃f : W→↥(Wᶜ:Finset V),Function.Injective f ∧
      (∀w,G.Adj w.val (f w).val) ∧ ∀w,(f w).val≠x := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b=>Classical.propDecidable (G.Adj a b)))
  have hRow:∀a:W,(univ.filter fun b:↥(Wᶜ:Finset V)=>G.Adj a.val b.val).card=G.degree a.val:=by
    intro a
    rw [DenseHall.subtype_filter_card,←card_neighborFinset_eq_degree]
    congr 1
    ext b
    simp only [mem_filter,mem_compl,mem_neighborFinset]
    constructor
    · exact fun h=>h.2
    · intro hab
      exact ⟨fun hb=>hInd a.property hb hab.ne hab,hab⟩
  have hCol:∀b:↥(Wᶜ:Finset V),(univ.filter fun a:W=>G.Adj a.val b.val).card=
      neighboursIn G W b.val:=by
    intro b
    have hCast:=DenseHall.subtype_filter_card W (fun a=>G.Adj a b.val)
    calc
      _=(W.filter fun a=>G.Adj a b.val).card:=by convert hCast using 1
      _=_:=by
        rw [RobustExpansion.neighboursIn_eq_filter_card]
        congr 1
        ext a
        simp only [mem_filter,G.adj_comm]
  obtain ⟨f,hf,hAdj,hAvoid⟩:=
    LowVertexMatchingFlexibility.exists_injection_avoiding_vertex_of_strict_degree_comparison
      (fun (a:W) (b:↥(Wᶜ:Finset V))=>G.Adj a.val b.val)
      (by intro a;rw [hRow];exact hPos a.val a.property)
      (by intro a b hab;rw [hCol,hRow];exact hHall a.val a.property b.val hab)
      ⟨x,mem_compl.mpr hx⟩
  refine ⟨f,hf,hAdj,?_⟩
  intro a he
  exact hAvoid a (Subtype.ext he)

theorem exists_pair_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hInd : G.IsIndepSet (Y:Set V))
    (hHall : ∀w∈Y,∀v,G.Adj w v → neighboursIn G Y v<G.degree w)
    (x y z : V) (hx : x∉Y) (hy : y∈Y) (hz : z∈Y) (hyz : y≠z)
    (hyPos : 0<G.degree y) (hzPos : 0<G.degree z) :
    ∃a b,a∈Yᶜ ∧ b∈Yᶜ ∧ a≠x ∧ b≠x ∧ a≠b ∧ G.Adj y a ∧ G.Adj z b := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b=>Classical.propDecidable (G.Adj a b)))
  let W:Finset V:={y,z}
  have hWY:W⊆Y:=by intro w hw;rcases mem_insert.mp hw with he|he;exact he ▸ hy;exact mem_singleton.mp he ▸ hz
  have hWInd:G.IsIndepSet (W:Set V):=by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab hAdj
    exact hInd (hWY ha) (hWY hb) hab hAdj
  have hWPos:∀w∈W,0<G.degree w:=by
    intro w hw
    rcases mem_insert.mp hw with he|he
    · exact he ▸ hyPos
    · exact mem_singleton.mp he ▸ hzPos
  have hWHall:∀w∈W,∀v,G.Adj w v → neighboursIn G W v<G.degree w:=by
    intro w hw v hAdj
    have hSub:(G.neighborFinset v).filter (fun u=>u∈W)⊆
        (G.neighborFinset v).filter (fun u=>u∈Y):=by
      intro u hu
      exact mem_filter.mpr ⟨(mem_filter.mp hu).1,hWY (mem_filter.mp hu).2⟩
    exact (card_le_card hSub).trans_lt (hHall w (hWY hw) v hAdj)
  obtain ⟨f,hf,hAdj,hAvoid⟩:=exists_transversal_avoiding G W hWInd hWPos hWHall x (fun hh=>hx (hWY hh))
  let a:=(f ⟨y,by simp [W]⟩).val
  let b:=(f ⟨z,by simp [W]⟩).val
  have hya:G.Adj y a:=hAdj ⟨y,by simp [W]⟩
  have hzb:G.Adj z b:=hAdj ⟨z,by simp [W]⟩
  refine ⟨a,b,?_,?_,hAvoid _,hAvoid _,?_,hya,hzb⟩
  · exact mem_compl.mpr (fun ha=>hInd hy ha hya.ne hya)
  · exact mem_compl.mpr (fun hb=>hInd hz hb hzb.ne hzb)
  · intro he
    exact hyz (congrArg Subtype.val (hf (Subtype.ext he)))

theorem top_pair_positive (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) {y z : V} (hTop : PaperTopDegreeMatching.IsTopPair G Y y z)
    (hActive : 2≤(Y.filter fun w=>0<G.degree w).card) :
    0<G.degree y ∧ 0<G.degree z := by
  obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp (show 1<(Y.filter fun w=>0<G.degree w).card by omega)
  have haY:=(mem_filter.mp ha).1
  have hbY:=(mem_filter.mp hb).1
  have haPos:=(mem_filter.mp ha).2
  have hbPos:=(mem_filter.mp hb).2
  constructor
  · exact haPos.trans_le (hTop.maximum a haY)
  · by_cases hay:a=y
    · exact hbPos.trans_le (hTop.second b hbY (fun he=>hab (hay.trans he.symm)))
    · exact haPos.trans_le (hTop.second a haY hay)

end OverfullWork.ClassTwoHallMatching
