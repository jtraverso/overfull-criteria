module

public import OverfullWork.LargeCentreCriticalGeometry
public import OverfullWork.LowVertexMatchingFlexibility

@[expose] public section


/-! # Critical independent vertices have a transversal avoiding one core vertex

VAL supplies strict Hall for any independent set of nonmaximum vertices,
not only the one-third low set. The actual avoiding transversal constructs
two disjoint cross edges for any two selected complementary vertices.
-/
namespace OverfullWork.CriticalIndependentPairMatching
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

theorem strict_column_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (Y : Finset V)
    (hNonmax : ∀y∈Y,G.degree y<G.maxDegree) {w v : V} (hwv : G.Adj w v) :
    ((G.neighborFinset v).filter fun z=>z∈Y).card<G.degree w := by
  let L:=(G.neighborFinset v).filter fun z=>z∈Y
  let C:=(G.neighborFinset v).filter fun z=>G.degree z=G.maxDegree
  have hDis:Disjoint L C:=Finset.disjoint_left.mpr (by
    intro z hzL hzC
    have hlt:=hNonmax z (mem_filter.mp hzL).2
    have heq:=(mem_filter.mp hzC).2
    omega)
  have hCard:=card_le_card (union_subset (filter_subset (fun z=>z∈Y) _)
    (filter_subset (fun z=>G.degree z=G.maxDegree) _) : L∪C⊆G.neighborFinset v)
  rw [card_union_of_disjoint hDis,card_neighborFinset_eq_degree] at hCard
  have hVal:=Gate8J2C.deficit_le_maximumNeighbours G hc hwv.symm
  change G.maxDegree-G.degree w+1≤C.card at hVal
  have hwD:=G.degree_le_maxDegree w
  have hvD:=G.degree_le_maxDegree v
  change L.card<G.degree w
  omega

theorem exists_transversal_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (Y : Finset V)
    (hInd : G.IsIndepSet (Y:Set V))
    (hNonmax : ∀y∈Y,G.degree y<G.maxDegree) (x : V) (hx : x∉Y) :
    ∃f : Y→↥(Yᶜ:Finset V),Function.Injective f ∧
      (∀y,G.Adj y.val (f y).val) ∧ ∀y,(f y).val≠x := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b=>Classical.propDecidable (G.Adj a b)))
  have hRow:∀a:Y,(univ.filter fun b:↥(Yᶜ:Finset V)=>G.Adj a.val b.val).card=G.degree a.val:=by
    intro a
    rw [DenseHall.subtype_filter_card,←card_neighborFinset_eq_degree]
    congr 1
    ext b
    simp only [mem_filter,mem_compl,mem_neighborFinset]
    constructor
    · exact fun h=>h.2
    · intro hab
      exact ⟨fun hb=>hInd a.property hb hab.ne hab,hab⟩
  have hCol:∀b:↥(Yᶜ:Finset V),(univ.filter fun a:Y=>G.Adj a.val b.val).card=
      ((G.neighborFinset b.val).filter fun z=>z∈Y).card:=by
    intro b
    have hCast:=DenseHall.subtype_filter_card Y (fun a=>G.Adj a b.val)
    calc
      _=(Y.filter fun a=>G.Adj a b.val).card:=by convert hCast using 1
      _=_:=by
        congr 1
        ext a
        simp only [mem_filter,mem_neighborFinset]
        exact ⟨fun h=>⟨h.2.symm,h.1⟩,fun h=>⟨h.2,h.1.symm⟩⟩
  obtain ⟨f,hf,hAdj,hAvoid⟩:=
    LowVertexMatchingFlexibility.exists_injection_avoiding_vertex_of_strict_degree_comparison
      (fun (a:Y) (b:↥(Yᶜ:Finset V))=>G.Adj a.val b.val)
      (by intro a;rw [hRow];have ht:=OddLowSmallCases.critical_two_le_degree G hc a.val;omega)
      (by intro a b hab;rw [hCol,hRow];exact strict_column_bound G hc Y hNonmax hab)
      ⟨x,mem_compl.mpr hx⟩
  refine ⟨f,hf,hAdj,?_⟩
  intro a he
  exact hAvoid a (Subtype.ext he)

/-- Every complementary vertex in a large-centre normalized cut is
nonmaximum: a second complementary vertex has critical degree at least two. -/
theorem complement_nonmaximum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x : V} (hx : x∈c.set) (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y)) :
    ∀y∈c.setᶜ,G.degree y<G.maxDegree := by
  have hTwo:=LargeCentreCriticalGeometry.two_le_complement_card G c hx hLarge
  intro y hy
  have hCard:(c.setᶜ.erase y).Nonempty:=by
    apply card_pos.mp
    rw [card_erase_of_mem hy]
    omega
  obtain ⟨z,hz⟩:=hCard
  have hLight:=c.light_pairs y hy z (mem_erase.mp hz).2 (mem_erase.mp hz).1.symm
  have hZ:=OddLowSmallCases.critical_two_le_degree G hc z
  omega

/-- The selected two cross edges are actual, disjoint, and avoid the
chosen core vertex. The selected complementary vertices are inputs;
their partners and all Hall data are constructed. -/
theorem exists_pair_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x : V} (hx : x∈c.set) (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y))
    (y z : V) (hy : y∈c.setᶜ) (hz : z∈c.setᶜ) (hyz : y≠z) :
    ∃a b : V,a∈c.set ∧ b∈c.set ∧ a≠x ∧ b≠x ∧ a≠b ∧ G.Adj y a ∧ G.Adj z b := by
  have hInd:G.IsIndepSet (↑(c.setᶜ):Set V):=by simpa only [coe_compl] using c.independent
  obtain ⟨f,hf,hAdj,hAvoid⟩:=exists_transversal_avoiding G hc c.setᶜ hInd
    (complement_nonmaximum G hc c hx hLarge) x (by simpa using hx)
  refine ⟨(f ⟨y,hy⟩).val,(f ⟨z,hz⟩).val,?_,?_,hAvoid _,hAvoid _,?_,hAdj ⟨y,hy⟩,hAdj ⟨z,hz⟩⟩
  · simpa only [mem_compl,not_not] using (f ⟨y,hy⟩).property
  · simpa only [mem_compl,not_not] using (f ⟨z,hz⟩).property
  · intro he
    exact hyz (congrArg Subtype.val (hf (Subtype.ext he)))

end OverfullWork.CriticalIndependentPairMatching
