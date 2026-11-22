module

public import OverfullWork.NormalizedTerminalAboveHalf
public import OverfullWork.MaximumCoreDegree

@[expose] public section


/-! # Exact degree information for applying the registered literature

These consequences refer to the actual normalized terminal source graph.
They prevent confusing a dense maximum-degree core with a core of
induced maximum degree two, or maximum-degree density with the
minimum-degree hypotheses of Plantholt–Shan. They do not exclude
applications after a further proved graph transformation.
-/
namespace OverfullWork.NormalizedTerminalLiteratureBridge
open SimpleGraph Finset NormalizedAlmostStoppingRun NormalizedClassTwoStep
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At most K neighbours lie outside a selected all-maximum core. -/
theorem maximum_core_degree_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K)
    (hCore : ∀v∈c.set,G.degree v=G.maxDegree) :
    G.maxDegree≤Gate8J2C.maximumCoreDegree G+K := by
  have hpos:0<c.set.card:=by obtain ⟨i,hi⟩:=c.odd;omega
  obtain ⟨x,hx⟩:=card_pos.mp hpos
  have hsub:G.neighborFinset x⊆
      ((G.neighborFinset x).filter fun v=>G.degree v=G.maxDegree)∪c.setᶜ:=by
    intro v hv
    by_cases hvc:v∈c.set
    · exact mem_union_left _ (mem_filter.mpr ⟨hv,hCore v hvc⟩)
    · exact mem_union_right _ (mem_compl.mpr hvc)
  have hc:=(card_le_card hsub).trans (card_union_le _ _)
  have hcount:Gate8J2C.maximumNeighbours G x≤Gate8J2C.maximumCoreDegree G:=
    Gate8J2C.maximumNeighbours_le_coreDegree G x (hCore x hx)
  have hdegree:(G.neighborFinset x).card=G.maxDegree:=by
    rw [G.card_neighborFinset_eq_degree,hCore x hx]
  have hY:=c.complement_small
  change (G.neighborFinset x).card≤Gate8J2C.maximumNeighbours G x+c.setᶜ.card at hc
  omega

theorem all_maximum_core_degree_gt_two {B K : ℕ} (s : State V B K)
    (hM : Margins s) (hCore : ∀v∈s.cut.set,s.graph.degree v=s.graph.maxDegree) :
    2<Gate8J2C.maximumCoreDegree s.graph := by
  have hh:=maximum_core_degree_lower s.graph s.cut hCore
  have hD:=hM.2.2
  omega

/-- The second-low-core branch forces the merged complementary degree
and the anchor degree to be at most the small budget. -/
theorem second_low_degree_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x v : V} (hx : x∈c.set)
    (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y))
    (hv : v∈c.set) (hvx : v≠x) (hLow : G.degree v≤G.maxDegree-G.degree x) :
    (∑y∈c.setᶜ,G.degree y)≤B ∧ G.degree x<B ∧ G.minDegree<B := by
  have hb:=LargeCentreCriticalGeometry.anchor_degree_add_excess_le G c hx hLarge hv hvx hLow
  have hmin:=G.minDegree_le_degree x
  omega

/-- In the actual second-low terminal source the minimum degree is
below one quarter of the order, rather than above one half. -/
theorem second_low_minimum_sparse {B K : ℕ} (s : State V B K) (hM : Margins s)
    {x v : V} (hx : x∈s.cut.set)
    (hLarge : s.graph.degree x<(∑y∈s.cut.setᶜ,s.graph.degree y))
    (hv : v∈s.cut.set) (hvx : v≠x)
    (hLow : s.graph.degree v≤s.graph.maxDegree-s.graph.degree x) :
    4*s.graph.minDegree<Fintype.card V := by
  have hb:=(second_low_degree_bounds s.graph s.cut hx hLarge hv hvx hLow).2.2
  have : Nonempty V:=⟨x⟩
  have hn:=s.graph.maxDegree_lt_card_verts
  have hD:=hM.2.2
  omega

end OverfullWork.NormalizedTerminalLiteratureBridge
