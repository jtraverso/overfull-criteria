module

public import OverfullWork.PaperLowSkeleton

@[expose] public section


/-! # Odd skeleton with its actual matching and extra edge retained -/
namespace OverfullWork.OddLowSkeletonWitness
open SimpleGraph Finset Overfull LowVertexMatchingAbsorption PaperLowSkeleton
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- The odd construction retains the formula for the skeleton, rather
than hiding the added edge behind an existential graph. -/
theorem odd_skeleton_of_fresh_matching (G M : SimpleGraph V)
    [DecidableRel M.Adj] (W : Finset V) (hM : M≤G)
    (hm : OneFactor.IsMatchingGraph M)
    (hcover : ∀w∈W,∃!v,M.Adj w v)
    (hcrossM : ∀u v,M.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    {w b : V} (hw : w∈W) (hwbG : G.Adj w b) (hb : b∉W)
    (hbfresh : M.degree b=0) (hthree : 3≤W.card) (hOdd : Odd W.card) :
    IsSkeleton G (M⊔edge w b) W ∧
    (∀v∉W,(M⊔edge w b).degree v≤1) ∧
    (outerLeaves (M⊔edge w b) W).card=W.card+1 := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel M.Adj)
    (fun u v => Classical.propDecidable (M.Adj u v)))
  have hcount := matching_edge_count M W hcover hcrossM
  have hone : ∀w∈W,M.degree w=1 := fun w hw => degree_eq_one_iff_existsUnique_adj.mpr (hcover w hw)
  have habNe : w≠b := hwbG.ne
  have hnot : ¬M.Adj w b := by
    intro h
    have hp := (M.degree_pos_iff_exists_adj b).mpr ⟨w,h.symm⟩
    rw [hbfresh] at hp
    omega
  have hEdge : edge w b≤G := by
    intro u v huv
    rcases (edge_adj w b u v).mp huv with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩
    · exact hwbG
    · exact hwbG.symm
  let H := M⊔edge w b
  let : Fintype H.edgeSet := H.fintypeEdgeSet
  have hinc : ∀v,H.degree v=M.degree v+(if v=w ∨ v=b then 1 else 0) := by
    intro v
    exact matching_sup_edge_degree M habNe hnot v
  have hHG : H≤G := sup_le hM hEdge
  have hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W) := by
    intro u v huv
    rcases huv with h|h
    · exact hcrossM u v h
    · rcases (edge_adj w b u v).mp h with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩
      · exact Or.inl ⟨hw,hb⟩
      · exact Or.inr ⟨hw,hb⟩
  have hdeg : ∀v,H.degree v≤2 := by
    intro v
    rw [hinc]
    have hh := matching_degree_le_one M hm v
    split_ifs <;> omega
  have hpos : ∀w∈W,1≤H.degree w := by
    intro w hw
    rw [hinc,hone w hw]
    omega
  have hlowEq : (W.filter fun w => H.degree w=1)=W.erase w := by
    ext w
    simp only [mem_filter,mem_erase]
    constructor
    · intro h
      refine ⟨?_,h.1⟩
      intro he
      subst w
      have hh := hinc w
      rw [hone w hw,if_pos (Or.inl rfl)] at hh
      omega
    · intro h
      refine ⟨h.2,?_⟩
      have hwb : w≠b := fun he => hb (he ▸ h.2)
      rw [hinc,hone w h.2,if_neg (by tauto)]
  have hlowEnds : 2≤(W.filter fun w => H.degree w=1).card := by
    rw [hlowEq,card_erase_of_mem hw]
    omega
  have htwos : (Wᶜ.filter fun v => H.degree v=2).card≤1 := by
    have hsub : Wᶜ.filter (fun v => H.degree v=2)⊆{b} := by
      intro v hv
      obtain ⟨hvout,hvdeg⟩ := mem_filter.mp hv
      have hvnot := mem_compl.mp hvout
      have hvne : v≠w := fun he => hvnot (he ▸ hw)
      have hh := hinc v
      have hm := matching_degree_le_one M hm v
      have hveq : v=b := by
        by_contra hn
        rw [if_neg (by tauto)] at hh
        omega
      exact mem_singleton.mpr hveq
    simpa only [card_singleton] using card_le_card hsub
  have hE : H.edgeFinset.card=W.card+1 := by
    have hh := card_edgeFinset_sup_edge (G:=M) hnot habNe
    rw [hcount] at hh
    convert hh using 1
  have heven : Even H.edgeFinset.card := by
    obtain ⟨k,hk⟩ := hOdd
    exact ⟨k+1,by omega⟩
  have hlower : 2+2*(Wᶜ.filter fun v => H.degree v=2).card≤H.edgeFinset.card := by omega
  obtain ⟨houterEven,houterLow⟩ := outer_endpoint_budget H W hdeg hcross heven hlower
  have hout : ∀v∉W,H.degree v≤1 := by
    intro v hv
    rw [hinc]
    by_cases hvb : v=b
    · subst v
      rw [hbfresh,if_pos (Or.inr rfl)]
    · have hva : v≠w := fun he => hv (he ▸ hw)
      rw [if_neg (by tauto),Nat.add_zero]
      exact matching_degree_le_one M hm v
  have hbip : H.IsBipartiteWith (W:Set V) (↑(Wᶜ : Finset V):Set V) := by
    refine ⟨?_,?_⟩
    · apply Set.disjoint_left.mpr
      intro v hv hvout
      exact (mem_compl.mp hvout) hv
    · intro u v huv
      rcases hcross u v huv with h|h
      · exact Or.inl ⟨h.1,mem_compl.mpr h.2⟩
      · exact Or.inr ⟨mem_compl.mpr h.2,h.1⟩
  have htwoszero : (Wᶜ.filter fun v => H.degree v=2).card=0 := by
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_notMem
    intro v hv
    obtain ⟨hvout,hvd⟩:=mem_filter.mp hv
    have hh:=hout v (mem_compl.mp hvout)
    omega
  have houter : (outerLeaves H W).card=W.card+1 := by
    have hh:=isBipartiteWith_sum_degrees_eq_card_edges' hbip
    rw [outer_degree_sum H W hdeg,htwoszero,hE] at hh
    omega
  have hdis : Disjoint M (edge w b) := by
    apply disjoint_iff_inf_le.mpr
    intro u v ⟨hu,hv⟩
    rcases (edge_adj w b u v).mp hv with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩
    · exact (hnot hu).elim
    · exact (hnot hu.symm).elim
  have hedge : OneFactor.IsMatchingGraph (edge w b) := by
    intro u v z huv huz
    grind
  have hc := (two_matching_union_colouring M (edge w b) hm hedge hdis).1
  have hs : IsSkeleton G H W :=
    ⟨hHG,matching_sup_edge_isAcyclic M hm habNe hnot,hdeg,hpos,hlowEnds,
      houterEven,houterLow,hE.le,hcross,hc⟩
  exact ⟨hs,hout,houter⟩

/-- Criticality supplies a matching and a genuinely fresh additional edge.
The two outer anchors of the resulting three-edge component are retained
for the later separated pairing. -/
theorem exists_odd_low_skeleton (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : IsDeltaCritical G) (hthree : 3≤(lowVertices G).card)
    (hOdd : Odd (lowVertices G).card) :
    ∃(M : SimpleGraph V) (w a b : V),
      M≤G ∧ OneFactor.IsMatchingGraph M ∧
      (∀v∈lowVertices G,∃!u,M.Adj v u) ∧
      (∀u v,M.Adj u v → (u∈lowVertices G ∧ v∉lowVertices G) ∨
        (v∈lowVertices G ∧ u∉lowVertices G)) ∧
      w∈lowVertices G ∧ M.Adj w a ∧ b∉lowVertices G ∧ M.degree b=0 ∧ G.Adj w b ∧
      IsSkeleton G (M⊔edge w b) (lowVertices G) ∧
      (∀v∉lowVertices G,(M⊔edge w b).degree v≤1) ∧
      a∈outerLeaves (M⊔edge w b) (lowVertices G) ∧
      b∈outerLeaves (M⊔edge w b) (lowVertices G) ∧ a≠b ∧
      4≤(outerLeaves (M⊔edge w b) (lowVertices G)).card := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v)))
  let W := lowVertices G
  have hthreeW : 3≤W.card := hthree
  obtain ⟨w,hw⟩ := card_pos.mp (show 0<W.card by omega)
  obtain ⟨u,v,huv⟩ := MaximumCoreTwo.exists_adj_of_not_colorable G hcrit.2.1
  obtain ⟨b,hwb⟩ := MaximumCoreTwo.exists_adj_of_connected hcrit.1 huv w
  have hb : b∉W := by
    intro hbW
    have hwD := (mem_filter.mp hw).2
    have hbD := (mem_filter.mp hbW).2
    have hsum := Overfull.deg_add hcrit hwb
    omega
  let b₀ : ↥(Wᶜ : Finset V) := ⟨b,mem_compl.mpr hb⟩
  obtain ⟨f,hf,hfr,havoid⟩ :=
    LowVertexMatchingFlexibility.exists_low_selection_avoiding_vertex G hcrit b₀
  let M := selectionGraph W f
  have hM : M≤G := selectionGraph_le W f hfr
  obtain ⟨hm,hcover⟩ := selectionGraph_isMatching W f hf
  have hcross : ∀u v,M.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W) :=
    fun _ _ h => selectionGraph_crosses_cut W f h
  have hbfresh : M.degree b=0 := by
    rw [←card_neighborFinset_eq_degree,card_eq_zero]
    apply eq_empty_of_forall_notMem
    intro z hz
    have hadj : M.Adj b z := (mem_neighborFinset _ _ _).mp hz
    rcases hadj with ⟨s,hs,_⟩|⟨s,_,hs⟩
    · exact hb (hs ▸ s.property)
    · exact havoid s (Subtype.ext hs.symm)
  obtain ⟨a,hwa,_⟩ := hcover w hw
  have ha : a∉W := by
    rcases hcross w a hwa with h|h
    · exact h.2
    · exact (h.2 hw).elim
  have hab : a≠b := by
    intro he
    subst a
    have hp := (M.degree_pos_iff_exists_adj b).mpr ⟨w,hwa.symm⟩
    omega
  have hnot : ¬M.Adj w b := by
    intro hh
    have hp := (M.degree_pos_iff_exists_adj b).mpr ⟨w,hh.symm⟩
    omega
  have hwaNe : a≠w := fun he => ha (he ▸ hw)
  have hdegA : M.degree a=1 :=
    degree_eq_one_iff_existsUnique_adj.mpr
      ⟨w,hwa.symm,fun z hz => hm a z w hz hwa.symm⟩
  have hanchorA : a∈outerLeaves (M⊔edge w b) W := by
    apply mem_filter.mpr
    refine ⟨mem_compl.mpr ha,?_⟩
    rw [matching_sup_edge_degree M hwb.ne hnot,hdegA,if_neg (by tauto)]
  have hanchorB : b∈outerLeaves (M⊔edge w b) W := by
    apply mem_filter.mpr
    refine ⟨mem_compl.mpr hb,?_⟩
    rw [matching_sup_edge_degree M hwb.ne hnot,hbfresh,if_pos (Or.inr rfl)]
  obtain ⟨hs,hout,hcard⟩ := odd_skeleton_of_fresh_matching G M W hM hm hcover hcross
    hw hwb hb hbfresh hthreeW hOdd
  refine ⟨M,w,a,b,hM,hm,hcover,hcross,hw,hwa,hb,hbfresh,hwb,hs,hout,
    hanchorA,hanchorB,hab,?_⟩
  change 4≤(outerLeaves (M⊔edge w b) W).card
  rw [hcard]
  omega

end OverfullWork.OddLowSkeletonWitness
