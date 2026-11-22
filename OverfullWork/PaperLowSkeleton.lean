module

public import OverfullWork.LowVertexMatchingFlexibility
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section


/-! # The low-vertex skeleton in CMS Operation 4.1, Step 2, Case S2.1

For an even low set take the first matching. For an odd low set of size
at least three add just one edge of the second matching. This produces
an actual linear forest with a positive even number of outside endpoints.
It does not require an acyclic union of the two full matchings.
-/
namespace OverfullWork.PaperLowSkeleton
open SimpleGraph Finset Overfull
open LowVertexMatchingAbsorption
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

noncomputable def outerLeaves (H : SimpleGraph V) [DecidableRel H.Adj] (W : Finset V) : Finset V :=
  Wᶜ.filter fun v => H.degree v=1

/-- An actual path skeleton and its endpoint and edge budgets. -/
structure IsSkeleton (G H : SimpleGraph V) [DecidableRel H.Adj] (W : Finset V) : Prop where
  le_graph : H≤G
  acyclic : H.IsAcyclic
  degree_le_two : ∀v,H.degree v≤2
  low_positive : ∀w∈W,1≤H.degree w
  low_endpoints : 2≤(W.filter fun w => H.degree w=1).card
  outer_even : Even (outerLeaves H W).card
  outer_two_le : 2≤(outerLeaves H W).card
  edge_bound : H.edgeFinset.card≤W.card+1
  crosses : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W)
  colourable : H.EdgeColorable 2

omit [Fintype V] [DecidableEq V] in
/-- A matching has no cycle: the first and last neighbours of a cycle
would have to be equal. -/
theorem matching_isAcyclic (M : SimpleGraph V) (hm : OneFactor.IsMatchingGraph M) : M.IsAcyclic := by
  intro v p hp
  exact hp.snd_ne_penultimate (hm v p.snd p.penultimate
    (p.adj_snd hp.not_nil) (p.adj_penultimate hp.not_nil).symm)

omit [Fintype V] [DecidableEq V] in
/-- A matching component has at most two vertices. -/
theorem matching_reachable_eq_or_adj (M : SimpleGraph V) (hm : OneFactor.IsMatchingGraph M)
    {u v : V} (hr : M.Reachable u v) : u=v ∨ M.Adj u v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact Or.inl rfl
  | @cons a b c hab p ih =>
    rcases ih with he|hbc
    · subst c
      exact Or.inr hab
    · exact Or.inl (hm b a c hab.symm hbc)

omit [Fintype V] [DecidableEq V] in
/-- Adding any new nonloop edge to a matching is still a forest. -/
theorem matching_sup_edge_isAcyclic (M : SimpleGraph V) (hm : OneFactor.IsMatchingGraph M)
    {a b : V} (hab : a≠b) (hnot : ¬M.Adj a b) : (M⊔edge a b).IsAcyclic := by
  apply (matching_isAcyclic M hm).sup_edge_of_not_reachable
  intro hr
  exact (matching_reachable_eq_or_adj M hm hr).elim hab hnot

omit [DecidableEq V] in
/-- Every vertex of a matching has degree at most one. -/
theorem matching_degree_le_one (M : SimpleGraph V) [DecidableRel M.Adj]
    (hm : OneFactor.IsMatchingGraph M) (v : V) : M.degree v≤1 := by
  rw [←card_neighborFinset_eq_degree]
  exact card_le_one.mpr (fun a ha b hb => hm v a b
    ((mem_neighborFinset _ _ _).mp ha) ((mem_neighborFinset _ _ _).mp hb))

private theorem bipartite_of_crosses (H : SimpleGraph V) (W : Finset V)
    (hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W)) :
    H.IsBipartiteWith (W:Set V) (↑(Wᶜ : Finset V):Set V) := by
  refine ⟨?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro v hv hw
    exact (mem_compl.mp hw) hv
  · intro u v huv
    rcases hcross u v huv with h|h
    · exact Or.inl ⟨h.1,mem_compl.mpr h.2⟩
    · exact Or.inr ⟨mem_compl.mpr h.2,h.1⟩

/-- The number of outside endpoints is determined by the outside degree
sum: all other positive outside degrees equal two. -/
theorem outer_degree_sum (H : SimpleGraph V) [DecidableRel H.Adj] (W : Finset V)
    (hdeg : ∀v,H.degree v≤2) :
    (∑v∈Wᶜ,H.degree v)=(outerLeaves H W).card+
      2*(Wᶜ.filter fun v => H.degree v=2).card := by
  have hp : ∀v∈Wᶜ,H.degree v=(if H.degree v=1 then 1 else 0)+(if H.degree v=2 then 2 else 0) := by
    intro v _
    have := hdeg v
    split_ifs <;> omega
  rw [sum_congr rfl hp,sum_add_distrib]
  rw [←sum_filter,←sum_filter,sum_const,sum_const,Nat.nsmul_eq_mul,Nat.nsmul_eq_mul,mul_one]
  change (outerLeaves H W).card+_=_
  omega

/-- A matching crossing the cut and saturating W has exactly |W| edges. -/
theorem matching_edge_count (M : SimpleGraph V) [DecidableRel M.Adj] (W : Finset V)
    (hcover : ∀w∈W,∃!v,M.Adj w v)
    (hcross : ∀u v,M.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W)) :
    M.edgeFinset.card=W.card := by
  have hc := isBipartiteWith_sum_degrees_eq_card_edges (bipartite_of_crosses M W hcross)
  have hw : ∀w∈W,M.degree w=1 := fun w hw => degree_eq_one_iff_existsUnique_adj.mpr (hcover w hw)
  rw [sum_congr rfl hw,sum_const,Nat.nsmul_eq_mul,mul_one] at hc
  exact hc.symm

/-- Edge counts and the number of outside double vertices yield the
required even, positive endpoint set. -/
theorem outer_endpoint_budget (H : SimpleGraph V) [DecidableRel H.Adj] (W : Finset V)
    (hdeg : ∀v,H.degree v≤2)
    (hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (heven : Even H.edgeFinset.card)
    (hlower : 2+2*(Wᶜ.filter fun v => H.degree v=2).card≤H.edgeFinset.card) :
    Even (outerLeaves H W).card ∧ 2≤(outerLeaves H W).card := by
  have hs := isBipartiteWith_sum_degrees_eq_card_edges' (bipartite_of_crosses H W hcross)
  rw [outer_degree_sum H W hdeg] at hs
  constructor
  · obtain ⟨k,hk⟩ := heven
    exact ⟨k-(Wᶜ.filter fun v => H.degree v=2).card,by omega⟩
  · omega

/-- The local degree increment from one new edge. -/
theorem matching_sup_edge_degree (M : SimpleGraph V) [DecidableRel M.Adj]
    {a b : V} (hab : a≠b) (hnot : ¬M.Adj a b) (v : V) :
    (M⊔edge a b).degree v=M.degree v+(if v=a ∨ v=b then 1 else 0) := by
  have hdis : Disjoint M (edge a b) := by
    apply disjoint_iff_inf_le.mpr
    intro u w ⟨hu,hw⟩
    have hh := (edge_adj a b u w).mp hw
    rcases hh.1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (hnot hu).elim
    · exact (hnot hu.symm).elim
  have he : (edge a b).degree v=if v=a ∨ v=b then 1 else 0 := by
    by_cases hva : v=a
    · subst v
      rw [if_pos (Or.inl rfl),←card_neighborFinset_eq_degree]
      have hn : (edge a b).neighborFinset a={b} := by ext w;simp +contextual [edge_adj,hab]
      rw [hn,card_singleton]
    · by_cases hvb : v=b
      · subst v
        rw [if_pos (Or.inr rfl),←card_neighborFinset_eq_degree]
        have hn : (edge a b).neighborFinset b={a} := by ext w;simp +contextual [edge_adj,hab.symm]
        rw [hn,card_singleton]
      · rw [if_neg (by tauto),←card_neighborFinset_eq_degree]
        have hn : (edge a b).neighborFinset v=∅ := by ext w;simp [edge_adj,hva,hvb]
        rw [hn,card_empty]
  rw [←card_neighborFinset_eq_degree,neighborFinset_sup,
    card_union_of_disjoint (disjoint_neighborFinset_of_disjoint M (edge a b) v hdis),
    card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,he]

/-- The outside endpoints fit in the same |W|+1 budget as the edges. -/
theorem IsSkeleton.outer_card_le {G H : SimpleGraph V} [DecidableRel H.Adj] {W : Finset V}
    (h : IsSkeleton G H W) : (outerLeaves H W).card≤W.card+1 := by
  have hs := isBipartiteWith_sum_degrees_eq_card_edges' (bipartite_of_crosses H W h.crosses)
  rw [outer_degree_sum H W h.degree_le_two] at hs
  have hb := h.edge_bound
  omega

/-- Every outside endpoint has a real low neighbour in the original graph. -/
theorem IsSkeleton.outer_neighbour {G H : SimpleGraph V} [DecidableRel H.Adj] {W : Finset V}
    (h : IsSkeleton G H W) {a : V} (ha : a∈outerLeaves H W) :
    ∃w∈W,G.Adj w a := by
  obtain ⟨haout,hadeg⟩ := mem_filter.mp ha
  have hanot := mem_compl.mp haout
  obtain ⟨w,haw⟩ := (H.degree_pos_iff_exists_adj a).mp (by omega)
  rcases h.crosses a w haw with ⟨haW,_⟩|⟨hwW,_⟩
  · exact False.elim (hanot haW)
  · exact ⟨w,hwW,(h.le_graph haw).symm⟩

/-- A matching takes one actual edge colour. -/
private theorem matching_colourable_one (M : SimpleGraph V) (hm : OneFactor.IsMatchingGraph M) :
    M.EdgeColorable 1 := by
  classical
  have hbot : (⊥ : SimpleGraph V).EdgeColorable 0 := by
    have : IsEmpty (⊥ : SimpleGraph V).edgeSet := ⟨fun e => by simpa using e.property⟩
    exact Colorable.of_isEmpty 0
  have hh : ((⊥ : SimpleGraph V)⊔M).EdgeColorable 1 :=
    OneFactor.colorable_sup_matching disjoint_bot_left hm hbot
  exact Critical.colourable_of_copy (Copy.ofLE M (⊥⊔M) le_sup_right) hh

private theorem matching_sup_edge_colourable (M : SimpleGraph V) (hm : OneFactor.IsMatchingGraph M)
    {a b : V} (hnot : ¬M.Adj a b) : (M⊔edge a b).EdgeColorable 2 := by
  have hdis : Disjoint M (edge a b) := by
    apply disjoint_iff_inf_le.mpr
    intro u v ⟨hu,hv⟩
    rcases (edge_adj a b u v).mp hv with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩
    · exact (hnot hu).elim
    · exact (hnot hu.symm).elim
  have hedge : OneFactor.IsMatchingGraph (edge a b) := by
    intro u v w huv huw
    grind
  exact OneFactor.colorable_sup_matching hdis hedge (matching_colourable_one M hm)

/-- In the even case the chosen skeleton is the matching itself. -/
theorem isSkeleton_of_even_matching (G M : SimpleGraph V) [DecidableRel M.Adj]
    (W : Finset V) (hLe : M ≤ G) (hm : OneFactor.IsMatchingGraph M)
    (hCover : ∀ w ∈ W,∃! v,M.Adj w v)
    (hCross : ∀ u v,M.Adj u v → (u ∈ W ∧ v ∉ W) ∨ (v ∈ W ∧ u ∉ W))
    (hSize : 2 ≤ W.card) (hEven : Even W.card) (hColour : M.EdgeColorable 2) :
    IsSkeleton G M W := by
  have hCount := matching_edge_count M W hCover hCross
  have hOne : ∀ w ∈ W,M.degree w = 1 := fun w hw =>
    degree_eq_one_iff_existsUnique_adj.mpr (hCover w hw)
  have hDeg : ∀ v,M.degree v ≤ 2 := fun v => (matching_degree_le_one M hm v).trans (by omega)
  have hTwos : (Wᶜ.filter fun v => M.degree v = 2).card = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_notMem
    intro v hv
    have h := (mem_filter.mp hv).2
    have h' := matching_degree_le_one M hm v
    omega
  have hEvenM : Even M.edgeFinset.card := by rwa [hCount]
  have hLower : 2+2*(Wᶜ.filter fun v => M.degree v = 2).card ≤ M.edgeFinset.card := by
    rw [hTwos,hCount]
    omega
  obtain ⟨hOuterEven,hOuterSize⟩ := outer_endpoint_budget M W hDeg hCross hEvenM hLower
  have hLowEnds : 2 ≤ (W.filter fun w => M.degree w = 1).card := by
    rwa [filter_eq_self.mpr hOne]
  refine ⟨hLe,matching_isAcyclic M hm,hDeg,?_,hLowEnds,hOuterEven,hOuterSize,by omega,hCross,hColour⟩
  intro w hw
  rw [hOne w hw]

/-- The exact even/odd skeleton choice from two actual crossing matchings.
Only one edge of the second matching is used in the odd case. -/
theorem exists_skeleton_of_two_matchings (G M₁ M₂ : SimpleGraph V)
    [DecidableRel M₁.Adj] [DecidableRel M₂.Adj] (W : Finset V)
    (hM₁ : M₁≤G) (hM₂ : M₂≤G)
    (hm₁ : OneFactor.IsMatchingGraph M₁) (hm₂ : OneFactor.IsMatchingGraph M₂)
    (hdis : Disjoint M₁ M₂)
    (hcover₁ : ∀w∈W,∃!v,M₁.Adj w v) (hcover₂ : ∀w∈W,∃!v,M₂.Adj w v)
    (hcross₁ : ∀u v,M₁.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (hcross₂ : ∀u v,M₂.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (hsize : 2≤W.card) : ∃H : SimpleGraph V,IsSkeleton G H W := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel M₁.Adj)
    (fun u v => Classical.propDecidable (M₁.Adj u v)))
  cases (Subsingleton.elim (inferInstance : DecidableRel M₂.Adj)
    (fun u v => Classical.propDecidable (M₂.Adj u v)))
  have hcount := matching_edge_count M₁ W hcover₁ hcross₁
  have hone : ∀w∈W,M₁.degree w=1 := fun w hw => degree_eq_one_iff_existsUnique_adj.mpr (hcover₁ w hw)
  have hcolUnion := (two_matching_union_colouring M₁ M₂ hm₁ hm₂ hdis).1
  by_cases hEven : Even W.card
  · exact ⟨M₁,isSkeleton_of_even_matching G M₁ W hM₁ hm₁ hcover₁ hcross₁ hsize hEven
      (Critical.colourable_of_copy (Copy.ofLE M₁ (M₁⊔M₂) le_sup_left) hcolUnion)⟩
  · have hOdd : Odd W.card := Nat.not_even_iff_odd.mp hEven
    have hthree : 3≤W.card := by obtain ⟨k,hk⟩ := hOdd;omega
    obtain ⟨a,ha⟩ := card_pos.mp (show 0<W.card by omega)
    obtain ⟨b,hab,_⟩ := hcover₂ a ha
    have hb : b∉W := by
      rcases hcross₂ a b hab with h|h
      · exact h.2
      · exact False.elim (h.2 ha)
    have habNe : a≠b := hab.ne
    have hnot : ¬M₁.Adj a b := fun h => (disjoint_iff_inf_le.mp hdis) ⟨h,hab⟩
    have hEdge : edge a b≤M₂ := by
      intro u v huv
      rcases (edge_adj a b u v).mp huv with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩
      · exact hab
      · exact hab.symm
    let H := M₁⊔edge a b
    let : DecidableRel H.Adj := Classical.decRel _
    let : Fintype H.edgeSet := H.fintypeEdgeSet
    have hinc : ∀v,H.degree v=M₁.degree v+(if v=a ∨ v=b then 1 else 0) := by
      intro v
      convert matching_sup_edge_degree M₁ habNe hnot v using 1
      congr 5
      exact Subsingleton.elim _ _
    have hHUnion : H≤M₁⊔M₂ := sup_le le_sup_left (hEdge.trans le_sup_right)
    have hHG : H≤G := hHUnion.trans (sup_le hM₁ hM₂)
    have hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W) := by
      intro u v huv
      exact (hHUnion huv).elim (hcross₁ u v) (hcross₂ u v)
    have hdeg : ∀v,H.degree v≤2 := by
      intro v
      rw [hinc]
      have hh := matching_degree_le_one M₁ hm₁ v
      split_ifs <;> omega
    have hpos : ∀w∈W,1≤H.degree w := by
      intro w hw
      rw [hinc,hone w hw]
      omega
    have hlowEq : (W.filter fun w => H.degree w=1)=W.erase a := by
      ext w
      simp only [mem_filter,mem_erase]
      constructor
      · intro h
        refine ⟨?_,h.1⟩
        intro he
        subst w
        have hh := hinc a
        rw [hone a ha,if_pos (Or.inl rfl)] at hh
        omega
      · intro h
        refine ⟨h.2,?_⟩
        have hwb : w≠b := fun he => hb (he ▸ h.2)
        rw [hinc,hone w h.2,if_neg (by tauto)]
    have hlowEnds : 2≤(W.filter fun w => H.degree w=1).card := by
      rw [hlowEq,card_erase_of_mem ha]
      omega
    have htwos : (Wᶜ.filter fun v => H.degree v=2).card≤1 := by
      have hsub : Wᶜ.filter (fun v => H.degree v=2)⊆{b} := by
        intro v hv
        obtain ⟨hvout,hvdeg⟩ := mem_filter.mp hv
        have hvnot := mem_compl.mp hvout
        have hvne : v≠a := fun he => hvnot (he ▸ ha)
        have hh := hinc v
        have hm := matching_degree_le_one M₁ hm₁ v
        have hveq : v=b := by
          by_contra hn
          rw [if_neg (by tauto)] at hh
          omega
        exact mem_singleton.mpr hveq
      simpa only [card_singleton] using card_le_card hsub
    have hE : H.edgeFinset.card=W.card+1 := by
      have hh := card_edgeFinset_sup_edge (G:=M₁) hnot habNe
      rw [hcount] at hh
      convert hh using 1
    have heven : Even H.edgeFinset.card := by
      obtain ⟨k,hk⟩ := hOdd
      exact ⟨k+1,by omega⟩
    have hlower : 2+2*(Wᶜ.filter fun v => H.degree v=2).card≤H.edgeFinset.card := by omega
    obtain ⟨houterEven,houterLow⟩ := outer_endpoint_budget H W hdeg hcross heven hlower
    refine ⟨H,⟨hHG,matching_sup_edge_isAcyclic M₁ hm₁ habNe hnot,hdeg,hpos,hlowEnds,
      houterEven,houterLow,hE.le,hcross,?_⟩⟩
    exact Critical.colourable_of_copy (Copy.ofLE H (M₁⊔M₂) hHUnion) hcolUnion

/-- If one additional low-to-outside edge has a fresh outside endpoint,
the skeleton can be chosen with no outside internal vertex. -/
theorem exists_skeleton_of_matching_fresh_edge (G M₁ : SimpleGraph V)
    [DecidableRel M₁.Adj] (W : Finset V) (hM₁ : M₁≤G)
    (hm₁ : OneFactor.IsMatchingGraph M₁)
    (hcover₁ : ∀w∈W,∃!v,M₁.Adj w v)
    (hcross₁ : ∀u v,M₁.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    {a b : V} (ha : a∈W) (habG : G.Adj a b) (hb : b∉W)
    (hbfresh : M₁.degree b=0) (hsize : 2≤W.card) :
    ∃H : SimpleGraph V,IsSkeleton G H W ∧ ∀v∉W,H.degree v≤1 := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel M₁.Adj)
    (fun u v => Classical.propDecidable (M₁.Adj u v)))
  have hcount := matching_edge_count M₁ W hcover₁ hcross₁
  have hone : ∀w∈W,M₁.degree w=1 := fun w hw => degree_eq_one_iff_existsUnique_adj.mpr (hcover₁ w hw)
  have hcolM₁ := matching_colourable_one M₁ hm₁
  by_cases hEven : Even W.card
  · have hdeg : ∀v,M₁.degree v≤2 := fun v => (matching_degree_le_one M₁ hm₁ v).trans (by omega)
    have htwos : (Wᶜ.filter fun v => M₁.degree v=2).card=0 := by
      apply card_eq_zero.mpr
      apply eq_empty_of_forall_notMem
      intro v hv
      have hh := (mem_filter.mp hv).2
      have hd := matching_degree_le_one M₁ hm₁ v
      omega
    have heven : Even M₁.edgeFinset.card := by rwa [hcount]
    have hlower : 2+2*(Wᶜ.filter fun v => M₁.degree v=2).card≤M₁.edgeFinset.card := by
      rw [htwos,hcount]
      omega
    obtain ⟨houterEven,houterLow⟩ := outer_endpoint_budget M₁ W hdeg hcross₁ heven hlower
    have hlowEnds : 2≤(W.filter fun w => M₁.degree w=1).card := by
      have heq : W.filter (fun w => M₁.degree w=1)=W := filter_eq_self.mpr hone
      simpa only [heq] using hsize
    refine ⟨M₁,?_,fun v _ => matching_degree_le_one M₁ hm₁ v⟩
    refine ⟨hM₁,matching_isAcyclic M₁ hm₁,hdeg,?_,hlowEnds,houterEven,houterLow,
      by omega,hcross₁,?_⟩
    · intro w hw
      rw [hone w hw]
    · exact hcolM₁.mono (by decide)
  · have hOdd : Odd W.card := Nat.not_even_iff_odd.mp hEven
    have hthree : 3≤W.card := by obtain ⟨k,hk⟩ := hOdd;omega
    have habNe : a≠b := habG.ne
    have hnot : ¬M₁.Adj a b := by
      intro h
      have hp := (M₁.degree_pos_iff_exists_adj b).mpr ⟨a,h.symm⟩
      rw [hbfresh] at hp
      omega
    have hEdge : edge a b≤G := by
      intro u v huv
      rcases (edge_adj a b u v).mp huv with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩
      · exact habG
      · exact habG.symm
    let H := M₁⊔edge a b
    let : DecidableRel H.Adj := Classical.decRel _
    let : Fintype H.edgeSet := H.fintypeEdgeSet
    have hinc : ∀v,H.degree v=M₁.degree v+(if v=a ∨ v=b then 1 else 0) := by
      intro v
      convert matching_sup_edge_degree M₁ habNe hnot v using 1
      congr 5
      exact Subsingleton.elim _ _
    have hHG : H≤G := sup_le hM₁ hEdge
    have hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W) := by
      intro u v huv
      rcases huv with h|h
      · exact hcross₁ u v h
      · rcases (edge_adj a b u v).mp h with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩
        · exact Or.inl ⟨ha,hb⟩
        · exact Or.inr ⟨ha,hb⟩
    have hdeg : ∀v,H.degree v≤2 := by
      intro v
      rw [hinc]
      have hh := matching_degree_le_one M₁ hm₁ v
      split_ifs <;> omega
    have hpos : ∀w∈W,1≤H.degree w := by
      intro w hw
      rw [hinc,hone w hw]
      omega
    have hlowEq : (W.filter fun w => H.degree w=1)=W.erase a := by
      ext w
      simp only [mem_filter,mem_erase]
      constructor
      · intro h
        refine ⟨?_,h.1⟩
        intro he
        subst w
        have hh := hinc a
        rw [hone a ha,if_pos (Or.inl rfl)] at hh
        omega
      · intro h
        refine ⟨h.2,?_⟩
        have hwb : w≠b := fun he => hb (he ▸ h.2)
        rw [hinc,hone w h.2,if_neg (by tauto)]
    have hlowEnds : 2≤(W.filter fun w => H.degree w=1).card := by
      rw [hlowEq,card_erase_of_mem ha]
      omega
    have htwos : (Wᶜ.filter fun v => H.degree v=2).card≤1 := by
      have hsub : Wᶜ.filter (fun v => H.degree v=2)⊆{b} := by
        intro v hv
        obtain ⟨hvout,hvdeg⟩ := mem_filter.mp hv
        have hvnot := mem_compl.mp hvout
        have hvne : v≠a := fun he => hvnot (he ▸ ha)
        have hh := hinc v
        have hm := matching_degree_le_one M₁ hm₁ v
        have hveq : v=b := by
          by_contra hn
          rw [if_neg (by tauto)] at hh
          omega
        exact mem_singleton.mpr hveq
      simpa only [card_singleton] using card_le_card hsub
    have hE : H.edgeFinset.card=W.card+1 := by
      have hh := card_edgeFinset_sup_edge (G:=M₁) hnot habNe
      rw [hcount] at hh
      convert hh using 1
    have heven : Even H.edgeFinset.card := by
      obtain ⟨k,hk⟩ := hOdd
      exact ⟨k+1,by omega⟩
    have hlower : 2+2*(Wᶜ.filter fun v => H.degree v=2).card≤H.edgeFinset.card := by omega
    obtain ⟨houterEven,houterLow⟩ := outer_endpoint_budget H W hdeg hcross heven hlower
    refine ⟨H,⟨hHG,matching_sup_edge_isAcyclic M₁ hm₁ habNe hnot,hdeg,hpos,hlowEnds,
      houterEven,houterLow,hE.le,hcross,matching_sup_edge_colourable M₁ hm₁ hnot⟩,?_⟩
    intro v hv
    rw [hinc]
    by_cases hvb : v=b
    · subst v
      rw [hbfresh,if_pos (Or.inr rfl)]
    · have hva : v≠a := fun he => hv (he ▸ ha)
      rw [if_neg (by tauto),Nat.add_zero]
      exact matching_degree_le_one M₁ hm₁ v

/-- The critical graph supplies both crossing matchings, so the paper's
skeleton exists without any matching or forest hypothesis. -/
theorem exists_low_skeleton (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : IsDeltaCritical G) (hsize : 2≤(lowVertices G).card) :
    ∃H : SimpleGraph V,IsSkeleton G H (lowVertices G) := by
  classical
  obtain ⟨M₁,M₂,hM₁,hM₂,hm₁,hm₂,hdis,hcover₁,hcover₂,hcross₁,hcross₂⟩ :=
    exists_two_matchings_saturating_low_vertices G hcrit
  exact exists_skeleton_of_two_matchings G M₁ M₂ (lowVertices G)
    hM₁ hM₂ hm₁ hm₂ hdis hcover₁ hcover₂ hcross₁ hcross₂ hsize

/-- Reserve a genuine neighbour first, then construct a matching avoiding
it. The odd-case extra edge therefore introduces a fresh outside endpoint.
All matching and freshness inputs are discharged from criticality. -/
theorem exists_low_skeleton_fresh (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : IsDeltaCritical G) (hsize : 2≤(lowVertices G).card) :
    ∃H : SimpleGraph V,IsSkeleton G H (lowVertices G) ∧
      ∀v∉lowVertices G,H.degree v≤1 := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v)))
  let W := lowVertices G
  have hsizeW : 2≤W.card := hsize
  obtain ⟨a,ha⟩ := card_pos.mp (show 0<W.card by omega)
  obtain ⟨u,v,huv⟩ := MaximumCoreTwo.exists_adj_of_not_colorable G hcrit.2.1
  obtain ⟨b,hab⟩ := MaximumCoreTwo.exists_adj_of_connected hcrit.1 huv a
  have hb : b∉W := by
    intro hbW
    have haD := (mem_filter.mp ha).2
    have hbD := (mem_filter.mp hbW).2
    have hsum := Overfull.deg_add hcrit hab
    omega
  let b₀ : ↥(Wᶜ : Finset V) := ⟨b,mem_compl.mpr hb⟩
  obtain ⟨f,hf,hfr,havoid⟩ := LowVertexMatchingFlexibility.exists_low_selection_avoiding_vertex G hcrit b₀
  let M := selectionGraph W f
  have hM : M≤G := selectionGraph_le W f hfr
  obtain ⟨hm,hcover⟩ := selectionGraph_isMatching W f hf
  have hcross : ∀u v,M.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W) :=
    fun _ _ h => selectionGraph_crosses_cut W f h
  have hbfresh : M.degree b=0 := by
    rw [←card_neighborFinset_eq_degree,card_eq_zero]
    apply eq_empty_of_forall_notMem
    intro w hw
    have hadj : M.Adj b w := (mem_neighborFinset _ _ _).mp hw
    rcases hadj with ⟨z,hz,_⟩|⟨z,_,hz⟩
    · exact hb (hz ▸ z.property)
    · exact havoid z (Subtype.ext hz.symm)
  exact exists_skeleton_of_matching_fresh_edge G M W hM hm hcover hcross ha hab hb hbfresh hsize

end OverfullWork.PaperLowSkeleton
