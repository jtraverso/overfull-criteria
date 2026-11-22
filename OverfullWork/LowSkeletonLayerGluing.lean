module

public import OverfullWork.LowSkeletonPreparation
public import OverfullWork.PairedEndpointEnumeration
public import OverfullWork.LowSkeletonAttachmentDegrees
public import OverfullWork.PathGraphRealization

@[expose] public section


/-! # Gluing the even low skeleton to actual core path covers

The acyclicity argument removes the low leaves, then the remaining
exceptional vertices. It never assumes that a projected skeleton has
an arbitrary spanning completion. The even skeleton is constructed as
one of the actual low-saturating matchings.
-/
namespace OverfullWork.LowSkeletonLayerGluing
open SimpleGraph Finset Overfull LowVertexMatchingAbsorption PaperLowSkeleton
open LowSkeletonProjection LowSkeletonPreparation
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

omit [Fintype V] [DecidableEq V] in
/-- A cycle cannot pass through the two levels of matching attachments:
first low leaves, then exceptional matching endpoints. -/
theorem acyclic_of_matching_attachments (H N K : SimpleGraph V) (W U : Finset V)
    (hWU : W⊆U) (hmH : OneFactor.IsMatchingGraph H) (hmN : OneFactor.IsMatchingGraph N)
    (hHcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (hNcross : ∀u v,N.Adj u v → (u∈U ∧ v∉U) ∨ (v∈U ∧ u∉U))
    (hNzero : ∀w∈W,∀v,¬N.Adj w v)
    (hKcore : ∀u v,K.Adj u v → u∉U ∧ v∉U) (hK : K.IsAcyclic) :
    ((H⊔N)⊔K).IsAcyclic := by
  let F := (H⊔N)⊔K
  intro v p hp
  have hnotW : ∀x∈p.support,x∉W := by
    intro x hxp hxW
    let q := p.rotate x hxp
    have hq : q.IsCycle := hp.rotate hxp
    have hrow : ∀z,F.Adj x z → H.Adj x z := by
      intro z h
      rcases h with (h|h)|h
      · exact h
      · exact False.elim (hNzero x hxW z h)
      · exact False.elim ((hKcore x z h).1 (hWU hxW))
    exact hq.snd_ne_penultimate (hmH x q.snd q.penultimate
      (hrow _ (q.adj_snd hq.not_nil)) (hrow _ (q.adj_penultimate hq.not_nil).symm))
  have hnotU : ∀x∈p.support,x∉U := by
    intro x hxp hxU
    let q := p.rotate x hxp
    have hq : q.IsCycle := hp.rotate hxp
    have hrow : ∀z,z∈p.support → F.Adj x z → N.Adj x z := by
      intro z hzp h
      rcases h with (h|h)|h
      · rcases hHcross x z h with ⟨hxW,_⟩|⟨hzW,_⟩
        · exact False.elim (hnotW x hxp hxW)
        · exact False.elim (hnotW z hzp hzW)
      · exact h
      · exact False.elim ((hKcore x z h).1 hxU)
    have hs : q.snd∈p.support := (p.mem_support_rotate_iff x hxp).mp (q.getVert_mem_support 1)
    have ht : q.penultimate∈p.support := (p.mem_support_rotate_iff x hxp).mp
      (q.getVert_mem_support (q.length-1))
    exact hq.snd_ne_penultimate (hmN x q.snd q.penultimate
      (hrow _ hs (q.adj_snd hq.not_nil)) (hrow _ ht (q.adj_penultimate hq.not_nil).symm))
  have htransfer : ∀e∈p.edges,e∈K.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      have ha := hnotU a (p.fst_mem_support_of_mem_edges he)
      have hb := hnotU b (p.snd_mem_support_of_mem_edges he)
      have hab := p.adj_of_mem_edges he
      rcases hab with (h|h)|h
      · rcases hHcross a b h with ⟨haW,_⟩|⟨hbW,_⟩
        · exact False.elim (ha (hWU haW))
        · exact False.elim (hb (hWU hbW))
      · rcases hNcross a b h with ⟨haU,_⟩|⟨hbU,_⟩
        · exact False.elim (ha haU)
        · exact False.elim (hb hbU)
      · exact h
  exact hK (p.transfer K htransfer) (hp.transfer htransfer)

/-- Projection edges never touch the low vertices of the skeleton. -/
theorem projection_no_low_edge (G H : SimpleGraph V) [DecidableRel H.Adj]
    (W U : Finset V) (hWU : W⊆U)
    (P : Projection G (outerLeaves H W) U (nonisolatedVertices H)) :
    ∀w∈W,∀v,¬P.matching.Adj w v := by
  intro w hw v h
  rcases P.endpoints w v h with h|h
  · have ha := (mem_inter.mp h.1).1
    exact (mem_compl.mp (mem_filter.mp ha).1) hw
  · exact h.2.1 (hWU hw)

/-- Projection edges go between the exceptional set and the core. -/
theorem projection_crosses_exceptional (G H : SimpleGraph V) [DecidableRel H.Adj]
    (W U : Finset V) (P : Projection G (outerLeaves H W) U (nonisolatedVertices H)) :
    ∀u v,P.matching.Adj u v → (u∈U ∧ v∉U) ∨ (v∈U ∧ u∉U) := by
  intro u v h
  rcases P.endpoints u v h with h|h
  · exact Or.inl ⟨(mem_inter.mp h.1).2,h.2.1⟩
  · exact Or.inr ⟨(mem_inter.mp h.1).2,h.2.1⟩

/-- The matching variant of the paper skeleton is constructed explicitly
when the low set has even cardinality. -/
theorem exists_even_matching_skeleton (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : IsDeltaCritical G) (hsize : 2≤(lowVertices G).card)
    (heven : Even (lowVertices G).card) :
    ∃H : SimpleGraph V,IsSkeleton G H (lowVertices G) ∧ OneFactor.IsMatchingGraph H := by
  classical
  obtain ⟨H,N,hH,hN,hmH,hmN,hdis,hcoverH,hcoverN,hcrossH,hcrossN⟩ :=
    exists_two_matchings_saturating_low_vertices G hcrit
  let W := lowVertices G
  have hsizeW : 2≤W.card := hsize
  have hcount := matching_edge_count H W hcoverH hcrossH
  have hone : ∀w∈W,H.degree w=1 := fun w hw => degree_eq_one_iff_existsUnique_adj.mpr (hcoverH w hw)
  have hdeg : ∀v,H.degree v≤2 := fun v => (matching_degree_le_one H hmH v).trans (by omega)
  have htwos : (Wᶜ.filter fun v => H.degree v=2).card=0 := by
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_notMem
    intro v hv
    have hh := (mem_filter.mp hv).2
    have hd := matching_degree_le_one H hmH v
    omega
  have he : Even H.edgeFinset.card := by rwa [hcount]
  have hl : 2+2*(Wᶜ.filter fun v => H.degree v=2).card≤H.edgeFinset.card := by
    rw [htwos,hcount]
    exact hsize
  obtain ⟨houterE,houterL⟩ := outer_endpoint_budget H W hdeg hcrossH he hl
  have hends : 2≤(W.filter fun w => H.degree w=1).card := by
    rw [filter_eq_self.mpr hone]
    exact hsize
  have hc := (two_matching_union_colouring H N hmH hmN hdis).1
  refine ⟨H,⟨hH,matching_isAcyclic H hmH,hdeg,?_,hends,houterE,houterL,
    ?_,hcrossH,?_⟩,hmH⟩
  · intro w hw
    rw [hone w hw]
  · convert hcount.le.trans (Nat.le_succ W.card) using 1
  · exact Critical.colourable_of_copy (Copy.ofLE H (H⊔N) le_sup_left) hc

section FiniteGluing
variable {I : Type*} [Fintype I]

/-- Actual disjoint paths on the core complete an even matching skeleton.
The hypotheses describe the walks themselves, rather than assuming any
forest or two-colour completion. -/
theorem finite_even_gluing (G H : SimpleGraph V) [DecidableRel H.Adj]
    (W U Z : Finset V) (hHG : H≤G) (hWU : W⊆U)
    (hmH : OneFactor.IsMatchingGraph H)
    (hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (P : Projection G (outerLeaves H W) U Z)
    (a b : I → V) (T : ∀i,G.Walk (a i) (b i))
    (hp : ∀i,(T i).IsPath)
    (hdis : ∀i j,i≠j → ∀z,z∈(T i).support → z∉(T j).support)
    (hcore : ∀i z,z∈(T i).support → z∉U)
    (hcover : ∀z,z∉U → ∃i,z∈(T i).support)
    (hab : ∀i,a i≠b i)
    (hend : ∀z,(∃v : outerLeaves H W,(P.representative v).val=z) ↔
      ∃i,z=a i ∨ z=b i) :
    let L := (H⊔P.matching)⊔PathGraphRealization.pathUnion T
    L≤G ∧ L.IsAcyclic ∧ (∀v,L.degree v≤2) ∧ (∀v,v∉U → L.degree v=2) := by
  classical
  let Q := H⊔P.matching
  let K := PathGraphRealization.pathUnion T
  have hNcross : ∀u v,P.matching.Adj u v →
      (u∈U ∧ v∉U) ∨ (v∈U ∧ u∉U) := by
    intro u v h
    rcases P.endpoints u v h with h|h
    · exact Or.inl ⟨(mem_inter.mp h.1).2,h.2.1⟩
    · exact Or.inr ⟨(mem_inter.mp h.1).2,h.2.1⟩
  have hKcore : ∀u v,K.Adj u v → u∉U ∧ v∉U := by
    intro u v h
    obtain ⟨i,hi⟩ := PathGraphRealization.pathUnion_adj_iff T |>.mp h
    exact ⟨hcore i u (PathGraphRealization.mem_support_of_adj (T i) hi),
      hcore i v (PathGraphRealization.mem_support_of_adj (T i) hi.symm)⟩
  have hQK : Disjoint Q K := by
    apply disjoint_iff_inf_le.mpr
    intro u v ⟨hQ,hK⟩
    obtain ⟨hu,hv⟩ := hKcore u v hK
    rcases hQ with hH|hN
    · rcases hcross u v hH with h|h
      · exact (hu (hWU h.1)).elim
      · exact (hv (hWU h.1)).elim
    · rcases hNcross u v hN with h|h
      · exact (hu h.1).elim
      · exact (hv h.1).elim
  have hsum : ∀v,(Q⊔K).degree v=Q.degree v+K.degree v := by
    intro v
    rw [←card_neighborFinset_eq_degree,neighborFinset_sup,
      card_union_of_disjoint (disjoint_neighborFinset_of_disjoint Q K v hQK),
      card_neighborFinset_eq_degree,card_neighborFinset_eq_degree]
  have hout : ∀v∉W,H.degree v≤1 := fun v _ => matching_degree_le_one H hmH v
  have hdeg : ∀v,H.degree v≤2 := fun v => (matching_degree_le_one H hmH v).trans (by omega)
  have hzeroK : ∀v∈U,K.degree v=0 := by
    intro v hv
    exact PathGraphRealization.pathUnion_degree_outside T
      (fun i hi => hcore i v hi hv)
  have htwo : ∀v,v∉U → (Q⊔K).degree v=2 := by
    intro v hv
    rw [hsum,LowSkeletonAttachmentDegrees.degree_on_core hWU hcross hout P hv]
    by_cases he : ∃i,v=a i ∨ v=b i
    · rw [if_pos ((hend v).mpr he)]
      obtain ⟨i,hi⟩ := he
      rcases hi with rfl|rfl
      · rw [PathGraphRealization.pathUnion_degree_start T hp hdis i (hab i)]
      · rw [PathGraphRealization.pathUnion_degree_end T hp hdis i (hab i)]
    · rw [if_neg (fun h => he ((hend v).mp h))]
      obtain ⟨i,hi⟩ := hcover v hv
      have hia : v≠a i := fun h => he ⟨i,Or.inl h⟩
      have hib : v≠b i := fun h => he ⟨i,Or.inr h⟩
      rw [PathGraphRealization.degree_eq_of_mem_support T hdis i hi,
        PathGraphRealization.degree_internal (T i) (hp i) hi hia hib]
  refine ⟨sup_le (LowSkeletonAttachmentDegrees.attachment_le hHG P)
    (PathGraphRealization.pathUnion_le_original T),?_,?_,htwo⟩
  · exact acyclic_of_matching_attachments H P.matching K W U hWU hmH P.isMatching
      hcross hNcross (fun w hw v => LowSkeletonAttachmentDegrees.no_matching_adj_at_low hWU P hw v)
      hKcore (PathGraphRealization.pathUnion_isAcyclic T hp hdis)
  · intro v
    by_cases hv : v∈U
    · rw [hsum,hzeroK v hv,Nat.add_zero]
      exact LowSkeletonAttachmentDegrees.degree_le_two hWU hcross hdeg hout P v
    · rw [htwo v hv]

end FiniteGluing

end OverfullWork.LowSkeletonLayerGluing
