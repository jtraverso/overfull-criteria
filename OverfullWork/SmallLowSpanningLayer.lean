module

public import OverfullWork.OddLowSmallCases
public import OverfullWork.LowSkeletonLayerGluing
public import OverfullWork.TwoColourTrimming

@[expose] public section


/-! # Actual spanning layers for zero or one low vertex

The core path is constructed by Hamilton-connectedness, and its matching
attachments are actual graph edges. No spanning layer is an input.
-/
namespace OverfullWork.SmallLowSpanningLayer
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open LowSkeletonProjection PathGraphRealization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

/-- A single prescribed core path, realized as an actual ambient graph. -/
theorem exists_core_path_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (a b : ↥(Uᶜ : Finset V)) (hab : a≠b)
    (hsize : 5≤Fintype.card ↥((U:Set V)ᶜ))
    (hdense : Fintype.card ↥((U:Set V)ᶜ)+2≤2*(G.induce ((U:Set V)ᶜ)).minDegree) :
    ∃K : SimpleGraph V,K≤G ∧ K.IsAcyclic ∧
      (∀x y,K.Adj x y → x∉U ∧ y∉U) ∧
      (∀v∈U,K.degree v=0) ∧
      ∀v∉U,K.degree v=if v=a.val ∨ v=b.val then 1 else 2 := by
  let C : Set V:=(U:Set V)ᶜ
  let core:=G.induce C
  let x : C:=⟨a.val,mem_compl.mp a.property⟩
  let y : C:=⟨b.val,mem_compl.mp b.property⟩
  have hxy : x≠y := fun he=>hab (Subtype.ext (congrArg (fun z:C=>z.val) he))
  obtain ⟨p,hp⟩:=DenseHamilton.exists_hamiltonian_path core hsize hdense hxy
  let f : core →g G:=(Embedding.induce C).toHom
  let q:=p.map f
  have hq : q.IsPath:=hp.isPath.map (show Function.Injective f from Subtype.val_injective)
  have hsupport : ∀v,v∈q.support ↔ ∃z∈p.support,z.val=v := by
    intro v
    rw [Walk.support_map,List.mem_map]
    rfl
  have hoff : ∀v,v∈q.support → v∉U := by
    intro v hv
    obtain ⟨z,_,rfl⟩:=(hsupport v).mp hv
    exact z.property
  have hcover : ∀v,v∉U → v∈q.support := by
    intro v hv
    exact (hsupport v).mpr ⟨⟨v,hv⟩,hp.mem_support _,rfl⟩
  refine ⟨pathGraph q,le_original q,isAcyclic q hq,?_,?_,?_⟩
  · intro u v huv
    exact ⟨hoff u (mem_support_of_adj q huv),hoff v (mem_support_of_adj q huv.symm)⟩
  · intro v hv
    exact degree_outside q (fun h=>hoff v h hv)
  · intro v hv
    have habval : a.val≠b.val:=fun he=>hab (Subtype.ext he)
    by_cases hva : v=a.val
    · subst v
      rw [if_pos (Or.inl rfl)]
      exact degree_start q hq habval
    by_cases hvb : v=b.val
    · subst v
      rw [if_pos (Or.inr rfl)]
      exact degree_end q hq habval
    rw [if_neg (by tauto)]
    exact degree_internal q hq (hcover v hv) hva hvb

/-- The layer records degree demands, rather than assuming a two-cover
at a charged fixed endpoint. -/
structure Certificate (G : SimpleGraph V) [DecidableRel G.Adj] where
  layer : SimpleGraph V
  le_original : layer≤G
  acyclic : layer.IsAcyclic
  degree_le_two : ∀v,layer.degree v≤2
  colourable : layer.EdgeColorable 2
  demands : ∀v,G.degree v+2≤G.maxDegree+layer.degree v
  low_one_cover : ∀w∈lowVertices G,layer.degree w=1
  residual_maxDegree : (G\layer).maxDegree=G.maxDegree-2
  residual_uncolourable : ¬(G\layer).EdgeColorable (G\layer).maxDegree

private theorem degree_union (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (hd : Disjoint A B) (v : V) : (A⊔B).degree v=A.degree v+B.degree v := by
  rw [←card_neighborFinset_eq_degree,neighborFinset_sup,
    card_union_of_disjoint (disjoint_neighborFinset_of_disjoint A B v hd),
    card_neighborFinset_eq_degree,card_neighborFinset_eq_degree]

/-- A matching projection has at most one incident edge, and positive
core degree occurs precisely at a projected exceptional endpoint. -/
theorem projection_core_degree {G : SimpleGraph V} {A U Z : Finset V}
    (P : Projection G A U Z) (v : V) (hv : v∉U) :
    P.matching.degree v=if ∃a:A,a.val∈U ∧ (P.representative a).val=v then 1 else 0 := by
  have hle:=PaperLowSkeleton.matching_degree_le_one P.matching P.isMatching v
  have hi : 0<P.matching.degree v ↔ ∃a:A,a.val∈U ∧ (P.representative a).val=v := by
    constructor
    · intro hh
      obtain ⟨w,hw⟩:=(P.matching.degree_pos_iff_exists_adj v).mp hh
      rcases P.endpoints v w hw with h|h
      · exact False.elim (hv (mem_inter.mp h.1).2)
      · let a : A:=⟨w,(mem_inter.mp h.1).1⟩
        have ha : a.val∈U:=(mem_inter.mp h.1).2
        have he:=P.isMatching w v (P.representative a).val hw.symm (P.selected a ha)
        exact ⟨a,ha,he.symm⟩
    · rintro ⟨a,ha,rfl⟩
      exact (P.matching.degree_pos_iff_exists_adj _).mpr ⟨a.val,(P.selected a ha).symm⟩
  split_ifs with h
  · have hh:=hi.mpr h;omega
  · have hh:¬0<P.matching.degree v:=fun hh=>h (hi.mp hh);omega

/-- A projection matching and the actual core Hamilton path give a
spanning forest. Fixed endpoints have degree one; projected endpoints
have degree two. -/
theorem exists_zero_low_layer_finite (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (hD : 2≤G.maxDegree)
    (U : Finset V) (hW : lowVertices G=∅)
    (hexception : ∀v∈U,G.degree v+2≤G.maxDegree)
    (P : OddLowSmallCases.ChargedPair G G.maxDegree U)
    (hsize : 5≤Fintype.card ↥((U:Set V)ᶜ))
    (hdense : Fintype.card ↥((U:Set V)ᶜ)+2≤2*(G.induce ((U:Set V)ᶜ)).minDegree) :
    Nonempty (Certificate G) := by
  classical
  let A : Finset V:={P.left,P.right}
  let N:=P.projection.matching
  let a : A:=⟨P.left,by simp [A]⟩
  let b : A:=⟨P.right,by simp [A]⟩
  let ra:=P.projection.representative a
  let rb:=P.projection.representative b
  have hr : ra≠rb := fun h=>P.distinct (congrArg Subtype.val (P.projection.injective h))
  obtain ⟨K,hKG,hKforest,hKcore,hKzero,hKdegree⟩:=exists_core_path_graph G U ra rb hr hsize hdense
  have hNcross : ∀x y,N.Adj x y → (x∈U ∧ y∉U) ∨ (y∈U ∧ x∉U) := by
    intro x y h
    rcases P.projection.endpoints x y h with h|h
    · exact Or.inl ⟨(mem_inter.mp h.1).2,h.2.1⟩
    · exact Or.inr ⟨(mem_inter.mp h.1).2,h.2.1⟩
  have hdis : Disjoint N K := by
    apply disjoint_iff_inf_le.mpr
    intro x y ⟨hn,hk⟩
    rcases hNcross x y hn with h|h
    · exact (hKcore x y hk).1 h.1
    · exact (hKcore x y hk).2 h.1
  let L:=N⊔K
  have hsum : ∀v,L.degree v=N.degree v+K.degree v := degree_union N K hdis
  have hforest : L.IsAcyclic := by
    have hh:=LowSkeletonLayerGluing.acyclic_of_matching_attachments (⊥:SimpleGraph V) N K ∅ U
      (empty_subset _) (by intro x y z h;cases h) P.projection.isMatching
      (by intro x y h;cases h) hNcross (by simp) hKcore hKforest
    simpa only [bot_sup_eq,L] using hh
  have hdeg : ∀v,L.degree v≤2 := by
    intro v
    rw [hsum]
    have hn:=PaperLowSkeleton.matching_degree_le_one N P.projection.isMatching v
    by_cases hv:v∈U
    · rw [hKzero v hv];omega
    · rw [hKdegree v hv,projection_core_degree P.projection v hv]
      split_ifs with he hrend
      · omega
      · obtain ⟨z,_,hz⟩:=he
        have hzpair : z.val=P.left ∨ z.val=P.right := by simpa only [mem_insert,mem_singleton] using z.property
        exfalso
        apply hrend
        rcases hzpair with h|h
        · have heq:z=a:=Subtype.ext h
          exact Or.inl (hz ▸ congrArg Subtype.val (congrArg P.projection.representative heq))
        · have heq:z=b:=Subtype.ext h
          exact Or.inr (hz ▸ congrArg Subtype.val (congrArg P.projection.representative heq))
      · omega
      · omega
  have hdemand : ∀v,G.degree v+2≤G.maxDegree+L.degree v := by
    intro v
    by_cases hv:v∈U
    · exact (hexception v hv).trans (Nat.le_add_right _ _)
    rw [hsum,hKdegree v hv]
    by_cases hvend : v=ra.val ∨ v=rb.val
    · rw [if_pos hvend]
      by_cases hn : N.degree v=0
      · rw [hn]
        have hvcharge : G.degree v+1≤G.maxDegree := by
          rcases hvend with he|he
          · have hpl : P.left∉U := by
              intro hh
              have hp:=P.projection.selected a hh
              have hpos : 0<N.degree v:=(N.degree_pos_iff_exists_adj v).mpr
                ⟨P.left,he ▸ hp.symm⟩
              omega
            have hrfix:=P.projection.fixed a hpl
            have hvp : v=P.left:=he.trans hrfix
            rw [hvp];exact P.left_charge
          · have hpr : P.right∉U := by
              intro hh
              have hp:=P.projection.selected b hh
              have hpos : 0<N.degree v:=(N.degree_pos_iff_exists_adj v).mpr
                ⟨P.right,he ▸ hp.symm⟩
              omega
            have hrfix:=P.projection.fixed b hpr
            have hvp : v=P.right:=he.trans hrfix
            rw [hvp];exact P.right_charge
        omega
      · have hh:=G.degree_le_maxDegree v;omega
    · rw [if_neg hvend]
      have hh:=G.degree_le_maxDegree v;omega
  have hLG : L≤G:=sup_le P.projection.matching_le hKG
  have hcol : L.EdgeColorable 2:=TwoColourTrimming.two_colourable_of_acyclic_and_degree_le_two L hforest hdeg
  refine ⟨⟨L,hLG,hforest,?_,hcol,?_,?_,?_,?_⟩⟩
  · convert hdeg using 1
    congr! 8
  · convert hdemand using 1
    congr! 8
  · intro w hw;rw [hW] at hw;exact False.elim (notMem_empty _ hw)
  · convert TwoColourTrimming.maxDegree_sdiff_of_degree_demands G L hD hLG hdeg hdemand using 1
    congr! 8
  · convert TwoColourTrimming.critical_residue_of_degree_demands G L hc hD hLG hcol hdeg hdemand using 1
    congr! 8

end OverfullWork.SmallLowSpanningLayer
