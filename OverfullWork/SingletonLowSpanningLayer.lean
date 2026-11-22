module

public import OverfullWork.SmallLowSpanningLayer

@[expose] public section


/-! # An actual degree-lowering layer with a singleton low set

One original low edge, its actual endpoint projection, and a constructed
core Hamilton path form the layer. The remaining endpoint is genuinely
deficient; it supplies the one unit absent at a fixed core endpoint.
-/
namespace OverfullWork.SmallLowSpanningLayer
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open LowSkeletonProjection PathGraphRealization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

private theorem degree_union_singleton (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (hd : Disjoint A B) (v : V) : (A⊔B).degree v=A.degree v+B.degree v := by
  rw [←card_neighborFinset_eq_degree,neighborFinset_sup,
    card_union_of_disjoint (disjoint_neighborFinset_of_disjoint A B v hd),
    card_neighborFinset_eq_degree,card_neighborFinset_eq_degree]

private theorem fixed_endpoint_matching_degree_zero {G : SimpleGraph V} {A U Z : Finset V}
    (P : Projection G A U Z) (v : V) (hvU : v∉U) (hvA : v∈A) : P.matching.degree v=0 := by
  by_contra hn
  obtain ⟨z,hz⟩:=(P.matching.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hn)
  rcases P.endpoints v z hz with h|h
  · exact hvU (mem_inter.mp h.1).2
  · exact h.2.2 (mem_union_left _ hvA)

/-- Finite singleton realization. Only actual graph degrees, a selected
edge and its constructed projection are used before Hamilton extension. -/
theorem exists_singleton_low_layer_finite (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (hD : 2≤G.maxDegree)
    (U : Finset V) (w a x : V) (hW : lowVertices G={w}) (hwU : w∈U)
    (hwa : G.Adj w a) (hax : a≠x) (hxw : x≠w) (hxD : G.degree x+1≤G.maxDegree)
    (hexception : ∀v∈U,G.degree v+2≤G.maxDegree)
    (P : Projection G {a,x} U {w,a})
    (hsize : 5≤Fintype.card ↥((U:Set V)ᶜ))
    (hdense : Fintype.card ↥((U:Set V)ᶜ)+2≤2*(G.induce ((U:Set V)ᶜ)).minDegree) :
    Nonempty (Certificate G) := by
  classical
  let A : Finset V:={a,x}
  let H:=edge w a
  let N:=P.matching
  let aa : A:=⟨a,by simp [A]⟩
  let xx : A:=⟨x,by simp [A]⟩
  let ra:=P.representative aa
  let rx:=P.representative xx
  have haw : a≠w:=Ne.symm (G.ne_of_adj hwa)
  have hr : ra≠rx:=fun he=>hax (congrArg Subtype.val (P.injective he))
  obtain ⟨K,hKG,hKforest,hKcore,hKzero,hKdegree⟩:=exists_core_path_graph G U ra rx hr hsize hdense
  have hmH : OneFactor.IsMatchingGraph H := by
    intro u v z huv huz
    simp only [H,edge_adj] at huv huz
    rcases huv.1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      rcases huz.1 with ⟨h1,h2⟩|⟨h1,h2⟩ <;> grind
  have hHdeg : ∀v,H.degree v=if v=w ∨ v=a then 1 else 0 := by
    intro v
    have hle:=PaperLowSkeleton.matching_degree_le_one H hmH v
    split_ifs with hv
    · have hpos : 0<H.degree v := by
        apply (H.degree_pos_iff_exists_adj v).mpr
        rcases hv with hvw|hva
        · refine ⟨a,?_⟩
          rw [hvw]
          exact (edge_adj w a w a).mpr ⟨Or.inl ⟨rfl,rfl⟩,Ne.symm haw⟩
        · refine ⟨w,?_⟩
          rw [hva]
          exact (edge_adj w a a w).mpr ⟨Or.inr ⟨rfl,rfl⟩,haw⟩
      omega
    · by_contra hh
      obtain ⟨z,hz⟩:=(H.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hh)
      exact hv (by rcases (edge_adj w a v z).mp hz |>.1 with h|h;exact Or.inl h.1;exact Or.inr h.1)
  have hNcross : ∀u v,N.Adj u v → (u∈U ∧ v∉U) ∨ (v∈U ∧ u∉U) := by
    intro u v h
    rcases P.endpoints u v h with h|h
    · exact Or.inl ⟨(mem_inter.mp h.1).2,h.2.1⟩
    · exact Or.inr ⟨(mem_inter.mp h.1).2,h.2.1⟩
  have hNw : ∀v,¬N.Adj w v := by
    intro v h
    rcases P.endpoints w v h with h|h
    · have hwA : w=a ∨ w=x := by simpa only [mem_insert,mem_singleton] using (mem_inter.mp h.1).1
      exact hwA.elim (fun he=>haw he.symm) (fun he=>hxw he.symm)
    · exact h.2.1 hwU
  have hHcross : ∀u v,H.Adj u v → (u∈({w}:Finset V) ∧ v∉({w}:Finset V)) ∨ (v∈({w}:Finset V) ∧ u∉({w}:Finset V)) := by
    intro u v h
    rcases (edge_adj w a u v).mp h |>.1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [haw]
  have hHN : Disjoint H N := by
    apply disjoint_iff_inf_le.mpr
    intro u v ⟨hH,hN⟩
    rcases hHcross u v hH with h|h
    · have hu:u=w:=mem_singleton.mp h.1;subst u;exact hNw v hN
    · have hv:v=w:=mem_singleton.mp h.1;subst v;exact hNw u hN.symm
  let Q:=H⊔N
  have hQsum : ∀v,Q.degree v=H.degree v+N.degree v := degree_union_singleton H N hHN
  have hQcross : ∀u v,Q.Adj u v → (u∈U ∧ v∉U) ∨ (v∈U ∧ u∉U) ∨ (u∈U ∧ v∈U) := by
    intro u v h
    rcases h with h|h
    · rcases hHcross u v h with h|h
      · have hu:u=w:=mem_singleton.mp h.1
        by_cases hv:v∈U
        · exact Or.inr (Or.inr ⟨hu ▸ hwU,hv⟩)
        · exact Or.inl ⟨hu ▸ hwU,hv⟩
      · have hv:v=w:=mem_singleton.mp h.1
        by_cases hu:u∈U
        · exact Or.inr (Or.inr ⟨hu,hv ▸ hwU⟩)
        · exact Or.inr (Or.inl ⟨hv ▸ hwU,hu⟩)
    · exact (hNcross u v h).elim Or.inl (Or.inr ∘ Or.inl)
  have hQK : Disjoint Q K := by
    apply disjoint_iff_inf_le.mpr
    intro u v ⟨hq,hk⟩
    obtain ⟨hu,hv⟩:=hKcore u v hk
    rcases hQcross u v hq with h|h|h
    · exact hu h.1
    · exact hv h.1
    · exact hu h.1
  let L:=Q⊔K
  have hsum : ∀v,L.degree v=Q.degree v+K.degree v := degree_union_singleton Q K hQK
  have hforest : L.IsAcyclic :=
    LowSkeletonLayerGluing.acyclic_of_matching_attachments H N K {w} U
      (singleton_subset_iff.mpr hwU) hmH P.isMatching hHcross hNcross
      (by intro u hu v;have he:u=w:=mem_singleton.mp hu;subst u;exact hNw v) hKcore hKforest
  have hQcore : ∀v∉U,Q.degree v≤1 := by
    intro v hv
    rw [hQsum,hHdeg]
    have hn:=PaperLowSkeleton.matching_degree_le_one N P.isMatching v
    by_cases hva:v=a
    · subst v
      rw [fixed_endpoint_matching_degree_zero P a hv (by simp),if_pos (Or.inr rfl)]
    · have hvw:v≠w:=fun he=>hv (he ▸ hwU)
      rw [if_neg (by tauto)];omega
  have hQpositive_endpoint : ∀v∉U,0<Q.degree v → v=ra.val ∨ v=rx.val := by
    intro v hv hp
    rw [hQsum,hHdeg] at hp
    by_cases hva:v=a
    · have haout : a∉U := by intro hh;apply hv;rw [hva];exact hh
      have hfix:=P.fixed aa haout
      exact Or.inl (hva.trans hfix.symm)
    · have hvw:v≠w:=fun he=>hv (he ▸ hwU)
      rw [if_neg (by tauto)] at hp
      have hn : 0<N.degree v := by omega
      have hformula:=projection_core_degree P v hv
      rw [hformula] at hn
      split_ifs at hn with he
      · obtain ⟨z,_,hz⟩:=he
        have hzpair:z.val=a ∨ z.val=x := by simpa only [mem_insert,mem_singleton] using z.property
        rcases hzpair with h|h
        · have heq:z=aa:=Subtype.ext h
          exact Or.inl (hz.symm.trans (congrArg Subtype.val (congrArg P.representative heq)))
        · have heq:z=xx:=Subtype.ext h
          exact Or.inr (hz.symm.trans (congrArg Subtype.val (congrArg P.representative heq)))
      · omega
  have hdeg : ∀v,L.degree v≤2 := by
    intro v
    rw [hsum]
    by_cases hv:v∈U
    · rw [hKzero v hv,hQsum]
      have hh:=PaperLowSkeleton.matching_degree_le_one H hmH v
      have hn:=PaperLowSkeleton.matching_degree_le_one N P.isMatching v
      omega
    · rw [hKdegree v hv]
      have hq:=hQcore v hv
      split_ifs with he
      · omega
      · have hn:¬0<Q.degree v:=fun hp=>he (hQpositive_endpoint v hv hp)
        omega
  have hleft : 0<Q.degree ra.val := by
    by_cases ha:a∈U
    · have hh:=P.selected aa ha
      have hpos:0<N.degree ra.val:=(N.degree_pos_iff_exists_adj _).mpr ⟨a,hh.symm⟩
      rw [hQsum];omega
    · have hfix:=P.fixed aa ha
      rw [hQsum,hHdeg,hfix]
      rw [if_pos (Or.inr rfl)]
      omega
  have hdemand : ∀v,G.degree v+2≤G.maxDegree+L.degree v := by
    intro v
    by_cases hv:v∈U
    · exact (hexception v hv).trans (Nat.le_add_right _ _)
    rw [hsum,hKdegree v hv]
    by_cases hvend:v=ra.val ∨ v=rx.val
    · rw [if_pos hvend]
      by_cases hq:0<Q.degree v
      · have hh:=G.degree_le_maxDegree v;omega
      · rcases hvend with he|he
        · have hh:=he ▸ hleft;omega
        · have hxout:x∉U := by
            intro hxU
            have hh:=P.selected xx hxU
            have hn:0<N.degree v:=(N.degree_pos_iff_exists_adj _).mpr ⟨x,he ▸ hh.symm⟩
            have hs:=hQsum v;omega
          have hfix:=P.fixed xx hxout
          have hvx:v=x:=he.trans hfix
          have hh : G.degree v+1≤G.maxDegree := by rw [hvx];exact hxD
          omega
    · rw [if_neg hvend]
      have hh:=G.degree_le_maxDegree v;omega
  have hLG : L≤G:=sup_le (sup_le ((edge_le_iff G).mpr (Or.inr hwa)) P.matching_le) hKG
  have hcol : L.EdgeColorable 2:=TwoColourTrimming.two_colourable_of_acyclic_and_degree_le_two L hforest hdeg
  have hlow : ∀u∈lowVertices G,L.degree u=1 := by
    intro u hu
    have he:u=w:=by simpa only [hW,mem_singleton] using hu
    subst u
    have hn:N.degree w=0 := by
      by_contra hh
      obtain ⟨z,hz⟩:=(N.degree_pos_iff_exists_adj w).mp (Nat.pos_of_ne_zero hh)
      exact hNw z hz
    rw [hsum,hKzero w hwU,hQsum,hHdeg,hn,if_pos (Or.inl rfl)]
  refine ⟨⟨L,hLG,hforest,?_,hcol,?_,?_,?_,?_⟩⟩
  · convert hdeg using 1
    congr! 8
  · convert hdemand using 1
    congr! 8
  · convert hlow using 1
    congr! 8
  · convert TwoColourTrimming.maxDegree_sdiff_of_degree_demands G L hD hLG hdeg hdemand using 1
    congr! 8
  · convert TwoColourTrimming.critical_residue_of_degree_demands G L hc hD hLG hcol hdeg hdemand using 1
    congr! 8

end OverfullWork.SmallLowSpanningLayer
