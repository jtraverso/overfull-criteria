module

public import OverfullWork.LargeCentreMatchingStep

@[expose] public section


/-! # CMS Claim 4.5, equation (4.8): exact odd-deficiency loss

The paper's def_G(S) is cut(S)+deficitMass(G,Delta,S), not merely the
ambient vertex deficit. The actual vertices not saturated by the matching
inside S form a finite set. Its cardinality is the exact loss in def_G(S)
when the matching is removed and the maximum drops by one.
-/
namespace OverfullWork.MatchingOddDeficiency
open SimpleGraph Finset OddCutDeficit
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

noncomputable def unmatchedWithin (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V) : Finset V :=
  S.filter fun v=>(Plantholt.nbIn F S v).card=0

theorem sum_inside_degrees (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V) :
    (∑v∈S,(Plantholt.nbIn F S v).card)=2*internalEdges F S := by
  classical
  rw [internalEdges_eq_multigraph,←MultiGraph.twiceInternal_eq]
  unfold MultiGraph.twiceInternal
  apply sum_congr rfl
  intro v _
  have hEq:Plantholt.nbIn F S v=S.filter (F.Adj v):=by
    ext w
    simp only [Plantholt.nbIn,mem_filter,mem_neighborFinset]
    tauto
  rw [hEq,card_eq_sum_ones,sum_filter]
  simp only [MultiGraph.ofSimpleGraph,mem_edgeSet]

/-- The unsaturated vertices are counted from the actual internal
matching, rather than defined by subtracting its edge count. -/
theorem twice_internal_add_unmatched (F : SimpleGraph V) [DecidableRel F.Adj]
    (hF : ∀v,F.degree v≤1) (S : Finset V) :
    2*internalEdges F S+(unmatchedWithin F S).card=S.card := by
  classical
  have hLocal:∀v∈S,(Plantholt.nbIn F S v).card+
      (if (Plantholt.nbIn F S v).card=0 then 1 else 0)=1:=by
    intro v _
    have hLe:(Plantholt.nbIn F S v).card≤1:=by
      exact ((card_le_card (filter_subset _ _)).trans
        (by simpa only [card_neighborFinset_eq_degree,←SimpleGraph.card_neighborSet_eq_degree,
          ←Nat.card_eq_fintype_card] using hF v))
    split_ifs <;>omega
  have hSum:=sum_congr rfl hLocal
  rw [sum_add_distrib,sum_inside_degrees] at hSum
  have hCount:(∑v∈S,if (Plantholt.nbIn F S v).card=0 then 1 else 0)=
      (unmatchedWithin F S).card:=by
    simp only [unmatchedWithin,card_eq_sum_ones,sum_filter]
  rw [hCount] at hSum
  simpa using hSum

theorem unmatched_odd (F : SimpleGraph V) [DecidableRel F.Adj]
    (hF : ∀v,F.degree v≤1) (S : Finset V) (hOdd : Odd S.card) :
    Odd (unmatchedWithin F S).card := by
  have hCount:=twice_internal_add_unmatched F hF S
  obtain ⟨k,hk⟩:=hOdd
  exact ⟨k-internalEdges F S,by omega⟩

theorem internal_edges_sdiff_add (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (hFG : F≤G) (S : Finset V) :
    internalEdges (G\F) S+internalEdges F S=internalEdges G S := by
  classical
  have hDegree:∀v,(G\F).degree v+F.degree v=G.degree v:=by
    intro v
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G F hFG v
  have hSum:=sum_congr (s₁:=S) (s₂:=S) rfl (fun v _=>hDegree v)
  rw [sum_add_distrib] at hSum
  have hG:=internal_cut_identity G S
  have hF:=internal_cut_identity F S
  have hR:=internal_cut_identity (G\F) S
  have hCut:=AlmostOverfullLayerCompatibility.cutEdges_eq_residue_add_layer G F hFG S
  omega

/-- Published equation (4.8), with the paper's internal deficiency
written in terms of the existing cut and ambient-deficit interfaces. -/
theorem deficiency_loss_eq_unmatched (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (hFG : F≤G)
    (hF : ∀v,F.degree v≤1) (hD : 0<G.maxDegree)
    (hDrop : (G\F).maxDegree=G.maxDegree-1) (S : Finset V) :
    (cutEdges (G\F) S+deficitMass (G\F) (G\F).maxDegree S)+
      (unmatchedWithin F S).card=cutEdges G S+deficitMass G G.maxDegree S := by
  have hTheta:=twice_internal_add_unmatched F hF S
  have hEdges:=internal_edges_sdiff_add G F hFG S
  have hG:=internal_cut_deficit_identity G G.maxDegree G.degree_le_maxDegree S
  have hR:=internal_cut_deficit_identity (G\F) (G\F).maxDegree (G\F).degree_le_maxDegree S
  have hProduct:(G.maxDegree-1)*S.card+S.card=G.maxDegree*S.card:=by
    rw [←Nat.add_one_mul,Nat.sub_add_cancel hD]
  rw [hDrop] at hR ⊢
  omega

/-- When exactly one vertex of an odd set is unsaturated internally,
original no-overfullness alone pays the entire published deficiency loss. -/
theorem internal_nonoverfull_of_one_unmatched (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (hFG : F≤G)
    (hF : ∀v,F.degree v≤1) (hD : 0<G.maxDegree)
    (hDrop : (G\F).maxDegree=G.maxDegree-1) (hNo : ¬G.HasOverfullSubgraph)
    (S : Finset V) (hOdd : Odd S.card) (hOne : (unmatchedWithin F S).card=1) :
    internalEdges (G\F) S≤(G\F).maxDegree*(S.card/2) := by
  have hEq:=deficiency_loss_eq_unmatched G F hFG hF hD hDrop S
  have hOld:=(no_overfull_iff_odd_cut_deficit G).mp hNo S hOdd
  apply (odd_internal_bound_iff_cut_deficit (G\F) (G\F).maxDegree
    (G\F).degree_le_maxDegree S hOdd).mpr
  rw [hOne] at hEq
  omega

theorem internal_zero_of_independent (H : SimpleGraph V) [DecidableRel H.Adj]
    (Y : Finset V) (hInd : H.IsIndepSet (Y:Set V)) : internalEdges H Y=0 := by
  have hTwice:(MultiGraph.ofSimpleGraph H).twiceInternal Y=0:=by
    unfold MultiGraph.twiceInternal
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro b hb
    have hNo:¬H.Adj a b:=fun hab=>hInd ha hb hab.ne hab
    simp [MultiGraph.ofSimpleGraph,mem_edgeSet,hNo]
  have hh:=(MultiGraph.ofSimpleGraph H).twiceInternal_eq Y
  rw [hTwice,←internalEdges_eq_multigraph] at hh
  omega

theorem cut_eq_complementary_degree_sum (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (hInd : H.IsIndepSet (↑(Sᶜ):Set V)) :
    cutEdges H S=∑v∈Sᶜ,H.degree v := by
  have hCut:=internal_cut_identity H Sᶜ
  rw [internal_zero_of_independent H Sᶜ hInd,NearTightOddSetGeometry.cutEdges_compl] at hCut
  simpa only [Nat.mul_zero,Nat.zero_add] using hCut

/-- Lemma 3.11 in the induced-odd-set form used repeatedly in Claim 4.5.
Being one below Delta is already sufficient because the parity agrees. -/
theorem odd_budget_of_one_below (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (hOdd : Odd S.card)
    (hNear : H.maxDegree≤cutEdges H S+deficitMass H H.maxDegree S+1) :
    H.maxDegree≤cutEdges H S+deficitMass H H.maxDegree S := by
  have hId:=internal_cut_deficit_identity H H.maxDegree H.degree_le_maxDegree S
  obtain ⟨m,hm⟩:=hOdd
  have hProduct:H.maxDegree*S.card=2*(H.maxDegree*m)+H.maxDegree:=by rw [hm];ring
  rw [hProduct] at hId
  omega

theorem internal_edges_le_of_le (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H≤G) (S : Finset V) :
    internalEdges H S ≤ internalEdges G S := by
  apply card_le_card
  intro e he
  obtain ⟨heH,heS⟩:=mem_filter.mp he
  exact mem_filter.mpr ⟨edgeFinset_mono hHG heH,heS⟩

/-- Cleanup can only increase the paper's deficiency when it preserves
Delta; this is the inequality following (4.8) in Claim 4.5. -/
theorem deficiency_mono_of_le_same_maximum (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H≤G)
    (hMax : H.maxDegree=G.maxDegree) (S : Finset V) :
    cutEdges G S+deficitMass G G.maxDegree S≤cutEdges H S+deficitMass H H.maxDegree S := by
  have hEdges:=internal_edges_le_of_le G H hHG S
  have hG:=internal_cut_deficit_identity G G.maxDegree G.degree_le_maxDegree S
  have hH:=internal_cut_deficit_identity H H.maxDegree H.degree_le_maxDegree S
  rw [hMax] at hH ⊢
  omega

/-- All matching neighbours lie in S if vertices outside S have degree
zero. The internal matching degree is then its actual ambient degree. -/
theorem inside_degree_eq_of_supported (F : SimpleGraph V) [DecidableRel F.Adj]
    (S : Finset V) (hOff : ∀v∉S,F.degree v=0) (v : V) :
    (Plantholt.nbIn F S v).card=F.degree v := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel F.Adj)
    (fun a b=>Classical.propDecidable (F.Adj a b)))
  have hEq:Plantholt.nbIn F S v=F.neighborFinset v:=by
    unfold Plantholt.nbIn
    apply filter_eq_self.mpr
    intro w hw
    by_contra hNot
    have hZero:=hOff w hNot
    have hPos:0<F.degree w:=(F.degree_pos_iff_exists_adj w).mpr
      ⟨v,((mem_neighborFinset F v w).mp hw).symm⟩
    omega
  rw [hEq,card_neighborFinset_eq_degree]

theorem unmatched_eq_singleton_of_supported (F : SimpleGraph V) [DecidableRel F.Adj]
    (S : Finset V) (x : V) (hx : x∈S) (hOff : ∀v∉S,F.degree v=0)
    (hOn : ∀v∈S,F.degree v=if v=x then 0 else 1) :
    unmatchedWithin F S={x} := by
  ext v
  rw [unmatchedWithin,mem_filter,mem_singleton,inside_degree_eq_of_supported F S hOff v]
  constructor
  · rintro ⟨hv,hZero⟩
    have hh:=hOn v hv
    by_contra hNot
    rw [if_neg hNot] at hh
    omega
  · intro he
    subst v
    exact ⟨hx,by simpa using hOn x hx⟩

end OverfullWork.MatchingOddDeficiency
