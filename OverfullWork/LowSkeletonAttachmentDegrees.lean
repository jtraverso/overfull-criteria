module

public import OverfullWork.PaperLowSkeleton
public import OverfullWork.LowSkeletonProjection

@[expose] public section


/-! # Exact degree budgets after attaching endpoint representatives

Projection edges avoid the low set. They are disjoint from the crossing
skeleton, and its original core leaves are exactly replaced by their
injectively chosen representatives. An outside-degree-one skeleton also
covers the odd construction with one fresh additional edge.
-/
namespace OverfullWork.LowSkeletonAttachmentDegrees
open SimpleGraph Finset PaperLowSkeleton LowSkeletonProjection
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G H : SimpleGraph V} [DecidableRel H.Adj]
  {W U Z : Finset V}
set_option maxHeartbeats 3000000

/-- Projection edges never meet the low set. -/
theorem no_matching_adj_at_low (hWU : W⊆U)
    (P : Projection G (outerLeaves H W) U Z) {w : V} (hw : w∈W) (v : V) :
    ¬P.matching.Adj w v := by
  intro hadj
  rcases P.endpoints w v hadj with h|h
  · exact (mem_compl.mp (mem_filter.mp (mem_inter.mp h.1).1).1) hw
  · exact h.2.1 (hWU hw)

/-- Every projection edge avoids W, whereas every skeleton edge meets W. -/
theorem attachment_disjoint (hWU : W⊆U)
    (hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (P : Projection G (outerLeaves H W) U Z) : Disjoint H P.matching := by
  apply disjoint_iff_inf_le.mpr
  intro u v ⟨hH,hN⟩
  rcases hcross u v hH with h|h
  · exact (no_matching_adj_at_low hWU P h.1 v hN).elim
  · exact (no_matching_adj_at_low hWU P h.1 u hN.symm).elim

/-- The attachment uses only actual graph edges. -/
theorem attachment_le (hHG : H≤G) (P : Projection G (outerLeaves H W) U Z) :
    H⊔P.matching≤G := sup_le hHG P.matching_le

/-- Disjoint attachments add their actual degrees. -/
theorem degree_attachment (hWU : W⊆U)
    (hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (P : Projection G (outerLeaves H W) U Z) (v : V) :
    (H⊔P.matching).degree v=H.degree v+P.matching.degree v := by
  rw [←card_neighborFinset_eq_degree,neighborFinset_sup,
    card_union_of_disjoint (disjoint_neighborFinset_of_disjoint H P.matching v
      (attachment_disjoint hWU hcross P)),
    card_neighborFinset_eq_degree,card_neighborFinset_eq_degree]

/-- Projection leaves the degree of every low vertex unchanged. -/
theorem degree_on_low (hWU : W⊆U)
    (hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (P : Projection G (outerLeaves H W) U Z) {w : V} (hw : w∈W) :
    (H⊔P.matching).degree w=H.degree w := by
  have hz : P.matching.degree w=0 := by
    by_contra hn
    obtain ⟨v,hv⟩:=(P.matching.degree_pos_iff_exists_adj w).mp (Nat.pos_of_ne_zero hn)
    exact no_matching_adj_at_low hWU P hw v hv
  rw [degree_attachment hWU hcross P,hz,Nat.add_zero]

/-- In particular, an original matching endpoint remains degree one. -/
theorem degree_one_on_low (hWU : W⊆U)
    (hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (P : Projection G (outerLeaves H W) U Z)
    (hone : ∀w∈W,H.degree w=1) {w : V} (hw : w∈W) :
    (H⊔P.matching).degree w=1 := by
  rw [degree_on_low hWU hcross P hw,hone w hw]

/-- Outside-degree-one is the extra property needed by the odd fresh-edge
skeleton; together with its two-degree bound it prevents branching. -/
theorem degree_le_two (hWU : W⊆U)
    (hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (hdeg : ∀v,H.degree v≤2) (hout : ∀v∉W,H.degree v≤1)
    (P : Projection G (outerLeaves H W) U Z) (v : V) :
    (H⊔P.matching).degree v≤2 := by
  by_cases hv : v∈W
  · rw [degree_on_low hWU hcross P hv]
    exact hdeg v
  · rw [degree_attachment hWU hcross P]
    have hH:=hout v hv
    have hN:=matching_degree_le_one P.matching P.isMatching v
    omega

/-- Original core leaves receive no projection edge themselves. -/
theorem matching_degree_zero_on_outer_core
    (P : Projection G (outerLeaves H W) U Z) {v : V}
    (hvU : v∉U) (hvA : v∈outerLeaves H W) : P.matching.degree v=0 := by
  by_contra hn
  obtain ⟨w,hw⟩:=(P.matching.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hn)
  rcases P.endpoints v w hw with h|h
  · exact hvU (mem_inter.mp h.1).2
  · exact h.2.2 (mem_union_left _ hvA)

/-- Core vertices have degree at most one in the attached skeleton. -/
theorem degree_le_one_on_core (hWU : W⊆U)
    (hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (hout : ∀v∉W,H.degree v≤1)
    (P : Projection G (outerLeaves H W) U Z) {v : V} (hvU : v∉U) :
    (H⊔P.matching).degree v≤1 := by
  have hvW : v∉W := fun hw => hvU (hWU hw)
  rw [degree_attachment hWU hcross P]
  by_cases hpos : 0<H.degree v
  · have hone : H.degree v=1 := by have hh:=hout v hvW;omega
    have hvA : v∈outerLeaves H W:=mem_filter.mpr ⟨mem_compl.mpr hvW,hone⟩
    rw [matching_degree_zero_on_outer_core P hvU hvA,hone]
  · have hz : H.degree v=0 := by omega
    rw [hz,Nat.zero_add]
    exact matching_degree_le_one P.matching P.isMatching v

/-- The positive core vertices are exactly the actual representatives. -/
theorem core_positive_iff_representative (hWU : W⊆U)
    (hout : ∀v∉W,H.degree v≤1)
    (P : Projection G (outerLeaves H W) U Z) {v : V} (hvU : v∉U) :
    0<(H⊔P.matching).degree v ↔
      ∃a : outerLeaves H W,(P.representative a).val=v := by
  constructor
  · intro hp
    obtain ⟨w,hw⟩:=((H⊔P.matching).degree_pos_iff_exists_adj v).mp hp
    rcases hw with hH|hN
    · have hvW : v∉W := fun h => hvU (hWU h)
      have hpos:0<H.degree v:=(H.degree_pos_iff_exists_adj v).mpr ⟨w,hH⟩
      have hone:H.degree v=1:=by have hh:=hout v hvW;omega
      have hvA:v∈outerLeaves H W:=mem_filter.mpr ⟨mem_compl.mpr hvW,hone⟩
      exact ⟨⟨v,hvA⟩,P.fixed ⟨v,hvA⟩ hvU⟩
    · rcases P.endpoints v w hN with h|h
      · exact False.elim (hvU (mem_inter.mp h.1).2)
      · obtain ⟨hwA,hwU⟩:=mem_inter.mp h.1
        let a : outerLeaves H W:=⟨w,hwA⟩
        have he : v=(P.representative a).val:=
          P.isMatching w v (P.representative a).val hN.symm (P.selected a hwU)
        exact ⟨a,he.symm⟩
  · rintro ⟨a,ha⟩
    by_cases hau : a.val∈U
    · apply ((H⊔P.matching).degree_pos_iff_exists_adj v).mpr
      refine ⟨a.val,Or.inr ?_⟩
      rw [←ha]
      exact (P.selected a hau).symm
    · have he:a.val=v:=(P.fixed a hau).symm.trans ha
      have hp:0<H.degree a.val:=by rw [(mem_filter.mp a.property).2];omega
      obtain ⟨w,hw⟩:=(H.degree_pos_iff_exists_adj a.val).mp hp
      apply ((H⊔P.matching).degree_pos_iff_exists_adj v).mpr
      exact ⟨w,Or.inl (he ▸ hw)⟩

/-- Exact core-degree formula, including isolated core vertices. -/
theorem degree_on_core (hWU : W⊆U)
    (hcross : ∀u v,H.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W))
    (hout : ∀v∉W,H.degree v≤1)
    (P : Projection G (outerLeaves H W) U Z) {v : V} (hvU : v∉U) :
    (H⊔P.matching).degree v=
      if ∃a : outerLeaves H W,(P.representative a).val=v then 1 else 0 := by
  have hle:=degree_le_one_on_core hWU hcross hout P hvU
  have hi:=core_positive_iff_representative hWU hout P hvU
  split_ifs with h
  · have hp:=hi.mpr h
    omega
  · have hn:¬0<(H⊔P.matching).degree v:=fun hp => h (hi.mp hp)
    omega

end OverfullWork.LowSkeletonAttachmentDegrees
