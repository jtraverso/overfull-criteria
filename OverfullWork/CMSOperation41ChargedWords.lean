module

public import OverfullWork.CMSOperation41MatchingArms

@[expose] public section


/-! The charged endpoints of CMS S2.2.1 and S2.4.1 and the singleton
part of S2.1 use the same projected arms. When a singleton has both
chosen edges, their join is physical. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private def projectionArm {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a : A) : List V :=
  if a.val ∈ U then [a.val,(P.representative a).val] else [(P.representative a).val]

private theorem projection_arm_mem {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a : A) (v : V) :
    v ∈ projectionArm P a ↔ v = (P.representative a).val ∨ (a.val ∈ U ∧ v = a.val) := by
  by_cases h : a.val ∈ U <;> simp [projectionArm,h,or_comm]

private theorem projection_arm_shape {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a : A) :
    (projectionArm P a).Nodup ∧ (projectionArm P a).IsChain G.Adj ∧
      (projectionArm P a).head? = some a.val ∧
      (projectionArm P a).getLast? = some (P.representative a).val := by
  by_cases h : a.val ∈ U
  · have hOut := mem_compl.mp (P.representative a).property
    have hn : a.val ≠ (P.representative a).val := fun hh => hOut (hh ▸ h)
    simp [projectionArm,h,hn,List.isChain_cons_cons,P.neighbour a h]
  · simp [projectionArm,h,P.fixed a h]

private theorem projection_arms_disjoint {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) {a b : A} (hab : a ≠ b) :
    List.Disjoint (projectionArm P a) (projectionArm P b) := by
  intro v ha hb
  have hOut (a : A) : (P.representative a).val ∉ U := mem_compl.mp (P.representative a).property
  rcases (projection_arm_mem P a v).mp ha with ha' | ⟨hA,ha'⟩ <;>
    rcases (projection_arm_mem P b v).mp hb with hb' | ⟨hB,hb'⟩
  · exact hab (P.injective (Subtype.ext (ha'.symm.trans hb')))
  · exact hOut a (ha' ▸ (hb'.symm ▸ hB))
  · exact hOut b (hb' ▸ (ha'.symm ▸ hA))
  · exact hab (Subtype.ext (ha'.symm.trans hb'))

private theorem projection_arm_exceptional {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a : A) (v : V)
    (hv : v ∈ projectionArm P a) (hU : v ∈ U) : v = a.val := by
  rcases (projection_arm_mem P a v).mp hv with h | ⟨_,h⟩
  · exact ((mem_compl.mp (P.representative a).property) (h ▸ hU)).elim
  · exact h

private theorem ordinary_member_projection_arm {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a : A) (v : V)
    (hv : v ∈ projectionArm P a) (hU : v ∉ U) : v = (P.representative a).val := by
  rcases (projection_arm_mem P a v).mp hv with h | ⟨ha,h⟩
  · exact h
  · exact (hU (h.symm ▸ ha)).elim

theorem charged_pair_replacement_word_with_core_endpoints {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a b : A) (hab : a ≠ b) :
    ∃ T : List V,T.Nodup ∧ T.head? = some (P.representative a).val ∧
      T.getLast? = some (P.representative b).val ∧
      T.IsChain (fun x y => G.Adj x y ∨ (x = a.val ∧ y = b.val)) ∧
      List.IsInfix [a.val,b.val] T ∧
      (∀ v ∈ T,v ∈ U → v = a.val ∨ v = b.val) ∧
      ∀ v ∈ T,v ∉ U → v = (P.representative a).val ∨ v = (P.representative b).val := by
  have hA := projection_arm_shape P a
  have hB := projection_arm_shape P b
  have hJ := join_projected_arms G _ _ _ _ hA.2.2.1 hB.2.2.1 hA.1 hB.1
    (projection_arms_disjoint P hab) hA.2.1 hB.2.1
  refine ⟨(projectionArm P a).reverse ++ projectionArm P b,hJ.1,
    hJ.2.1.trans hA.2.2.2,hJ.2.2.1.trans hB.2.2.2,hJ.2.2.2.1,hJ.2.2.2.2,?_,?_⟩
  · intro v hv hu
    rcases List.mem_append.mp hv with h | h
    · exact Or.inl (projection_arm_exceptional P a v (List.mem_reverse.mp h) hu)
    · exact Or.inr (projection_arm_exceptional P b v h hu)
  · intro v hv hu
    rcases List.mem_append.mp hv with h | h
    · exact Or.inl (ordinary_member_projection_arm P a v (List.mem_reverse.mp h) hu)
    · exact Or.inr (ordinary_member_projection_arm P b v h hu)

theorem charged_pair_replacement_word {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a b : A) (hab : a ≠ b) :
    ∃ T : List V,T.Nodup ∧ T.head? = some (P.representative a).val ∧
      T.getLast? = some (P.representative b).val ∧
      T.IsChain (fun x y => G.Adj x y ∨ (x = a.val ∧ y = b.val)) ∧
      List.IsInfix [a.val,b.val] T ∧
      ∀ v ∈ T,v ∈ U → v = a.val ∨ v = b.val := by
  obtain ⟨T,hSimple,hHead,hLast,hChain,hGap,hExceptional,_⟩ :=
    charged_pair_replacement_word_with_core_endpoints P a b hab
  exact ⟨T,hSimple,hHead,hLast,hChain,hGap,hExceptional⟩

theorem singleton_projected_replacement_word_with_leaf_positions {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a b : A) (hab : a ≠ b)
    (w : V) (hw : w ∈ U) (hwa : G.Adj w a.val) (hwb : w ≠ b.val) :
    ∃ T : List V,T.Nodup ∧ T.head? = some (P.representative a).val ∧
      T.getLast? = some (P.representative b).val ∧
      T.IsChain (fun x y => G.Adj x y ∨ (x = w ∧ y = b.val)) ∧ List.IsInfix [w,b.val] T ∧
      (G.Adj w b.val → T.IsChain G.Adj) ∧
      (∀ v ∈ U,v ∈ T ↔ v = w ∨ v = a.val ∨ v = b.val) ∧
      (∀ v ∈ T,v ∉ U → v = (P.representative a).val ∨ v = (P.representative b).val) ∧
      T.length = 3+(if a.val ∈ U then 1 else 0)+(if b.val ∈ U then 1 else 0) ∧
      List.IsInfix [a.val,w] T := by
  have hA := projection_arm_shape P a
  have hB := projection_arm_shape P b
  have hAbsentA : w ∉ projectionArm P a := fun h =>
    hwa.ne (projection_arm_exceptional P a w h hw)
  have hAbsentB : w ∉ projectionArm P b := fun h =>
    hwb (projection_arm_exceptional P b w h hw)
  let A₀ := w :: projectionArm P a
  have hNo : A₀.Nodup := List.nodup_cons.mpr ⟨hAbsentA,hA.1⟩
  have hChain : A₀.IsChain G.Adj := by
    apply List.isChain_cons.mpr
    refine ⟨?_,hA.2.1⟩
    intro x hx
    rw [hA.2.2.1] at hx
    exact (Option.mem_some_iff.mp hx) ▸ hwa
  have hEnd : A₀.getLast? = some (P.representative a).val := by
    have hNonempty : projectionArm P a ≠ [] := by intro h; simp [h] at hA
    change (w :: projectionArm P a).getLast? = _
    rw [List.getLast?_cons_of_ne_nil hNonempty,hA.2.2.2]
  have hDis : List.Disjoint A₀ (projectionArm P b) := by
    intro v hv hv'
    rcases List.mem_cons.mp hv with rfl | hh
    · exact hAbsentB hv'
    · exact projection_arms_disjoint P hab hh hv'
  have hJ := join_projected_arms G A₀ _ w b.val rfl hB.2.2.1 hNo hB.1 hDis hChain hB.2.1
  refine ⟨A₀.reverse ++ projectionArm P b,hJ.1,hJ.2.1.trans hEnd,hJ.2.2.1.trans hB.2.2.2,
    hJ.2.2.2.1,hJ.2.2.2.2,?_,?_,?_,?_,?_⟩
  · intro h
    apply hJ.2.2.2.1.imp
    intro u v huv
    rcases huv with huv | ⟨rfl,rfl⟩
    · exact huv
    · exact h
  · intro v hU
    constructor
    · intro hv
      rcases List.mem_append.mp hv with h | h
      · rcases List.mem_cons.mp (List.mem_reverse.mp h) with he | he
        · exact Or.inl he
        · exact Or.inr (Or.inl (projection_arm_exceptional P a v he hU))
      · exact Or.inr (Or.inr (projection_arm_exceptional P b v h hU))
    · rintro (rfl | ha | hb)
      · exact List.mem_append_left _ (List.mem_reverse.mpr List.mem_cons_self)
      · exact List.mem_append_left _ (List.mem_reverse.mpr
          (List.mem_cons_of_mem _ ((projection_arm_mem P a v).mpr (Or.inr ⟨ha ▸ hU,ha⟩))))
      · exact List.mem_append_right _ ((projection_arm_mem P b v).mpr (Or.inr ⟨hb ▸ hU,hb⟩))
  · intro v hv hU
    rcases List.mem_append.mp hv with h | h
    · rcases List.mem_cons.mp (List.mem_reverse.mp h) with rfl | he
      · exact (hU hw).elim
      · exact Or.inl (ordinary_member_projection_arm P a v he hU)
    · exact Or.inr (ordinary_member_projection_arm P b v h hU)
  · have hLength (x : A) : (projectionArm P x).length = 1+(if x.val ∈ U then 1 else 0) := by
      by_cases h : x.val ∈ U <;> simp [projectionArm,h]
    simp only [A₀,List.length_append,List.length_reverse,List.length_cons,hLength]
    omega
  · obtain ⟨tail,htail⟩ := List.head?_eq_some_iff.mp hA.2.2.1
    refine ⟨tail.reverse,projectionArm P b,?_⟩
    simp only [A₀,htail,List.reverse_cons,List.append_assoc]
    rfl

theorem singleton_projected_replacement_word_with_core_endpoints {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a b : A) (hab : a ≠ b)
    (w : V) (hw : w ∈ U) (hwa : G.Adj w a.val) (hwb : w ≠ b.val) :
    ∃ T : List V,T.Nodup ∧ T.head? = some (P.representative a).val ∧
      T.getLast? = some (P.representative b).val ∧
      T.IsChain (fun x y => G.Adj x y ∨ (x = w ∧ y = b.val)) ∧ List.IsInfix [w,b.val] T ∧
      (G.Adj w b.val → T.IsChain G.Adj) ∧
      (∀ v ∈ T,v ∈ U → v = w ∨ v = a.val ∨ v = b.val) ∧
      (∀ v ∈ T,v ∉ U → v = (P.representative a).val ∨ v = (P.representative b).val) ∧
      T.length = 3+(if a.val ∈ U then 1 else 0)+(if b.val ∈ U then 1 else 0) := by
  obtain ⟨T,hNode,hA,hB,hChain,hGap,hKeep,hException,hCore,hLength,_⟩ :=
    singleton_projected_replacement_word_with_leaf_positions P a b hab w hw hwa hwb
  exact ⟨T,hNode,hA,hB,hChain,hGap,hKeep,fun v hv hu => (hException v hu).mp hv,hCore,hLength⟩

theorem singleton_projected_replacement_word {G : SimpleGraph V} {A U Z : Finset V}
    (P : LowSkeletonProjection.Projection G A U Z) (a b : A) (hab : a ≠ b)
    (w : V) (hw : w ∈ U) (hwa : G.Adj w a.val) (hwb : w ≠ b.val) :
    ∃ T : List V,T.Nodup ∧ T.head? = some (P.representative a).val ∧
      T.getLast? = some (P.representative b).val ∧
      T.IsChain (fun x y => G.Adj x y ∨ (x = w ∧ y = b.val)) ∧ List.IsInfix [w,b.val] T ∧
      (G.Adj w b.val → T.IsChain G.Adj) ∧
      ∀ v ∈ T,v ∈ U → v = w ∨ v = a.val ∨ v = b.val := by
  obtain ⟨T,hSimple,hHead,hLast,hChain,hGap,hActual,hExceptional,_,_⟩ :=
    singleton_projected_replacement_word_with_core_endpoints P a b hab w hw hwa hwb
  exact ⟨T,hSimple,hHead,hLast,hChain,hGap,hActual,hExceptional⟩

theorem singleton_matching_choice_avoids_charged_vertex {M₁ M₂ : SimpleGraph V}
    {w x : V} (hDis : Disjoint M₁ M₂)
    (h₁ : ∃ a,M₁.Adj w a) (h₂ : ∃ b,M₂.Adj w b) :
    ∃ a,a ≠ x ∧ (M₁.Adj w a ∨ M₂.Adj w a) := by
  obtain ⟨a,ha⟩ := h₁
  obtain ⟨b,hb⟩ := h₂
  by_cases h : a = x
  · have hn : b ≠ x := by
      intro he
      exact (disjoint_iff_inf_le.mp hDis) ⟨h ▸ ha,he ▸ hb⟩
    exact ⟨b,hn,Or.inr hb⟩
  · exact ⟨a,h,Or.inl ha⟩

end OverfullWork.CMSTrimmingRound
