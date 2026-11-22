module

public import OverfullWork.DirectedLayoutRoundCompletion

@[expose] public section


/-! Degrees after removing the short paths and adding the marker,
as in GGKLO Lemma 7.3(i), (III') and (IV'). -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedLongLayoutPath
open scoped Classical
variable {V I : Type*} [Fintype V]

/-- All vertices lost from the dense side belong to the layout or to a
short interior. The bound also pays for isolated layout vertices. -/
theorem ShortPortion.dense_trim_bound [Fintype I]
    {K : Digraph V} {L : Layout V I} {long : I}
    (S : ShortPortion K L long) (A : Finset V) (h : ℕ)
    (hLen : ∀ i ∉ insert long L.fixed, (S.interior i).length ≤ h) :
    (Aᶜ \ S.denseVertices A).card ≤ L.boundary.card+(univ \ insert long L.fixed).card*h := by
  let J : Finset I := univ \ insert long L.fixed
  let U := J.biUnion fun i => (S.interior i).toFinset
  have hSub : Aᶜ \ S.denseVertices A ⊆ L.boundary ∪ U := by
    intro x hx
    have hxA : x ∉ A := mem_compl.mp (mem_sdiff.mp hx).1
    have hNot : ¬S.remaining x := by
      intro hr
      exact (mem_sdiff.mp hx).2 (by simp [ShortPortion.denseVertices,hr,hxA])
    by_cases hv : x ∈ L.boundary
    · exact mem_union_left _ hv
    · apply mem_union_right
      by_contra hm
      apply hNot
      refine ⟨hv,fun i hi hi' => hm ?_⟩
      exact mem_biUnion.mpr ⟨i,by simp [J,hi],List.mem_toFinset.mpr hi'⟩
  exact (card_le_card hSub).trans ((card_union_le _ _).trans (Nat.add_le_add_left
    (card_biUnion_le_card_mul _ _ _ fun i hi =>
      (List.toFinset_card_le _).trans (hLen i (mem_sdiff.mp hi).2)) _))

omit [Fintype V] in
private theorem filter_option_card (Y : Finset V) (P : V → Prop) (Q : Prop) :
    ((univ : Finset (Option Y)).filter (fun x => x.elim Q (fun y => P y.val))).card =
      (if Q then 1 else 0)+(Y.filter P).card := by
  rw [card_filter]
  let f : Option Y → ℕ := fun x => if x.elim Q (fun y => P y.val) then 1 else 0
  change (∑ x, f x) = _
  rw [Fintype.sum_option,card_filter]
  have h := Finset.sum_attach Y (fun x => if P x then (1:ℕ) else 0)
  rw [← univ_eq_attach Y] at h
  exact congrArg (fun z : ℕ => (if Q then 1 else 0)+z) h


omit [Fintype V] in
private theorem card_filter_trim (B Y : Finset V) (hY : Y ⊆ B) (P : V → Prop) :
    (Y.filter P).card ≤ (B.filter P).card ∧
    (B.filter P).card ≤ (Y.filter P).card+(B \ Y).card := by
  have hSub : Y.filter P ⊆ B.filter P := filter_subset_filter P hY
  have hDiff : B.filter P \ Y.filter P ⊆ B \ Y := by
    intro v hv
    simp only [mem_sdiff,mem_filter] at hv ⊢
    exact ⟨hv.1.1,fun h => hv.2 ⟨h,hv.1.2⟩⟩
  have hCard := card_sdiff_add_card_eq_card hSub
  have hp := card_le_card hDiff
  exact ⟨card_le_card hSub,by omega⟩

/-- The incoming profile is the residual host profile into the
representative, with at most one additional arc from the marker. -/
theorem dense_marker_inDegree_bounds {W : Type*} (D : Digraph V) (e : W ↪ V)
    (B Y : Finset V) (hY : Y ⊆ B) (a b : V) (x : Option Y) :
    let d : Y ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    let P := B.filter (fun v => D.Adj v (x.elim b d))
    let k := inDegree (denseWithMarker D e d a b) x
    k ≤ P.card+1 ∧ P.card ≤ k+(B \ Y).card := by
  intro d P k
  have he : k = (if D.Adj a (x.elim b d) then 1 else 0) +
      (Y.filter (fun w => D.Adj w (x.elim b d))).card :=
    by
      dsimp only [k]
      unfold inDegree inNeighbours
      convert filter_option_card Y (fun w => D.Adj w (x.elim b d))
        (D.Adj a (x.elim b d)) using 2
      ext y
      cases y <;>
        exact ⟨fun h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩,
          fun h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩⟩
  have h := card_filter_trim B Y hY (fun w => D.Adj w (x.elim b d))
  change (Y.filter _).card ≤ P.card ∧ P.card ≤ (Y.filter _).card+(B \ Y).card at h
  rw [he]
  split <;> omega

/-- The outgoing profile inherits the source representative and loses
only arcs to deleted vertices, with at most one new arc to the marker. -/
theorem dense_marker_outDegree_bounds {W : Type*} (D : Digraph V) (e : W ↪ V)
    (B Y : Finset V) (hY : Y ⊆ B) (a b : V) (x : Option Y) :
    let d : Y ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    let P := B.filter (fun v => D.Adj (x.elim a d) v)
    let k := outDegree (denseWithMarker D e d a b) x
    k ≤ P.card+1 ∧ P.card ≤ k+(B \ Y).card := by
  intro d P k
  have he : k = (if D.Adj (x.elim a d) b then 1 else 0) +
      (Y.filter (fun w => D.Adj (x.elim a d) w)).card :=
    by
      dsimp only [k]
      unfold outDegree
      convert filter_option_card Y (fun w => D.Adj (x.elim a d) w)
        (D.Adj (x.elim a d) b) using 2
      ext y
      cases y <;>
        exact ⟨fun h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩,
          fun h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩⟩
  have h := card_filter_trim B Y hY (fun w => D.Adj (x.elim a d) w)
  change (Y.filter _).card ≤ P.card ∧ P.card ≤ (Y.filter _).card+(B \ Y).card at h
  rw [he]
  split <;> omega

end OverfullWork.DirectedSpanningConfiguration
