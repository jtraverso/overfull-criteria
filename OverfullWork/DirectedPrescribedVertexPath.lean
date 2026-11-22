module

public import OverfullWork.DirectedRobustShortPaths
public import OverfullWork.DirectedRouteJoining

@[expose] public section


/-! Actual short simple directed path through prescribed distinct
vertices in their given order. This is the iterative path construction
in KLO Corollary 6.8, with an explicit finite deletion budget. -/
namespace OverfullWork.DirectedPrescribedVertexPath
open Finset DirectedRobustExpansion DirectedListRoutes DirectedRobustShortPaths
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 12000000

theorem exists_ordered_path (D : Digraph V) (r r' t L : ℕ)
    (hRobust : IsRobustAt D r t) (hr' : 0 < r')
    (hL : Fintype.card V/r'+3 ≤ L) :
    ∀ (marks : List V) (Z : Finset V) (x : V),
      (x :: marks).Nodup →
      (∀ v∈x :: marks,v∉Z) →
      Z.card+marks.length*(L+2)+r' ≤ r →
      (∀ v∈x :: marks,t+Z.card+marks.length*(L+2) ≤ outDegree D v) →
      (∀ v∈x :: marks,t ≤ inDegree D v) →
      ∃ l,(x :: l).IsChain D.Adj ∧
        (x :: l).getLast?=(x :: marks).getLast? ∧
        (x :: l).Nodup ∧ marks.Sublist l ∧ l.length ≤ marks.length*L ∧
        ∀ v∈x :: l,v∉Z := by
  intro marks
  induction marks with
  | nil =>
    intro Z x _ hAvoid _ _ _
    exact ⟨[],.singleton _,rfl,by simp,by simp,by simp,hAvoid⟩
  | cons y ys ih =>
    intro Z x hDistinct hAvoid hBudget hOut hIn
    have hXY : x≠y := by
      intro he
      exact (List.nodup_cons.mp hDistinct).1 (by simp [he])
    have hxYS : x∉ys := fun hh => (List.nodup_cons.mp hDistinct).1 (List.mem_cons_of_mem _ hh)
    have hyYS : y∉ys := (List.nodup_cons.mp (List.nodup_cons.mp hDistinct).2).1
    let F := Z∪ys.toFinset
    have hF : F.card ≤ Z.card+ys.length :=
      (card_union_le _ _).trans (Nat.add_le_add_left (List.toFinset_card_le _) _)
    have hxF : x∉F := by
      intro hh
      rcases mem_union.mp hh with hh|hh
      · exact hAvoid x (by simp) hh
      · exact hxYS (List.mem_toFinset.mp hh)
    have hyF : y∉F := by
      intro hh
      rcases mem_union.mp hh with hh|hh
      · exact hAvoid y (by simp) hh
      · exact hyYS (List.mem_toFinset.mp hh)
    have hCount : Z.card+ys.length ≤ Z.card+(y :: ys).length*(L+2) := by
      simp only [List.length_cons]
      nlinarith only [Nat.zero_le (ys.length*L)]
    obtain ⟨l,hRoute,hSimple,hLength,hPathAvoid⟩ := exists_short_path_avoiding D F r r' t
      hRobust hr' (by omega) x y hxF hyF
      (by have hh := hOut x (by simp);omega) (hIn y (by simp))
    have hLen : l.length ≤ L := hLength.trans hL
    let Z' := Z∪((x :: l).toFinset.erase y)
    have hZ' : Z'.card ≤ Z.card+L+1 := by
      have h₁ := card_union_le Z ((x :: l).toFinset.erase y)
      have h₂ := card_erase_le (s:=(x :: l).toFinset) (a:=y)
      have h₃ := List.toFinset_card_le (x :: l)
      simp only [List.length_cons] at h₃
      dsimp only [Z']
      omega
    have hFuture : ∀ v∈y :: ys,v∉Z' := by
      intro v hv hh
      rcases mem_union.mp hh with hh|hh
      · exact hAvoid v (List.mem_cons_of_mem _ hv) hh
      · obtain ⟨hvy,hvL⟩ := mem_erase.mp hh
        rcases List.mem_cons.mp hv with rfl|hv
        · exact hvy rfl
        · exact hPathAvoid v (List.mem_toFinset.mp hvL)
            (mem_union_right _ (List.mem_toFinset.mpr hv))
    have hPaid : Z'.card+ys.length*(L+2) ≤ Z.card+(y :: ys).length*(L+2) := by
      simp only [List.length_cons]
      nlinarith only [hZ']
    obtain ⟨s,hsChain,hsLast,hsSimple,hsSub,hsLen,hsAvoid⟩ := ih Z' y
      (List.nodup_cons.mp hDistinct).2 hFuture (by omega)
      (fun v hv => by have hh := hOut v (List.mem_cons_of_mem _ hv);omega)
      (fun v hv => hIn v (List.mem_cons_of_mem _ hv))
    have hsNoY : y∉s := (List.nodup_cons.mp hsSimple).1
    have hsDisjoint : ∀ v∈s,v∉x :: l := by
      intro v hv hvL
      have hvy : v≠y := by intro he;subst v;exact hsNoY hv
      exact hsAvoid v (List.mem_cons_of_mem _ hv)
        (mem_union_right _ (mem_erase.mpr ⟨hvy,List.mem_toFinset.mpr hvL⟩))
    have hyL : y∈l := by
      have hh : y∈x :: l := List.mem_of_mem_getLast? (by rw [hRoute.2];rfl)
      rcases List.mem_cons.mp hh with hh|hh
      · exact False.elim (hXY hh.symm)
      · exact hh
    refine ⟨l++s,join_chain D hRoute hsChain,?_,?_,?_,?_,?_⟩
    · rw [join_last hRoute.2,hsLast,List.getLast?_cons_cons]
    · change ((x :: l)++s).Nodup
      apply List.nodup_append.mpr
      refine ⟨hSimple,(List.nodup_cons.mp hsSimple).2,?_⟩
      intro v hv w hw he
      subst w
      exact hsDisjoint v hw hv
    · exact (List.singleton_sublist.mpr hyL).append hsSub
    · simp only [List.length_append,List.length_cons]
      nlinarith only [hLen,hsLen]
    · intro v hv hh
      change v∈(x :: l)++s at hv
      rcases List.mem_append.mp hv with hv|hv
      · exact hPathAvoid v hv (mem_union_left _ hh)
      · exact hsAvoid v (List.mem_cons_of_mem _ hv) (mem_union_left _ hh)

end OverfullWork.DirectedPrescribedVertexPath
