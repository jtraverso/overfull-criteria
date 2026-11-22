module

public import OverfullWork.CMSOperation41ProjectionAssembly
public import OverfullWork.CMSOperation41CorePacking

@[expose] public section


/-! The projected layer separates into the prescribed words and the
ordinary host edges from the simultaneous packing. The host parts
remain disjoint when mapped back to the source and gaps are omitted. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph DirectedSpanningConfiguration DirectedRobustExpansion
open scoped Classical

variable {V C J : Type*}

private theorem infix_map_pair_iff (e : C ↪ V) (T : List C) (a b : V) :
    List.IsInfix [a,b] (T.map e) ↔
      ∃ u v,e u = a ∧ e v = b ∧ List.IsInfix [u,v] T := by
  constructor
  · intro h
    obtain ⟨S,hS,hMap⟩ := List.infix_map_iff.mp h
    cases S with
    | nil => simp at hMap
    | cons u S =>
      cases S with
      | nil => simp at hMap
      | cons v S =>
        have hTail : S = [] := by
          have hl := congrArg List.length hMap
          simp at hl
          exact hl
        have he : [a,b] = [e u,e v] := by
          simpa only [hTail,List.map_cons,List.map_nil] using hMap
        obtain ⟨ha,hb⟩ := by simpa using he
        have hS' : List.IsInfix [u,v] T := by simpa only [hTail] using hS
        exact ⟨u,v,ha.symm,hb.symm,hS'⟩
  · rintro ⟨u,v,rfl,rfl,h⟩
    exact h.map e

theorem mapped_host_edges_disjoint {I : J → Type*} {G : SimpleGraph C}
    {L : ∀ j,Layout C (I j)} (P : CMSPacking I G L) (e : C ↪ V) :
    Pairwise fun i j => Disjoint ((hostEdges G (P.configuration i).used).map e)
      ((hostEdges G (P.configuration j).used).map e) := by
  intro i j hij
  rw [disjoint_iff_inf_le]
  intro x y h
  obtain ⟨u,v,hi,rfl,rfl⟩ := (SimpleGraph.map_adj e _ _ _).mp h.1
  obtain ⟨a,b,hj,ha,hb⟩ := (SimpleGraph.map_adj e _ _ _).mp h.2
  have h₁ : a = u := e.injective ha
  have h₂ : b = v := e.injective hb
  subst a b
  have hCopy (k : J) (hk : (hostEdges G (P.configuration k).used).Adj u v) :
      Sum.inl (β := Σ j, I j) s(u,v) ∈ P.copies k := by
    change s(u,v) ∈ (hostEdges G (P.configuration k).used).edgeSet
    exact (hostEdges G (P.configuration k).used).mem_edgeSet.mpr hk
  exact ((Set.disjoint_left.mp (P.copies_pairwise hij)) (hCopy i hi) (hCopy j hj)).elim

theorem physical_layer_eq_prescribed_sup_host
    {n : ℕ} (e : C ↪ V) (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ C)
    (fixed : Finset (Fin (n+1))) (isolated : Finset C)
    {G : SimpleGraph C} {D : Digraph C} (hOr : IsOrientationOf D G)
    (P : Realization D (cyclicLayout hn w fixed isolated))
    (external : Fin (n+1) → List V) (gaps : Finset (Sym2 V)) (F Q : SimpleGraph V)
    (hF : ∀ a b,F.Adj a b ↔ s(a,b) ∉ gaps ∧
      ∃ i ∈ fixed,List.IsInfix [a,b] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))]) ∨
        List.IsInfix [b,a] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))])) :
    let body := realizedReplacementInterior e fixed P.interior external
    (∀ a b,Q.Adj a b ↔ s(a,b) ∉ gaps ∧
      ∃ i,List.IsInfix [a,b] (e (w i) :: body i ++ [e (w (finRotate (n+1) i))]) ∨
        List.IsInfix [b,a] (e (w i) :: body i ++ [e (w (finRotate (n+1) i))])) →
    Q = F ⊔ ((hostEdges G P.used).map e).deleteEdges (gaps : Set (Sym2 V)) := by
  intro body hQ
  have hFlexible (a b : V) :
      ((hostEdges G P.used).map e).Adj a b ↔
        ∃ i ∉ fixed,List.IsInfix [a,b] ((P.word i).map e) ∨ List.IsInfix [b,a] ((P.word i).map e) := by
    constructor
    · intro hab
      obtain ⟨u,v,hAdj,rfl,rfl⟩ := (SimpleGraph.map_adj e _ _ _).mp hab
      rcases hAdj.2 with h | h
      · obtain ⟨⟨i,hi⟩,huv⟩ := Digraph.iSup_adj.mp h
        exact ⟨i,hi,Or.inl (List.IsInfix.map e huv)⟩
      · obtain ⟨⟨i,hi⟩,hvu⟩ := Digraph.iSup_adj.mp h
        exact ⟨i,hi,Or.inr (List.IsInfix.map e hvu)⟩
    · rintro ⟨i,hi,h | h⟩
      · obtain ⟨u,v,rfl,rfl,huv⟩ := (infix_map_pair_iff e (P.word i) a b).mp h
        have h' : P.used.Adj u v := Digraph.iSup_adj.mpr ⟨⟨i,hi⟩,huv⟩
        exact (SimpleGraph.map_adj e _ _ _).mpr ⟨u,v,⟨hOr.1 u v (P.used_le h'),Or.inl h'⟩,rfl,rfl⟩
      · obtain ⟨v,u,rfl,rfl,hvu⟩ := (infix_map_pair_iff e (P.word i) b a).mp h
        have h' : P.used.Adj v u := Digraph.iSup_adj.mpr ⟨⟨i,hi⟩,hvu⟩
        exact (SimpleGraph.map_adj e _ _ _).mpr
          ⟨u,v,⟨(hOr.1 v u (P.used_le h')).symm,Or.inr h'⟩,rfl,rfl⟩
  ext a b
  rw [hQ,sup_adj,hF,deleteEdges_adj,hFlexible]
  constructor
  · rintro ⟨hGap,i,hi⟩
    by_cases hFixed : i ∈ fixed
    · exact Or.inl ⟨hGap,i,hFixed,by simpa only [body,realizedReplacementInterior,if_pos hFixed] using hi⟩
    · refine Or.inr ⟨⟨i,hFixed,?_⟩,hGap⟩
      simpa only [body,realizedReplacementInterior,if_neg hFixed,Realization.word,cyclicLayout,
        List.map_cons,List.map_append,List.map_nil] using hi
  · rintro (⟨hGap,i,hi,hFixed⟩ | ⟨⟨i,hi,hFlex⟩,hGap⟩)
    · exact ⟨hGap,i,by simpa only [body,realizedReplacementInterior,if_pos hi] using hFixed⟩
    · refine ⟨hGap,i,?_⟩
      simpa only [body,realizedReplacementInterior,if_neg hi,Realization.word,cyclicLayout,
        List.map_cons,List.map_append,List.map_nil] using hFlex

end OverfullWork.CMSTrimmingRound
