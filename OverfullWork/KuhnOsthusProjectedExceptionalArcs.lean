module

public import OverfullWork.KuhnOsthusCycleAbsorberOriginalArcs
public import OverfullWork.KuhnOsthusCycleAbsorberConstruction

@[expose] public section


/-! Equip a projected exceptional path cover with the original arcs
with which it is realized. Exact restoration preserves both the
ordinary routing arcs and each supplied original interval. -/
namespace OverfullWork.DirectedRobustExpansion

open Function Finset
open scoped Classical
variable {V Z J K : Type*}

structure ProjectedExceptionalArcs (G : Digraph (V ⊕ Z)) (P : Digraph V) (atVertex : J → Z) where
  source : J ↪ V
  target : J → V
  shortcut : ∀ j, P.Adj (source j) (target j)
  path_arcs : ∀ j, G.Adj (.inl (source j)) (.inr (atVertex j)) ∧
    G.Adj (.inr (atVertex j)) (.inl (target j))
  ordinary : ∀ {x y}, P.Adj x y → x ∉ Set.range source → G.Adj (.inl x) (.inl y)

def liftOrdinaryCycleArcs (Z : Type*) (O : Digraph V) : Digraph (V ⊕ Z) :=
  ⟨fun x y => match x,y with | .inl a,.inl b => O.Adj a b | _,_ => False⟩

def ProjectedExceptionalArcs.original {G : Digraph (V ⊕ Z)} {P : Digraph V} {atVertex : J → Z}
    (E : ProjectedExceptionalArcs G P atVertex) : Digraph (V ⊕ Z) :=
  ⟨fun x y => match x,y with
    | .inl u,.inl v => P.Adj u v ∧ u ∉ Set.range E.source
    | .inl u,.inr z => ∃ j, E.source j = u ∧ atVertex j = z
    | .inr z,.inl v => ∃ j, atVertex j = z ∧ E.target j = v
    | .inr _,.inr _ => False⟩

theorem ProjectedExceptionalArcs.original_le {G : Digraph (V ⊕ Z)} {P : Digraph V}
    {atVertex : J → Z} (E : ProjectedExceptionalArcs G P atVertex) : E.original ≤ G := by
  rintro (x | z) (y | w) h
  · exact E.ordinary h.1 h.2
  · obtain ⟨j,rfl,rfl⟩ := h
    exact (E.path_arcs j).1
  · obtain ⟨j,rfl,rfl⟩ := h
    exact (E.path_arcs j).2
  · exact h.elim

/-- The original intervals are arc-disjoint when they occupy
distinct ordinary incoming and outgoing slots. -/
theorem ProjectedExceptionalArcs.original_disjoint_of_slots
    {G : Digraph (V ⊕ Z)} {P Q : Digraph V} {e : J → Z} {f : K → Z}
    (E : ProjectedExceptionalArcs G P e) (F : ProjectedExceptionalArcs G Q f)
    (hOut : ∀ {x a y z}, P.Adj x y → Q.Adj a z → x ≠ a)
    (hIn : ∀ {x a y z}, P.Adj x y → Q.Adj a z → y ≠ z) :
    Disjoint E.original F.original := by
  rw [disjoint_iff_inf_le]
  rintro (x | z) (y | w) ⟨h,h'⟩
  · exact hOut h.1 h'.1 rfl
  · obtain ⟨j,hj,_⟩ := h
    obtain ⟨k,hk,_⟩ := h'
    exact hOut (E.shortcut j) (F.shortcut k) (hj.trans hk.symm)
  · obtain ⟨j,_,hj⟩ := h
    obtain ⟨k,_,hk⟩ := h'
    exact hIn (E.shortcut j) (F.shortcut k) (hj.trans hk.symm)
  · exact h

/-- Join two projected systems with disjoint outgoing slots. No
ordinary edge of one system can be a shortcut of the other. -/
def ProjectedExceptionalArcs.join {G : Digraph (V ⊕ Z)} {P Q : Digraph V}
    {e : J → Z} {f : K → Z} (E : ProjectedExceptionalArcs G P e)
    (F : ProjectedExceptionalArcs G Q f)
    (hSeparate : ∀ x, (∃ y, P.Adj x y) → (∃ y, Q.Adj x y) → False) :
    ProjectedExceptionalArcs G (P ⊔ Q) (Sum.elim e f) where
  source := ⟨Sum.elim E.source F.source,by
    rintro (j | k) (j' | k') r
    · exact congrArg Sum.inl (E.source.injective r)
    · change E.source j = F.source k' at r
      exact (hSeparate _ ⟨_,E.shortcut j⟩ ⟨_,r.symm ▸ F.shortcut k'⟩).elim
    · change F.source k = E.source j' at r
      exact (hSeparate _ ⟨_,r.symm ▸ E.shortcut j'⟩ ⟨_,F.shortcut k⟩).elim
    · exact congrArg Sum.inr (F.source.injective r)⟩
  target := Sum.elim E.target F.target
  shortcut := by
    rintro (j | k)
    · exact .inl (E.shortcut j)
    · exact .inr (F.shortcut k)
  path_arcs := by
    rintro (j | k)
    · exact E.path_arcs j
    · exact F.path_arcs k
  ordinary := by
    rintro x y (he | hf) hn
    · exact E.ordinary he (fun ⟨j,hj⟩ => hn ⟨.inl j,hj⟩)
    · exact F.ordinary hf (fun ⟨j,hj⟩ => hn ⟨.inr j,hj⟩)

theorem ProjectedExceptionalArcs.join_original {G : Digraph (V ⊕ Z)} {P Q : Digraph V}
    {e : J → Z} {f : K → Z} (E : ProjectedExceptionalArcs G P e)
    (F : ProjectedExceptionalArcs G Q f)
    (hSeparate : ∀ x, (∃ y, P.Adj x y) → (∃ y, Q.Adj x y) → False) :
    (E.join F hSeparate).original = E.original ⊔ F.original := by
  ext x y
  rcases x with x | z <;> rcases y with y | w
  · constructor
    · rintro ⟨he | hf,hn⟩
      · exact .inl ⟨he,fun ⟨j,hj⟩ => hn ⟨.inl j,hj⟩⟩
      · exact .inr ⟨hf,fun ⟨j,hj⟩ => hn ⟨.inr j,hj⟩⟩
    · rintro (⟨he,hn⟩ | ⟨hf,hn⟩)
      · refine ⟨.inl he,?_⟩
        rintro ⟨j | k,r⟩
        · exact hn ⟨j,r⟩
        · change F.source k = x at r
          exact hSeparate x ⟨_,he⟩ ⟨_,r ▸ F.shortcut k⟩
      · refine ⟨.inr hf,?_⟩
        rintro ⟨j | k,r⟩
        · change E.source j = x at r
          exact hSeparate x ⟨_,r ▸ E.shortcut j⟩ ⟨_,hf⟩
        · exact hn ⟨k,r⟩
  · constructor
    · rintro ⟨j | k,hj,hw⟩
      · exact .inl ⟨j,hj,hw⟩
      · exact .inr ⟨k,hj,hw⟩
    · rintro (⟨j,hj,hw⟩ | ⟨k,hk,hw⟩)
      · exact ⟨.inl j,hj,hw⟩
      · exact ⟨.inr k,hk,hw⟩
  · constructor
    · rintro ⟨j | k,hj,hw⟩
      · exact .inl ⟨j,hj,hw⟩
      · exact .inr ⟨k,hj,hw⟩
    · rintro (⟨j,hj,hw⟩ | ⟨k,hk,hw⟩)
      · exact ⟨.inl j,hj,hw⟩
      · exact ⟨.inr k,hk,hw⟩
  · exact ⟨False.elim,fun h => h.elim id id⟩

/-- A projected permutation factor restores to the exact original
interval arcs and the retained ordinary routes. -/
theorem ProjectedExceptionalArcs.restore_exact {G : Digraph (V ⊕ Z)} {P O : Digraph V}
    {e : J → Z} (E : ProjectedExceptionalArcs G P e) (σ : Equiv.Perm V)
    (hFactor : ∀ x y, (O ⊔ P).Adj x y ↔ σ x = y)
    (hSep : ∀ {x y}, O.Adj x y → ¬ P.Adj x y) :
    restoreExceptionalFactor σ E.source e = liftOrdinaryCycleArcs Z O ⊔ E.original := by
  have hTarget (j : J) : σ (E.source j) = E.target j := (hFactor _ _).mp (.inr (E.shortcut j))
  ext x y
  rcases x with x | z <;> rcases y with y | w
  · constructor
    · rintro ⟨h,hn⟩
      exact ((hFactor _ _).mpr h).elim Or.inl (fun hp => .inr ⟨hp,hn⟩)
    · rintro (ho | ⟨hp,hn⟩)
      · have h := (hFactor _ _).mp (.inl ho)
        refine ⟨h,?_⟩
        rintro ⟨j,rfl⟩
        exact hSep ho ((hTarget j).symm.trans h ▸ E.shortcut j)
      · exact ⟨(hFactor _ _).mp (.inr hp),hn⟩
  · exact ⟨Or.inr,fun h => h.elim False.elim id⟩
  · constructor
    · rintro ⟨j,hj,hy⟩
      exact .inr ⟨j,hj,(hTarget j).symm.trans hy⟩
    · rintro (h | ⟨j,hj,hy⟩)
      · exact h.elim
      · exact ⟨j,hj,(hTarget j).trans hy⟩
  · exact ⟨False.elim,fun h => h.elim id id⟩

end OverfullWork.DirectedRobustExpansion
