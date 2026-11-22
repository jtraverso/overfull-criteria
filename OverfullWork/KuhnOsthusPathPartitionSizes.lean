module

public import OverfullWork.KuhnOsthusPathPartition
public import OverfullWork.DirectedDemandHall

@[expose] public section


/-! Count the residual exceptional cover and bound the style and size
of each assembled system in Kühn–Osthus Lemma 8.1. -/
namespace OverfullWork.DirectedRobustExpansion

open DirectedDemandHall (Arc)
variable {V : Type*} [Fintype V]

/-- A covering path system with every arc incident to exactly one
exceptional vertex has two arcs per exceptional vertex. -/
theorem card_arcs_of_exceptional_cover {D : Digraph V} {Z : Finset V}
    (hP : IsDirectedPathSystem D) (hCov : CoversExceptional D Z)
    (hCross : ∀ {x y}, D.Adj x y → (x ∈ Z ∧ y ∉ Z) ∨ (x ∉ Z ∧ y ∈ Z)) :
    Fintype.card (Arc D) = 2 * Z.card := by
  classical
  let f (e : Arc D) : Z ⊕ Z :=
    if h : e.val.1 ∈ Z then Sum.inl ⟨e.val.1,h⟩
    else Sum.inr ⟨e.val.2,((hCross e.prop).resolve_left (fun hx => h hx.1)).2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      by_cases ha : a.val.1 ∈ Z
      · by_cases hb : b.val.1 ∈ Z
        · simp only [f,dif_pos ha,dif_pos hb,Sum.inl.injEq,Subtype.mk.injEq] at he
          apply Subtype.ext
          apply Prod.ext he
          have hB : D.Adj a.val.1 b.val.2 := by rw [he]; exact b.prop
          exact hP.out_unique a.prop hB
        · simp only [f,dif_pos ha,dif_neg hb,Sum.inl_ne_inr] at he
      · by_cases hb : b.val.1 ∈ Z
        · simp only [f,dif_neg ha,dif_pos hb,Sum.inr_ne_inl] at he
        · simp only [f,dif_neg ha,dif_neg hb,Sum.inr.injEq,Subtype.mk.injEq] at he
          apply Subtype.ext
          apply Prod.ext _ he
          have hB : D.Adj b.val.1 a.val.2 := by rw [he]; exact b.prop
          exact hP.in_unique a.prop hB
    · rintro (x | y)
      · obtain ⟨z,hz⟩ := (hCov x x.prop).1
        exact ⟨⟨(x,z),hz⟩,by simp [f,x.prop]⟩
      · obtain ⟨z,hz⟩ := (hCov y y.prop).2
        have hn : z ∉ Z := ((hCross hz).resolve_left (fun hp => hp.2 y.prop)).1
        exact ⟨⟨(z,y),hz⟩,by simp [f,hn]⟩
  rw [Fintype.card_congr (Equiv.ofBijective f hf),Fintype.card_sum,Fintype.card_coe]
  omega

theorem card_arcs_le_sum_of_sup (A B : Digraph V) :
    Fintype.card (Arc (A ⊔ B)) ≤ Fintype.card (Arc A) + Fintype.card (Arc B) := by
  classical
  let f (e : Arc (A ⊔ B)) : Arc A ⊕ Arc B :=
    if h : A.Adj e.val.1 e.val.2 then Sum.inl ⟨e.val,h⟩
    else Sum.inr ⟨e.val,((Digraph.sup_adj _ _ _ _).mp e.prop).resolve_left h⟩
  have hf : Function.Injective f := by
    intro a b he
    have he' := congrArg (Sum.elim (fun a : Arc A => a.val) (fun b : Arc B => b.val)) he
    have hv (e : Arc (A ⊔ B)) :
        Sum.elim (fun a : Arc A => a.val) (fun b : Arc B => b.val) (f e) = e.val := by
      dsimp only [f]
      split <;> rfl
    rw [hv,hv] at he'
    exact Subtype.ext he'
  simpa only [Fintype.card_sum] using Fintype.card_le_of_injective f hf

theorem card_arcs_le_of_path_piece_support {A H C Q : Digraph V}
    (hQ : Q ≤ A ⊔ H ⊔ C) :
    Fintype.card (Arc Q) ≤ Fintype.card (Arc A) + Fintype.card (Arc H) +
      Fintype.card (Arc C) := by
  let f (e : Arc Q) : Arc (A ⊔ H ⊔ C) := ⟨e.val,hQ e.prop⟩
  have hf : Function.Injective f := fun _ _ h =>
    Subtype.ext (congrArg (fun a : Arc (A ⊔ H ⊔ C) => a.val) h)
  apply (Fintype.card_le_of_injective f hf).trans
  exact (card_arcs_le_sum_of_sup (A ⊔ H) C).trans
    (Nat.add_le_add_right (card_arcs_le_sum_of_sup A H) _)

variable {J : Type*}

/-- The style of a path system contains the style of every ordinary
vertex incident to one of its arcs. -/
def SupportedByStyles (label : V → J)
    (Z : Finset V) (S : Finset J) (D : Digraph V) : Prop :=
  ∀ x, x ∉ Z → IncidentTo D x → label x ∈ S

omit [Fintype V] in
theorem styles_of_path_piece_support [DecidableEq J]
    {label : V → J} {Z : Finset V} {A H C Q : Digraph V} {a h c : Finset J}
    (hQ : Q ≤ A ⊔ H ⊔ C) (hA : SupportedByStyles label Z a A)
    (hH : SupportedByStyles label Z h H) (hC : SupportedByStyles label Z c C) :
    SupportedByStyles label Z (a ∪ h ∪ c) Q := by
  intro x hx hInc
  have edge {u v : V} (hq : Q.Adj u v) :
      (A.Adj u v ∨ H.Adj u v) ∨ C.Adj u v := hQ hq
  have hInc' : (IncidentTo A x ∨ IncidentTo H x) ∨ IncidentTo C x := by
    rcases hInc with ⟨w,hw⟩ | ⟨w,hw⟩
    · exact (edge hw).imp (fun hp => hp.imp (fun hh => Or.inl ⟨w,hh⟩)
        (fun hh => Or.inl ⟨w,hh⟩)) (fun hc => Or.inl ⟨w,hc⟩)
    · exact (edge hw).imp (fun hp => hp.imp (fun hh => Or.inr ⟨w,hh⟩)
        (fun hh => Or.inr ⟨w,hh⟩)) (fun hc => Or.inr ⟨w,hc⟩)
  rcases hInc' with (ha | hh) | hc
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hA x hx ha))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hH x hx hh))
  · exact Finset.mem_union_right _ (hC x hx hc)

omit [Fintype V] in
theorem disjoint_ordinary_vertices_of_styles [DecidableEq J]
    {label : V → J} {Z : Finset V} {A B : Digraph V} {S T : Finset J}
    (hA : SupportedByStyles label Z S A) (hB : SupportedByStyles label Z T B)
    (hDis : Disjoint S T) :
    ∀ v, v ∉ Z → IncidentTo A v → ¬ IncidentTo B v := by
  intro v hv ha hb
  exact Finset.disjoint_left.mp hDis (hA v hv ha) (hB v hv hb)

omit [Fintype V] in
theorem supported_styles_of_residual_slot [DecidableEq J] {ι : Type*}
    {label : V → J} {Z : Finset V} {H C : ι → Digraph V} {R : Digraph V} {S : Finset J}
    (hR : ∀ x y, R.Adj x y → ∃ i, (C i).Adj x y ∧
      ((∃ w, (H i).Adj x w) ∨ (∃ w, (H i).Adj w y)))
    (hStyles : ∀ i, (∃ x y, (H i).Adj x y) → SupportedByStyles label Z S (C i)) :
    SupportedByStyles label Z S R := by
  intro v hv hInc
  have transfer {x y : V} (h : R.Adj x y) :
      ∃ i, (C i).Adj x y ∧ SupportedByStyles label Z S (C i) := by
    obtain ⟨i,hc,hh⟩ := hR x y h
    refine ⟨i,hc,hStyles i ?_⟩
    rcases hh with ⟨w,hw⟩ | ⟨w,hw⟩
    · exact ⟨x,w,hw⟩
    · exact ⟨w,y,hw⟩
  rcases hInc with ⟨w,hw⟩ | ⟨w,hw⟩
  · obtain ⟨i,hi,hs⟩ := transfer hw
    exact hs v hv (Or.inl ⟨w,hi⟩)
  · obtain ⟨i,hi,hs⟩ := transfer hw
    exact hs v hv (Or.inr ⟨w,hi⟩)

end OverfullWork.DirectedRobustExpansion
