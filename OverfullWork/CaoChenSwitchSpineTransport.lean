module

public import OverfullWork.CaoChenLocatedPaletteSwitching
public import OverfullWork.CaoChenPaletteKempeTransport
public import OverfullWork.CaoChenSwitchingOverlap

@[expose] public section


/-! # The actual selected palette at a spine after a located switching

The spine row is an explicitly located Kempe row. Its selected bad palette
is therefore transported by the transposition if the spine belongs to the
component, and is unchanged otherwise. No transport outcome is assumed.
-/
namespace OverfullWork.CaoChenSwitchSpineTransport
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenPaletteKempeTransport
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

omit [DecidableEq V] in
private theorem mem_image_swap_iff (T : Finset (Fin G.maxDegree))
    (δ θ γ : Fin G.maxDegree) :
    γ∈T.image (Equiv.swap δ θ) ↔ Equiv.swap δ θ γ∈T := by
  constructor
  · rintro h
    obtain ⟨τ,hτ,hτγ⟩:=mem_image.mp h
    rw [←hτγ,Equiv.swap_apply_self]
    exact hτ
  · intro h
    exact mem_image.mpr ⟨Equiv.swap δ θ γ,h,by simp⟩

/-- Exact transport of the selected bad/S palette at an unchanged
non-target spine row, including protected memberships and score monotonicity. -/
theorem exists_selected_transport_general (hG : IsClassTwo G)
    {c c' : PEC G (Fin G.maxDegree)} {x y w u : V} {η θ δ : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (q : ℝ)
    (hηA : η∈paletteA c q x y) (hδx : c.IsFree x δ) (hθy : c.IsFree y θ)
    (hfull : SwitchingResult c c' q x y w η θ)
    (hrow : ∀v,c'.col u v=(c.kempeSwap δ θ w).col u v)
    (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u∩paletteS c q x y)
    (hηT : η∈T) (hδT : δ∉T)
    (hδF : δ∉F) (hθF : θ∉F) :
    ∃T' : Finset (Fin G.maxDegree),
      T'=(if (c.kempeGraph δ θ).Reachable w u then T.image (Equiv.swap δ θ) else T) ∧
      T'⊆badColours c' q u∩paletteS c' q x y ∧ T'.card=T.card ∧
      (∀γ∈F,γ∈T'↔γ∈T) ∧
      (T∩missing c x).card≤(T'∩missing c' x).card ∧
      η∈T' ∧ (c'.IsFree u η↔c.IsFree u η) ∧
      ∀v,(c'.col u v=some η↔c.col u v=some η) := by
  have hθx : ¬c.IsFree x θ := fun h => (hcm.ab_facts hG).1 θ h hθy
  have hηx : ¬c.IsFree x η :=
    (mem_presentColours c x η).mp ((mem_paletteA c q x y η).mp hηA).1
  have hηδ : η≠δ := by intro he;exact hηx (he.symm ▸ hδx)
  have hηθ : η≠θ := by
    intro he
    obtain ⟨_,v,hyv,_⟩:=(mem_paletteA c q x y η).mp hηA
    exact hθy v (he ▸ hyv)
  have hηcol : ∀v,(c'.col u v=some η↔c.col u v=some η) := by
    intro v
    rw [hrow]
    by_cases hr : (c.kempeGraph δ θ).Reachable w u
    · rw [col_eq_swap_iff c δ θ hr,Equiv.swap_apply_of_ne_of_ne hηδ hηθ]
    · rw [kempeSwap_col,kempeSwapFun_of_not_reachable c δ θ hr]
  have hηu' : c'.IsFree u η↔c.IsFree u η := by
    constructor
    · intro hf v hv
      exact hf v ((hηcol v).mpr hv)
    · intro hf v hv
      exact hf v ((hηcol v).mp hv)
  have hbad : badColours c' q u=badColours (c.kempeSwap δ θ w) q u := by
    ext γ
    simp only [mem_badColours,IsFree]
    simp_rw [hrow]
  have hmissing : missing c' x=missing c x := by
    ext γ
    simp only [mem_missing,IsFree,hfull.leftRow]
  have hδS : δ∈paletteS c q x y :=
    (mem_paletteS_iff_free_or_bad c q x y δ).mpr (Or.inl hδx)
  have hθS : θ∈paletteS c q x y :=
    (mem_paletteS_iff_free_or_bad c q x y θ).mpr
      (Or.inr ((mem_badColours c q y θ).mpr (Or.inl hθy)))
  by_cases hr : (c.kempeGraph δ θ).Reachable w u
  · refine ⟨T.image (Equiv.swap δ θ),by rw [if_pos hr],?_,?_,?_,?_,?_,hηu',hηcol⟩
    · intro γ hγ
      have hold : Equiv.swap δ θ γ∈T := (mem_image_swap_iff T δ θ γ).mp hγ
      refine mem_inter.mpr ⟨?_,?_⟩
      · rw [hbad]
        exact (mem_bad_swap_iff c q δ θ hr γ).mpr (mem_inter.mp (hT hold)).1
      · rw [hfull.palette_eq]
        exact image_swap_subset_paletteS c q x y T (fun _ h => (mem_inter.mp (hT h)).2) hδS hθS hγ
    · exact card_image_of_injective T (Equiv.swap δ θ).injective
    · intro γ hγ
      rw [mem_image_swap_iff T δ θ γ,Equiv.swap_apply_of_ne_of_ne
        (show γ≠δ by intro he;exact hδF (he ▸ hγ))
        (show γ≠θ by intro he;exact hθF (he ▸ hγ))]
    · rw [hmissing]
      apply card_le_card
      intro γ hγ
      obtain ⟨hγT,hγx⟩:=mem_inter.mp hγ
      have hγδ : γ≠δ := by intro he;exact hδT (he ▸ hγT)
      have hγθ : γ≠θ := by intro he;exact hθx (he ▸ mem_missing.mp hγx)
      refine mem_inter.mpr ⟨?_,hγx⟩
      exact mem_image.mpr ⟨γ,hγT,Equiv.swap_apply_of_ne_of_ne hγδ hγθ⟩
    · exact mem_image.mpr ⟨η,hηT,Equiv.swap_apply_of_ne_of_ne hηδ hηθ⟩
  · have hbad' : badColours c' q u=badColours c q u := by
      rw [hbad]
      ext γ
      simp only [mem_badColours,IsFree,kempeSwap_col,kempeSwapFun_of_not_reachable c δ θ hr]
    refine ⟨T,by rw [if_neg hr],?_,rfl,fun _ _ => Iff.rfl,?_,hηT,hηu',hηcol⟩
    · rw [hbad',hfull.palette_eq]
      exact hT
    · rw [hmissing]

/-- The missing-at-spine specialization, with the same explicit selected
palette as the general transport theorem. -/
theorem exists_selected_transport (hG : IsClassTwo G)
    {c c' : PEC G (Fin G.maxDegree)} {x y w u : V} {η θ δ : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (q : ℝ)
    (hηA : η∈paletteA c q x y) (hδx : c.IsFree x δ) (hθy : c.IsFree y θ)
    (hfull : SwitchingResult c c' q x y w η θ)
    (hrow : ∀v,c'.col u v=(c.kempeSwap δ θ w).col u v)
    (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u∩paletteS c q x y)
    (hηT : η∈T) (hηu : c.IsFree u η) (hδT : δ∉T)
    (hδF : δ∉F) (hθF : θ∉F) :
    ∃T' : Finset (Fin G.maxDegree),
      T'=(if (c.kempeGraph δ θ).Reachable w u then T.image (Equiv.swap δ θ) else T) ∧
      T'⊆badColours c' q u∩paletteS c' q x y ∧ T'.card=T.card ∧
      (∀γ∈F,γ∈T'↔γ∈T) ∧
      (T∩missing c x).card≤(T'∩missing c' x).card ∧
      η∈T' ∧ c'.IsFree u η := by
  obtain ⟨T',he,hs,hc,hF,hscore,hηT',hηfree,_⟩:=
    exists_selected_transport_general hG hcm q hηA hδx hθy hfull hrow T F hT hηT hδT hδF hθF
  exact ⟨T',he,hs,hc,hF,hscore,hηT',hηfree.mpr hηu⟩

end OverfullWork.CaoChenSwitchSpineTransport
