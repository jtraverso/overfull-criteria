module

public import OverfullWork.CaoChenFinitePaletteProgress

@[expose] public section


/-! # Concrete Case-2 progress from a low leaf with a common root colour

The three missing-colour endpoints force the actual Kempe component at
u to avoid both ends of the deleted edge. The selected palette is then
transported by its exact transposition and gains a root-missing colour.
Every root overlap loses at most one, rather than assuming component avoidance.
-/
namespace OverfullWork.CaoChenLowLeafProgress
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenPaletteKempeTransport CaoChenFinitePaletteProgress
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 3000000

omit [DecidableEq V] in
private theorem mem_image_swap_iff (T : Finset (Fin G.maxDegree))
    (δ τ γ : Fin G.maxDegree) :
    γ∈T.image (Equiv.swap δ τ) ↔ Equiv.swap δ τ γ∈T := by
  constructor
  · intro h
    obtain ⟨η,hη,hηγ⟩:=mem_image.mp h
    rw [←hηγ,Equiv.swap_apply_self]
    exact hη
  · intro h
    exact mem_image.mpr ⟨Equiv.swap δ τ γ,h,by simp⟩

/-- The actual one-unit Case-2 gain, without an off-component oracle.
The degree of the leaf is irrelevant once its common missing colour
has been constructed; low degree is used when obtaining that colour. -/
theorem gain_of_low_leaf_common_root (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u t : V}
    (hcm : IsColMinus c x y) (htx : t≠x)
    (q : ℝ) (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u∩paletteS c q x y)
    {δ τ : Fin G.maxDegree}
    (hδx : c.IsFree x δ) (hτy : c.IsFree y τ)
    (hut : c.col u t=some τ) (hδt : c.IsFree t δ)
    (hτT : τ∈T) (hδT : δ∉T) (hδF : δ∉F) (hτF : τ∉F) :
    Progress c (c.kempeSwap δ τ u) q x y u T (T.image (Equiv.swap δ τ)) F 1 := by
  have hty : t≠y := by
    intro he
    subst t
    exact hτy u (by rw [c.col_symm];exact hut)
  have hlink:=(hcm.ab_facts hG).2 δ τ hδx hτy
  have htoff : ¬(c.kempeGraph δ τ).Reachable t x := by
    intro h
    exact not_three_linked c hcm.adj.ne htx.symm hty.symm
      (Or.inl hδx) (Or.inr hτy) (Or.inl hδt) hlink h.symm
  have htu : (c.kempeGraph δ τ).Reachable t u := by
    apply SimpleGraph.Adj.reachable
    exact ⟨(c.col_adj hut).ne.symm,Or.inr (by rw [c.col_symm];exact hut)⟩
  have hoffx : ¬(c.kempeGraph δ τ).Reachable u x:=fun h => htoff (htu.trans h)
  have hoffy : ¬(c.kempeGraph δ τ).Reachable u y:=fun h => hoffx (h.trans hlink.symm)
  let c':=c.kempeSwap δ τ u
  have hrow : ∀w,c'.col x w=c.col x w:=
    fun w => kempeSwapFun_of_not_reachable c δ τ hoffx w
  have hyrow : ∀w,c'.col y w=c.col y w:=
    fun w => kempeSwapFun_of_not_reachable c δ τ hoffy w
  have hmissing : missing c' x=missing c x := by
    ext γ
    simp only [mem_missing,IsFree,hrow]
  have hτx : ¬c.IsFree x τ:=fun h => (hcm.ab_facts hG).1 τ h hτy
  have hδS : δ∈paletteS c q x y:=
    (mem_paletteS_iff_free_or_bad c q x y δ).mpr (Or.inl hδx)
  have hτS : τ∈paletteS c q x y:=
    (mem_paletteS_iff_free_or_bad c q x y τ).mpr (Or.inr
      ((mem_badColours c q y τ).mpr (Or.inl hτy)))
  have hS : paletteS c' q x y=paletteS c q x y:=
    paletteS_eq_of_endpoint_rows c c' q x y hrow hyrow
  refine ⟨hcm.kempeSwap δ τ u,hrow,?_,?_,?_,?_,?_,?_⟩
  · intro a b γ hγ
    have hγδ : γ≠δ:=fun he => hδF (he ▸ hγ)
    have hγτ : γ≠τ:=fun he => hτF (he ▸ hγ)
    by_cases hr : (c.kempeGraph δ τ).Reachable u a
    · rw [col_eq_swap_iff c δ τ hr,Equiv.swap_apply_of_ne_of_ne hγδ hγτ]
    · change c.kempeSwapFun δ τ u a b=some γ ↔ _
      rw [kempeSwapFun_of_not_reachable c δ τ hr]
  · intro γ hγ
    have hγδ : γ≠δ:=fun he => hδF (he ▸ hγ)
    have hγτ : γ≠τ:=fun he => hτF (he ▸ hγ)
    rw [mem_image_swap_iff T δ τ γ,Equiv.swap_apply_of_ne_of_ne hγδ hγτ]
  · intro γ hγ
    have hold : Equiv.swap δ τ γ∈T:=(mem_image_swap_iff T δ τ γ).mp hγ
    refine mem_inter.mpr ⟨?_,?_⟩
    · exact (mem_bad_swap_iff c q δ τ (SimpleGraph.Reachable.refl u) γ).mpr
        (mem_inter.mp (hT hold)).1
    · rw [hS]
      exact image_swap_subset_paletteS c q x y T (fun η hη => (mem_inter.mp (hT hη)).2)
        hδS hτS hγ
  · exact card_image_of_injective T (Equiv.swap δ τ).injective
  · rw [hmissing]
    exact (swap_inter_card_gain T (missing c x) hτT hδT (mem_missing.mpr hδx)
      (fun h => hτx (mem_missing.mp h))).ge
  · exact root_overlap_drop_le_one_kempe c x δ τ u hoffx hτx

/-- A sufficiently large actual common root palette supplies the auxiliary
colour and constructs the corresponding progress step. -/
theorem exists_low_leaf_candidate_gain (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u t : V}
    (hcm : IsColMinus c x y) (htx : t≠x)
    (q : ℝ) (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u∩paletteS c q x y)
    {τ : Fin G.maxDegree} (hτy : c.IsFree y τ) (hut : c.col u t=some τ)
    (hτT : τ∈T) (hτF : τ∉F)
    (hbudget : F.card+(T∩missing c x).card<(missing c t∩missing c x).card) :
    ∃c' T',Progress c c' q x y u T T' F 1 := by
  obtain ⟨δ,hδx,hδt,hδF,hδT⟩:=exists_common_root_auxiliary c x t F T hbudget
  exact ⟨c.kempeSwap δ τ u,T.image (Equiv.swap δ τ),
    gain_of_low_leaf_common_root hG hcm htx q T F hT hδx hτy hut hδt hτT hδT hδF hτF⟩

end OverfullWork.CaoChenLowLeafProgress
