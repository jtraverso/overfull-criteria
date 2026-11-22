module

public import OverfullWork.CaoChenPaletteKempeTransport
public import OverfullWork.CaoChenSwitchingOverlap
public import OverfullWork.CaoChenLocatedPaletteSwitching
public import OverfullWork.CaoChenSwitchSpineTransport

@[expose] public section


/-! # Actual finite progress of a selected bad palette

The output colourings are constructed by Kempe changes. These local progress
lemmas do not assume a one-step recolouring oracle or a global R1 estimate.
-/
namespace OverfullWork.CaoChenFinitePaletteProgress
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenPaletteKempeTransport
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

/-- The selected palette gains a root-missing colour, with a bounded loss
of root overlap at every vertex. Protected colours retain their exact roles. -/
structure Progress (c c' : PEC G (Fin G.maxDegree)) (q : ℝ) (x y u : V)
    (T T' F : Finset (Fin G.maxDegree)) (loss : ℕ) : Prop where
  cm : IsColMinus c' x y
  rootRow : ∀w,c'.col x w=c.col x w
  protectedColours : ∀a b γ,γ∈F → (c'.col a b=some γ ↔ c.col a b=some γ)
  protectedMembership : ∀γ∈F,γ∈T' ↔ γ∈T
  selected : T'⊆badColours c' q u∩paletteS c' q x y
  card : T'.card=T.card
  gain : (T∩missing c x).card+1≤(T'∩missing c' x).card
  rootDrop : ∀v,(missing c v∩missing c x).card≤(missing c' v∩missing c' x).card+loss

/-- A swap avoiding the root can remove only its root-missing swap colour
from any other vertex's root overlap. -/
theorem root_overlap_drop_le_one_kempe (c : PEC G (Fin G.maxDegree))
    (x : V) (δ η : Fin G.maxDegree) (r : V)
    (hoff : ¬(c.kempeGraph δ η).Reachable r x) (hη : ¬c.IsFree x η) (v : V) :
    (missing c v∩missing c x).card≤
      (missing (c.kempeSwap δ η r) v∩missing (c.kempeSwap δ η r) x).card+1 := by
  have hsub : missing c v∩missing c x⊆
      insert δ (missing (c.kempeSwap δ η r) v∩missing (c.kempeSwap δ η r) x) := by
    intro γ hγ
    by_cases hγδ : γ=δ
    · simp [hγδ]
    apply mem_insert_of_mem
    obtain ⟨hv,hx⟩:=mem_inter.mp hγ
    have hγη : γ≠η := by intro he;exact hη (he ▸ mem_missing.mp hx)
    exact mem_inter.mpr ⟨mem_missing.mpr
      ((kempeSwap_isFree_of_ne c δ η r v hγδ hγη).mpr (mem_missing.mp hv)),
      mem_missing.mpr ((isFree_kempeSwap_of_not_reachable c δ η hoff γ).mpr (mem_missing.mp hx))⟩
  exact (card_le_card hsub).trans (card_insert_le _ _)

/-- Construct a root-missing auxiliary colour outside both finite protected
families. The budget is a cardinal inequality, not a colour-choice oracle. -/
theorem exists_root_auxiliary (c : PEC G (Fin G.maxDegree)) (x : V)
    (F T : Finset (Fin G.maxDegree)) (hbudget : F.card+T.card<(missing c x).card) :
    ∃δ,c.IsFree x δ ∧ δ∉F ∧ δ∉T := by
  obtain ⟨δ,hδ,hnot⟩:=exists_mem_notMem_of_card_lt_card ((card_union_le F T).trans_lt hbudget)
  exact ⟨δ,mem_missing.mp hδ,fun h => hnot (mem_union.mpr (Or.inl h)),
    fun h => hnot (mem_union.mpr (Or.inr h))⟩

omit [DecidableEq V] in
private theorem mem_image_swap_iff (T : Finset (Fin G.maxDegree))
    (δ η γ : Fin G.maxDegree) :
    γ∈T.image (Equiv.swap δ η) ↔ Equiv.swap δ η γ∈T := by
  constructor
  · rintro h
    obtain ⟨τ,hτ,hτγ⟩:=mem_image.mp h
    rw [←hτγ,Equiv.swap_apply_self]
    exact hτ
  · intro h
    exact mem_image.mpr ⟨Equiv.swap δ η γ,h,by simp⟩

/-- An explicit missing-y Kempe gain, including the actual output colouring
and the global one-unit root-overlap loss bound. -/
theorem gain_of_two_missing (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V}
    (hcm : IsColMinus c x y) (hux : u≠x) (huy : u≠y)
    (q : ℝ) (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u∩paletteS c q x y)
    {δ η : Fin G.maxDegree} (hδx : c.IsFree x δ)
    (hηy : c.IsFree y η) (hηu : c.IsFree u η)
    (hηT : η∈T) (hδT : δ∉T) (hδF : δ∉F) (hηF : η∉F) :
    Progress c (c.kempeSwap δ η u) q x y u T (T.image (Equiv.swap δ η)) F 1 := by
  have hlink := (hcm.ab_facts hG).2 δ η hδx hηy
  have hoffx : ¬(c.kempeGraph δ η).Reachable u x := by
    intro h
    exact not_three_linked c hcm.adj.ne hux.symm huy.symm
      (Or.inl hδx) (Or.inr hηy) (Or.inr hηu) hlink h.symm
  have hoffy : ¬(c.kempeGraph δ η).Reachable u y :=
    fun h => hoffx (h.trans hlink.symm)
  let c' := c.kempeSwap δ η u
  let T' := T.image (Equiv.swap δ η)
  have hrow : ∀w,c'.col x w=c.col x w :=
    fun w => kempeSwapFun_of_not_reachable c δ η hoffx w
  have hyrow : ∀w,c'.col y w=c.col y w :=
    fun w => kempeSwapFun_of_not_reachable c δ η hoffy w
  have hmissing : missing c' x=missing c x := by
    ext γ
    simp only [mem_missing,IsFree,hrow]
  have hηx : ¬c.IsFree x η := fun h => (hcm.ab_facts hG).1 η h hηy
  have hδS : δ∈paletteS c q x y :=
    (mem_paletteS_iff_free_or_bad c q x y δ).mpr (Or.inl hδx)
  have hηS : η∈paletteS c q x y :=
    (mem_paletteS_iff_free_or_bad c q x y η).mpr (Or.inr
      ((mem_badColours c q y η).mpr (Or.inl hηy)))
  have hS : paletteS c' q x y=paletteS c q x y :=
    paletteS_eq_of_endpoint_rows c c' q x y hrow hyrow
  refine ⟨hcm.kempeSwap δ η u,hrow,?_,?_,?_,?_,?_,?_⟩
  · intro a b γ hγ
    have hγδ : γ≠δ := fun he => hδF (he ▸ hγ)
    have hγη : γ≠η := fun he => hηF (he ▸ hγ)
    by_cases hr : (c.kempeGraph δ η).Reachable u a
    · rw [col_eq_swap_iff c δ η hr]
      rw [Equiv.swap_apply_of_ne_of_ne hγδ hγη]
    · change c.kempeSwapFun δ η u a b=some γ ↔ _
      rw [kempeSwapFun_of_not_reachable c δ η hr]
  · intro γ hγ
    have hγδ : γ≠δ := fun he => hδF (he ▸ hγ)
    have hγη : γ≠η := fun he => hηF (he ▸ hγ)
    rw [mem_image_swap_iff T δ η γ,Equiv.swap_apply_of_ne_of_ne hγδ hγη]
  · intro γ hγ
    have hold : Equiv.swap δ η γ∈T := (mem_image_swap_iff T δ η γ).mp hγ
    refine mem_inter.mpr ⟨?_,?_⟩
    · exact (mem_bad_swap_iff c q δ η (SimpleGraph.Reachable.refl u) γ).mpr
        (mem_inter.mp (hT hold)).1
    · rw [hS]
      exact image_swap_subset_paletteS c q x y T (fun τ hτ => (mem_inter.mp (hT hτ)).2)
        hδS hηS hγ
  · exact card_image_of_injective T (Equiv.swap δ η).injective
  · rw [hmissing]
    exact (swap_inter_card_gain T (missing c x) hηT hδT (mem_missing.mpr hδx)
      (fun h => hηx (mem_missing.mp h))).ge
  · exact root_overlap_drop_le_one_kempe c x δ η u hoffx hηx

/-- Root cardinality alone supplies the auxiliary colour in the direct
missing-y case. No recolouring witness is assumed. -/
theorem exists_missing_y_candidate_gain (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V}
    (hcm : IsColMinus c x y) (hux : u≠x) (huy : u≠y)
    (q : ℝ) (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u∩paletteS c q x y)
    {η : Fin G.maxDegree} (hηy : c.IsFree y η) (hηu : c.IsFree u η)
    (hηT : η∈T) (hηF : η∉F) (hbudget : F.card+T.card<(missing c x).card) :
    ∃c' T',Progress c c' q x y u T T' F 1 := by
  obtain ⟨δ,hδx,hδF,hδT⟩:=exists_root_auxiliary c x F T hbudget
  exact ⟨c.kempeSwap δ η u,T.image (Equiv.swap δ η),
    gain_of_two_missing hG hcm hux huy q T F hT hδx hηy hηu hηT hδT hδF hηF⟩

/-- A large concrete root overlap at a low leaf supplies the common
auxiliary colour outside the protected family and the selected palette. -/
theorem exists_common_root_auxiliary (c : PEC G (Fin G.maxDegree)) (x z : V)
    (F T : Finset (Fin G.maxDegree))
    (hbudget : F.card+(T∩missing c x).card<(missing c z∩missing c x).card) :
    ∃δ,c.IsFree x δ ∧ c.IsFree z δ ∧ δ∉F ∧ δ∉T := by
  obtain ⟨δ,hδ,hnot⟩:=exists_mem_notMem_of_card_lt_card
    ((card_union_le F (T∩missing c x)).trans_lt hbudget)
  obtain ⟨hδz,hδx⟩:=mem_inter.mp hδ
  refine ⟨δ,mem_missing.mp hδx,mem_missing.mp hδz,?_,?_⟩
  · exact fun h => hnot (mem_union.mpr (Or.inl h))
  · exact fun h => hnot (mem_union.mpr (Or.inr (mem_inter.mpr ⟨h,hδx⟩)))

/-- All intermediate witnesses of the A-colour preparation remain visible.
In particular the conditional selected-palette transport is not hidden behind
an unspecified existential recolouring. -/
structure APreparation (c c' : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y u w : V) (η θ δ : Fin G.maxDegree)
    (T T' F : Finset (Fin G.maxDegree)) : Prop where
  oldColour : c.col y w=some η
  thetaMissing : c.IsFree y θ
  deltaRoot : c.IsFree x δ
  deltaLeaf : c.IsFree w δ
  full : SwitchingResult c c' q x y w η θ
  protectedSwitch : ProtectedPaletteSwitching c c' x y w η θ δ
  rowOff : ∀a,a≠y → a≠w → ∀v,c'.col a v=(c.kempeSwap δ θ w).col a v
  selectedEq : T'=(if (c.kempeGraph δ θ).Reachable w u then T.image (Equiv.swap δ θ) else T)
  selected : T'⊆badColours c' q u∩paletteS c' q x y
  card : T'.card=T.card
  protectedMembership : ∀γ∈F,γ∈T'↔γ∈T
  score : (T∩missing c x).card≤(T'∩missing c' x).card
  candidate : η∈T'
  candidateMissing : c'.IsFree u η
  protectedColours : ∀a b γ,γ∈F → (c'.col a b=some γ↔c.col a b=some γ)

/-- A large root profile at the actual y-eta leaf constructs the A-case
switching and the full selected-palette preparation. -/
theorem exists_A_candidate_preparation (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V}
    (hcm : IsColMinus c x y) (q : ℝ) (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u∩paletteS c q x y)
    {η : Fin G.maxDegree} (hηA : η∈paletteA c q x y)
    (hηu : c.IsFree u η) (hηT : η∈T) (hηF : η∉F)
    (hF : ∀γ∈F,γ∈presentColours c y)
    (hlarge : ∀w,c.col y w=some η →
      F.card+(T∩missing c x).card<(missing c w∩missing c x).card) :
    ∃w θ δ c' T',APreparation c c' q x y u w η θ δ T T' F := by
  obtain ⟨_,w,hyw,_⟩:=(mem_paletteA c q x y η).mp hηA
  obtain ⟨δ,hδx,hδw,hδF,hδT⟩:=exists_common_root_auxiliary c x w F T (hlarge w hyw)
  obtain ⟨θ,hθy⟩:=hcm.exists_free_right
  have hθF : θ∉F := fun h => (mem_presentColours c y θ).mp (hF θ h) hθy
  have huy : u≠y := by intro he;exact hηu w (he ▸ hyw)
  have huw : u≠w := by
    intro he
    exact hηu y (by rw [he,c.col_symm];exact hyw)
  obtain ⟨c',hfull,hprot,_hoff,hrow⟩:=exists_located_full_palette_switching hG hcm q
    η θ δ hηA hyw hθy hδx hδw
  obtain ⟨T',hTeq,hselect,hcard,hFmem,hscore,hηT',hηu'⟩:=
    CaoChenSwitchSpineTransport.exists_selected_transport hG hcm q hηA hδx hθy
      hfull (hrow u huy huw) T F hT hηT hηu hδT hδF hθF
  refine ⟨w,θ,δ,c',T',⟨hyw,hθy,hδx,hδw,hfull,hprot,hrow,hTeq,
    hselect,hcard,hFmem,hscore,hηT',hηu',?_⟩⟩
  intro a b γ hγ
  exact hprot.otherEdges γ (fun he => hηF (he ▸ hγ))
    (fun he => hθF (he ▸ hγ)) (fun he => hδF (he ▸ hγ)) a b

/-- The entire missing-spine A branch gives an actual strict gain. Its
intermediate switching, transported palette, and final literal Kempe swap
are exported together, so subsequent role/margin arguments use the same
witnesses. No finite-iteration or global R1 assertion is made here. -/
theorem exists_A_missing_candidate_gain (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V}
    (hcm : IsColMinus c x y) (hux : u≠x) (huy : u≠y)
    (q : ℝ) (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u∩paletteS c q x y)
    {η : Fin G.maxDegree} (hηA : η∈paletteA c q x y)
    (hηu : c.IsFree u η) (hηT : η∈T) (hηF : η∉F)
    (hF : ∀γ∈F,γ∈presentColours c y)
    (hlarge : ∀w,c.col y w=some η →
      F.card+(T∩missing c x).card<(missing c w∩missing c x).card)
    (hbudget : F.card+T.card<(missing c x).card) :
    ∃w θ δ c₁ T₁ κ,
      APreparation c c₁ q x y u w η θ δ T T₁ F ∧
      c₁.IsFree x κ ∧ κ∉F ∧ κ∉T₁ ∧
      Progress c (c₁.kempeSwap κ η u) q x y u T
        (T₁.image (Equiv.swap κ η)) F 2 := by
  obtain ⟨w,θ,δ,c₁,T₁,hs⟩:=exists_A_candidate_preparation hG hcm q T F hT
    hηA hηu hηT hηF hF hlarge
  have hmissing : missing c₁ x=missing c x := by
    ext γ
    simp only [mem_missing,IsFree,hs.full.leftRow]
  have hbudget₁ : F.card+T₁.card<(missing c₁ x).card := by
    rw [hs.card,hmissing]
    exact hbudget
  obtain ⟨κ,hκ,hκF,hκT⟩:=exists_root_auxiliary c₁ x F T₁ hbudget₁
  have hg:=gain_of_two_missing hG hs.full.cm hux huy q T₁ F hs.selected
    hκ hs.full.etaMissing hs.candidateMissing hs.candidate hκT hκF hηF
  have hηx : η∈presentColours c x := ((mem_paletteA c q x y η).mp hηA).1
  have hθx : θ∈presentColours c x := (mem_presentColours c x θ).mpr
    (fun h => (hcm.ab_facts hG).1 θ h hs.thetaMissing)
  refine ⟨w,θ,δ,c₁,T₁,κ,hs,hκ,hκF,hκT,⟨hg.cm,?_,?_,?_,hg.selected,?_,?_,?_⟩⟩
  · intro v
    exact (hg.rootRow v).trans (hs.full.leftRow v)
  · intro a b γ hγ
    exact (hg.protectedColours a b γ hγ).trans (hs.protectedColours a b γ hγ)
  · intro γ hγ
    exact (hg.protectedMembership γ hγ).trans (hs.protectedMembership γ hγ)
  · exact hg.card.trans hs.card
  · have hh:=hg.gain
    have hm:=hs.score
    omega
  · intro v
    have hfirst:=CaoChenSwitchingOverlap.root_overlap_drop_le_one hs.protectedSwitch hηx hθx v
    have hsecond:=hg.rootDrop v
    omega

end OverfullWork.CaoChenFinitePaletteProgress
