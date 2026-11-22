module

public import OverfullWork.CaoChenSecondarySpineNormalization

@[expose] public section


/-! # Actual initial normalization against the root palette alone

The selected vertices are the actual A-leaves of the protected colours C.
Applying the root-only secondary normalizer with no primary family produces
an initial finite exceptional set, with every bound depending only on the
protected colour-family sizes and the prescribed overlap threshold.
-/
namespace OverfullWork.CaoChenRootPaletteNormalization
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenPaletteOverlapNormalization CaoChenOverlapNormalization
open CaoChenSecondaryNormalization CaoChenSecondarySpineNormalization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

omit [DecidableEq V] in
/-- The actual protected A-colours and their low leaves give the same
small-overlap count against the ROOT palette alone. -/
theorem smallRootOverlapColours_card_eq (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y : V) (C : Finset (Fin G.maxDegree)) (m : ℕ) :
    (smallRootOverlapColours c q x y C m).card=
      (lowOverlapVertices c (missing c x) (paletteLeaves c q x y C) m).card := by
  symm
  apply CaoChenPaletteCounting.card_leaves_eq_card_colours
  · intro v hv
    obtain ⟨hvT,hvsmall⟩:=mem_filter.mp hv
    obtain ⟨η,hη,hyv⟩:=(mem_filter.mp hvT).2
    exact ⟨η,mem_filter.mpr ⟨hη,v,hyv,hvsmall⟩,hyv⟩
  · intro η hη
    obtain ⟨hηCA,v,hyv,hvsmall⟩:=mem_filter.mp hη
    exact ⟨v,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ v,η,hηCA,hyv⟩,hvsmall⟩,hyv⟩

/-- A constructed initial state retaining all selected colour roles. -/
structure RootNormalized (c₀ c : PEC G (Fin G.maxDegree)) (q : ℝ) (x y : V)
    (C E : Finset (Fin G.maxDegree)) (m L : ℕ) : Prop where
  cm : IsColMinus c x y
  rootRow : ∀w,c.col x w=c₀.col x w
  otherMissing : ∀γ,c.IsFree y γ↔c₀.IsFree y γ
  protectedColours : ∀a b γ,γ∈C∪E → (c.col a b=some γ↔c₀.col a b=some γ)
  Aroles : ∀η∈C,η∈paletteA c q x y↔η∈paletteA c₀ q x y
  leaves : paletteLeaves c q x y C=paletteLeaves c₀ q x y C
  small : (smallRootOverlapColours c q x y C m).card<L

/-- The initial root-only normalization is built from actual colourings.
No normalized state, extremizer, or recolourability assumption is supplied. -/
theorem exists_root_normalized_palette (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y : V} (hcm₀ : IsColMinus c₀ x y)
    (q : ℝ) (C E : Finset (Fin G.maxDegree)) (m L : ℕ)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hq : q=(1-ε)*(G.maxDegree:ℝ)) (hx : (G.degree x:ℝ)<q)
    (hL : 1≤ε*(L:ℝ))
    (hthreshold : (m:ℝ)+((C.card-1:ℕ):ℝ)*
      ((E.card+(m+3)*C.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hbudget : E.card+(m+3)*C.card+C.card*m<(missing c₀ x).card) :
    ∃c : PEC G (Fin G.maxDegree),RootNormalized c₀ c q x y C E m L := by
  let T:=paletteLeaves c₀ q x y C
  let F:=C∪E
  have hTcard : T.card≤C.card := by
    rw [paletteLeaves_card_eq]
    exact card_le_card inter_subset_left
  have hTlow : ∀v∈T,(G.degree v:ℝ)<(1-ε)*(G.maxDegree:ℝ) := by
    intro v hv
    obtain ⟨η,hη,hyv⟩:=(mem_filter.mp hv).2
    obtain ⟨_,w,hyw,hwlow⟩:=(mem_paletteA c₀ q x y η).mp (mem_inter.mp hη).2
    have he : v=w:=c₀.col_proper hyv hyw
    subst w
    rwa [←hq]
  have hFbound : F.card+(m+2)*T.card≤E.card+(m+3)*C.card := by
    have hF:=card_union_le C E
    change F.card≤C.card+E.card at hF
    have hm:=Nat.mul_le_mul_left (m+2) hTcard
    nlinarith only [hF,hm]
  have hthreshold' : (m:ℝ)+((T.card-1:ℕ):ℝ)*
      ((F.card+(m+2)*T.card+(0+2)*(∅ : Finset V).card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) := by
    simp only [card_empty,mul_zero,add_zero]
    have hN : T.card-1≤C.card-1:=by omega
    have hNR : ((T.card-1:ℕ):ℝ)≤((C.card-1:ℕ):ℝ):=by exact_mod_cast hN
    have hFR : ((F.card+(m+2)*T.card+1:ℕ):ℝ)≤((E.card+(m+3)*C.card+1:ℕ):ℝ) := by
      exact_mod_cast (show F.card+(m+2)*T.card+1≤E.card+(m+3)*C.card+1 by omega)
    have hm:=mul_le_mul hNR hFR (by positivity) (by positivity)
    linarith only [hm,hthreshold]
  have hbudget' : F.card+(m+2)*T.card+(0+2)*(∅ : Finset V).card+T.card*m<(missing c₀ x).card := by
    simp only [card_empty,mul_zero,add_zero]
    have hm:=Nat.mul_le_mul_right m hTcard
    omega
  obtain ⟨c,hs,hsmall⟩:=exists_root_overlap_normalization_preserving_primary hG c₀ hcm₀
    T ∅ F ∅ m 0 L ε hε hεone (by rwa [←hq]) hTlow hL hthreshold' hbudget'
  have hAroles : ∀η∈C,η∈paletteA c q x y↔η∈paletteA c₀ q x y := by
    intro η hη
    exact A_role_iff hs q η (mem_union_left E hη)
  have hleaves : paletteLeaves c q x y C=paletteLeaves c₀ q x y C := by
    ext v
    simp only [paletteLeaves,mem_filter,mem_univ,true_and,mem_inter]
    constructor
    · rintro ⟨η,⟨hηC,hηA⟩,hyv⟩
      exact ⟨η,⟨hηC,(hAroles η hηC).mp hηA⟩,
        (hs.protectedColours y v η (mem_union_left E hηC)).mp hyv⟩
    · rintro ⟨η,⟨hηC,hηA⟩,hyv⟩
      exact ⟨η,⟨hηC,(hAroles η hηC).mpr hηA⟩,
        (hs.protectedColours y v η (mem_union_left E hηC)).mpr hyv⟩
  refine ⟨c,⟨hs.cm,hs.rootRow,hs.otherMissing,hs.protectedColours,hAroles,hleaves,?_⟩⟩
  rw [smallRootOverlapColours_card_eq,hleaves]
  exact hsmall

/-- Taking L=k+1 gives the fixed exceptional set bound needed by finite progress. -/
theorem exists_root_normalized_palette_card_le (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y : V} (hcm₀ : IsColMinus c₀ x y)
    (q : ℝ) (C E : Finset (Fin G.maxDegree)) (m k : ℕ)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hq : q=(1-ε)*(G.maxDegree:ℝ)) (hx : (G.degree x:ℝ)<q)
    (hk : 1≤ε*((k+1:ℕ):ℝ))
    (hthreshold : (m:ℝ)+((C.card-1:ℕ):ℝ)*
      ((E.card+(m+3)*C.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hbudget : E.card+(m+3)*C.card+C.card*m<(missing c₀ x).card) :
    ∃c : PEC G (Fin G.maxDegree),RootNormalized c₀ c q x y C E m (k+1) ∧
      (smallRootOverlapColours c q x y C m).card≤k := by
  obtain ⟨c,hc⟩:=exists_root_normalized_palette hG c₀ hcm₀ q C E m (k+1) ε hε hεone hq hx hk
    hthreshold hbudget
  exact ⟨c,hc,by have hh:=hc.small;omega⟩

end OverfullWork.CaoChenRootPaletteNormalization
