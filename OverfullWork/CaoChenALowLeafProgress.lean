module

public import OverfullWork.CaoChenFinitePaletteProgress
public import OverfullWork.CaoChenLowLeafProgress
public import OverfullWork.CaoChenSwitchSpineTransport

@[expose] public section


/-! # The A-colour low-leaf branch of finite palette progress

A located full switching first makes the candidate colour missing at y.
The selected palette is transported at its actual spine row, while an
already chosen common root/leaf colour is protected. A subsequent explicit
low-leaf Kempe gain gives total root-overlap loss at most two.
-/
namespace OverfullWork.CaoChenALowLeafProgress
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenFinitePaletteProgress CaoChenSwitchSpineTransport
open CaoChenLowLeafProgress
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- Metadata for the same actual intermediate colouring and selected palette. -/
structure Preparation (c c₁ : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y u t w : V) (η θ δnorm δleaf : Fin G.maxDegree)
    (T T₁ F : Finset (Fin G.maxDegree)) : Prop where
  full : SwitchingResult c c₁ q x y w η θ
  protectedSwitch : ProtectedPaletteSwitching c c₁ x y w η θ δnorm
  locatedRow : ∀v,c₁.col u v=(c.kempeSwap δnorm θ w).col u v
  normMissingRoot : c.IsFree x δnorm
  normMissingLeaf : c.IsFree w δnorm
  thetaMissing : c.IsFree y θ
  selected : T₁⊆badColours c₁ q u∩paletteS c₁ q x y
  card : T₁.card=T.card
  protectedMembership : ∀γ∈insert δleaf F,γ∈T₁↔γ∈T
  protectedColours : ∀a b γ,γ∈insert δleaf F → (c₁.col a b=some γ↔c.col a b=some γ)
  score : (T∩missing c x).card≤(T₁∩missing c₁ x).card
  candidate : η∈T₁
  candidateEdge : c₁.col u t=some η
  leafMissingRoot : c₁.IsFree x δleaf
  leafMissingLeaf : c₁.IsFree t δleaf
  leafNotSelected : δleaf∉T₁
  rootDrop : ∀v,(missing c v∩missing c x).card≤(missing c₁ v∩missing c₁ x).card+1

/-- An actual located preparation protects the common leaf colour.
The large overlap is measured at the actual y-leaf of the A-colour. -/
theorem exists_A_low_leaf_preparation (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u t w : V} {η δleaf : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (huy : u≠y)
    (q : ℝ) (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u∩paletteS c q x y)
    (hηA : η∈paletteA c q x y) (hηT : η∈T) (hηF : η∉F)
    (hFpresent : ∀γ∈F,γ∈presentColours c y)
    (hut : c.col u t=some η) (hyw : c.col y w=some η)
    (hδleafx : c.IsFree x δleaf) (hδleaft : c.IsFree t δleaf)
    (_hδleafF : δleaf∉F) (hδleafT : δleaf∉T)
    (hlarge : (insert δleaf F).card+(T∩missing c x).card<(missing c w∩missing c x).card) :
    ∃θ δnorm : Fin G.maxDegree,∃c₁ : PEC G (Fin G.maxDegree),∃T₁ : Finset (Fin G.maxDegree),
      Preparation c c₁ q x y u t w η θ δnorm δleaf T T₁ F := by
  let Ftemp:=insert δleaf F
  have hηx : ¬c.IsFree x η:=
    (mem_presentColours c x η).mp ((mem_paletteA c q x y η).mp hηA).1
  have hηδleaf : η≠δleaf:=fun he => hηx (he.symm ▸ hδleafx)
  have hηTemp : η∉Ftemp := by
    intro h
    rcases mem_insert.mp h with he|hF
    · exact hηδleaf he
    · exact hηF hF
  have hFtemp : ∀γ∈Ftemp,γ∈presentColours c y := by
    intro γ hγ
    rcases mem_insert.mp hγ with he|hγF
    · subst γ
      exact (mem_presentColours c y δleaf).mpr ((hcm.ab_facts hG).1 δleaf hδleafx)
    · exact hFpresent γ hγF
  obtain ⟨δnorm,hδnx,hδnw,hδnTemp,hδnT⟩:=exists_common_root_auxiliary c x w Ftemp T hlarge
  obtain ⟨θ,hθy⟩:=hcm.exists_free_right
  have hθTemp : θ∉Ftemp:=fun h => (mem_presentColours c y θ).mp (hFtemp θ h) hθy
  have huw : u≠w := by
    intro he
    subst w
    have huycol : c.col u y=some η:=by rw [c.col_symm];exact hyw
    have heyt : y=t:=c.col_proper huycol hut
    subst t
    exact (hcm.ab_facts hG).1 δleaf hδleafx hδleaft
  obtain ⟨c₁,hfull,hsw,_hlocated,hrow⟩:=exists_located_full_palette_switching hG hcm q
    η θ δnorm hηA hyw hθy hδnx hδnw
  have hrowu:=hrow u huy huw
  obtain ⟨T₁,_hformula,hselected,hcard,hmem,hscore,hηT₁,_hηfree,hηedge⟩:=
    exists_selected_transport_general hG hcm q hηA hδnx hθy hfull hrowu
      T Ftemp hT hηT hδnT hδnTemp hθTemp
  have hclasses : ∀a b γ,γ∈Ftemp → (c₁.col a b=some γ↔c.col a b=some γ) := by
    intro a b γ hγ
    have hγη : γ≠η:=fun he => hηTemp (he ▸ hγ)
    have hγθ : γ≠θ:=fun he => hθTemp (he ▸ hγ)
    have hγδ : γ≠δnorm:=fun he => hδnTemp (he ▸ hγ)
    exact hsw.otherEdges γ hγη hγθ hγδ a b
  have hδleafTemp : δleaf∈Ftemp:=mem_insert_self _ _
  have hδleafx₁ : c₁.IsFree x δleaf := by
    intro a ha
    exact hδleafx a (by rw [←hfull.leftRow a];exact ha)
  have hδleaft₁ : c₁.IsFree t δleaf := by
    intro a ha
    exact hδleaft a ((hclasses t a δleaf hδleafTemp).mp ha)
  have hδleafT₁ : δleaf∉T₁:=fun h => hδleafT ((hmem δleaf hδleafTemp).mp h)
  have hθx : θ∈presentColours c x:=
    (mem_presentColours c x θ).mpr (fun h => (hcm.ab_facts hG).1 θ h hθy)
  refine ⟨θ,δnorm,c₁,T₁,⟨hfull,hsw,hrowu,hδnx,hδnw,hθy,hselected,hcard,hmem,
    hclasses,hscore,hηT₁,(hηedge t).mpr hut,hδleafx₁,hδleaft₁,hδleafT₁,?_⟩⟩
  exact CaoChenSwitchingOverlap.root_overlap_drop_le_one hsw
    ((mem_paletteA c q x y η).mp hηA).1 hθx

/-- All local Case-2 A-branches now yield an actual two-stage progress
step. Both intermediate metadata and the final literal Kempe swap are exported. -/
theorem exists_A_low_leaf_progress (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u t w : V} {η δleaf : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (huy : u≠y) (htx : t≠x)
    (q : ℝ) (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u∩paletteS c q x y)
    (hηA : η∈paletteA c q x y) (hηT : η∈T) (hηF : η∉F)
    (hFpresent : ∀γ∈F,γ∈presentColours c y)
    (hut : c.col u t=some η) (hyw : c.col y w=some η)
    (hδleafx : c.IsFree x δleaf) (hδleaft : c.IsFree t δleaf)
    (hδleafF : δleaf∉F) (hδleafT : δleaf∉T)
    (hlarge : (insert δleaf F).card+(T∩missing c x).card<(missing c w∩missing c x).card) :
    ∃θ δnorm : Fin G.maxDegree,∃c₁ : PEC G (Fin G.maxDegree),∃T₁ : Finset (Fin G.maxDegree),
      Preparation c c₁ q x y u t w η θ δnorm δleaf T T₁ F ∧
      Progress c (c₁.kempeSwap δleaf η u) q x y u T (T₁.image (Equiv.swap δleaf η)) F 2 := by
  obtain ⟨θ,δnorm,c₁,T₁,hprep⟩:=exists_A_low_leaf_preparation hG hcm huy q T F hT
    hηA hηT hηF hFpresent hut hyw hδleafx hδleaft hδleafF hδleafT hlarge
  have hgain:=gain_of_low_leaf_common_root hG hprep.full.cm htx q T₁ F hprep.selected
    hprep.leafMissingRoot hprep.full.etaMissing hprep.candidateEdge hprep.leafMissingLeaf
    hprep.candidate hprep.leafNotSelected hδleafF hηF
  refine ⟨θ,δnorm,c₁,T₁,hprep,⟨hgain.cm,?_,?_,?_,hgain.selected,?_,?_,?_⟩⟩
  · intro a
    exact (hgain.rootRow a).trans (hprep.full.leftRow a)
  · intro a b γ hγ
    exact (hgain.protectedColours a b γ hγ).trans
      (hprep.protectedColours a b γ (mem_insert_of_mem hγ))
  · intro γ hγ
    exact (hgain.protectedMembership γ hγ).trans
      (hprep.protectedMembership γ (mem_insert_of_mem hγ))
  · exact hgain.card.trans hprep.card
  · have h0:=hprep.score
    have h1:=hgain.gain
    omega
  · intro v
    have h0:=hprep.rootDrop v
    have h1:=hgain.rootDrop v
    omega

end OverfullWork.CaoChenALowLeafProgress
