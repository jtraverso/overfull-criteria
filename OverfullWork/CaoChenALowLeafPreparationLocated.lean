module

public import OverfullWork.CaoChenALowLeafProgress

@[expose] public section


/-! # The same low-leaf preparation with its selected-palette location

This reconstructs the actual located switching of the earlier preparation,
retaining the conditional image formula needed by the finite role invariant.
The two outputs concern the same constructed colouring and selected palette.
-/
namespace OverfullWork.CaoChenALowLeafPreparationLocated
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenFinitePaletteProgress CaoChenSwitchSpineTransport
open CaoChenLowLeafProgress CaoChenALowLeafProgress
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- An actual located preparation protects the common leaf colour.
The large overlap is measured at the actual y-leaf of the A-colour. -/
theorem exists_A_low_leaf_preparation_located (hG : IsClassTwo G)
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
      Preparation c c₁ q x y u t w η θ δnorm δleaf T T₁ F ∧
      T₁=(if (c.kempeGraph δnorm θ).Reachable w u then T.image (Equiv.swap δnorm θ) else T) := by
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
  obtain ⟨T₁,hformula,hselected,hcard,hmem,hscore,hηT₁,_hηfree,hηedge⟩:=
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
    hclasses,hscore,hηT₁,(hηedge t).mpr hut,hδleafx₁,hδleaft₁,hδleafT₁,?_⟩,hformula⟩
  exact CaoChenSwitchingOverlap.root_overlap_drop_le_one hsw
    ((mem_paletteA c q x y η).mp hηA).1 hθx


end OverfullWork.CaoChenALowLeafPreparationLocated
