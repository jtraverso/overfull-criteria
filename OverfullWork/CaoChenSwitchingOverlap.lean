module

public import OverfullWork.CaoChenFullPaletteSwitching
public import OverfullWork.CaoChenPaletteOverlapNormalization

@[expose] public section


/-! # Root-overlap control under one full palette switching

The union of the two endpoint missing palettes changes in a full switching;
it is therefore not used as an invariant here. The root palette is fixed.
Only its auxiliary colour delta can change missing status elsewhere, giving
an actual loss bound of one and a controlled eta-to-theta change of A-roles.
-/
namespace OverfullWork.CaoChenSwitchingOverlap
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenOverlapNormalization CaoChenPaletteOverlapNormalization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

noncomputable def rootSmallOverlapColours (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y : V) (C : Finset (Fin G.maxDegree)) (M : ℕ) : Finset (Fin G.maxDegree) :=
  (C∩paletteA c q x y).filter fun γ => ∃v,c.col y v=some γ ∧
    (missing c v∩missing c x).card≤M

private theorem root_missing_fixed
    {c c' : PEC G (Fin G.maxDegree)} {x y w : V} {η θ δ : Fin G.maxDegree}
    (hsw : ProtectedPaletteSwitching c c' x y w η θ δ) : missing c' x=missing c x := by
  ext γ
  simp only [mem_missing,IsFree,hsw.leftRow]

private theorem root_overlap_subset_insert_aux
    {c c' : PEC G (Fin G.maxDegree)} {x y w : V} {η θ δ : Fin G.maxDegree}
    (hsw : ProtectedPaletteSwitching c c' x y w η θ δ)
    (hηx : η∈presentColours c x) (hθx : θ∈presentColours c x) (v : V) :
    missing c v∩missing c x⊆insert δ (missing c' v∩missing c' x) := by
  intro γ hγ
  obtain ⟨hγv,hγx⟩:=mem_inter.mp hγ
  by_cases hγδ : γ=δ
  · simp [hγδ]
  apply mem_insert_of_mem
  have hγη : γ≠η := by
    intro he
    subst γ
    exact (mem_presentColours c x η).mp hηx (mem_missing.mp hγx)
  have hγθ : γ≠θ := by
    intro he
    subst γ
    exact (mem_presentColours c x θ).mp hθx (mem_missing.mp hγx)
  refine mem_inter.mpr ⟨mem_missing.mpr ?_,?_⟩
  · intro a ha
    exact mem_missing.mp hγv a ((hsw.otherEdges γ hγη hγθ hγδ v a).mp ha)
  · rwa [root_missing_fixed hsw]

/-- Every vertex loses at most one root-missing colour in a full switching. -/
theorem root_overlap_drop_le_one
    {c c' : PEC G (Fin G.maxDegree)} {x y w : V} {η θ δ : Fin G.maxDegree}
    (hsw : ProtectedPaletteSwitching c c' x y w η θ δ)
    (hηx : η∈presentColours c x) (hθx : θ∈presentColours c x) (v : V) :
    (missing c v∩missing c x).card≤(missing c' v∩missing c' x).card+1 := by
  exact (card_le_card (root_overlap_subset_insert_aux hsw hηx hθx v)).trans (card_insert_le _ _)

/-- If delta is not among a vertex's old root overlaps, none of those
overlaps is lost. This is stronger than merely bounding the cardinal loss. -/
theorem root_overlap_mono_of_aux_not_missing
    {c c' : PEC G (Fin G.maxDegree)} {x y w : V} {η θ δ : Fin G.maxDegree}
    (hsw : ProtectedPaletteSwitching c c' x y w η θ δ)
    (hηx : η∈presentColours c x) (hθx : θ∈presentColours c x) (v : V)
    (hδ : δ∉missing c v∩missing c x) :
    missing c v∩missing c x⊆missing c' v∩missing c' x := by
  intro γ hγ
  have hh:=root_overlap_subset_insert_aux hsw hηx hθx v hγ
  exact (mem_insert.mp hh).resolve_left (fun he => hδ (he ▸ hγ))

/-- Protecting the boundary root overlaps prevents any new small profile
in a fixed vertex family. This assertion is about the root palette only. -/
theorem root_low_filter_subset_of_protected_boundary
    {c c' : PEC G (Fin G.maxDegree)} {x y w : V} {η θ δ : Fin G.maxDegree}
    (hsw : ProtectedPaletteSwitching c c' x y w η θ δ)
    (hηx : η∈presentColours c x) (hθx : θ∈presentColours c x)
    (T : Finset V) (M : ℕ) (hδ : δ∉boundaryPalette c (missing c x) T M) :
    lowOverlapVertices c' (missing c' x) T M⊆lowOverlapVertices c (missing c x) T M := by
  intro v hv
  obtain ⟨hvT,hvM⟩:=mem_filter.mp hv
  apply mem_filter.mpr
  refine ⟨hvT,?_⟩
  have hdrop:=root_overlap_drop_le_one hsw hηx hθx v
  by_contra hn
  have hbound : (missing c v∩missing c x).card=M+1:=by omega
  have hnot : δ∉missing c v∩missing c x := by
    intro he
    exact hδ (mem_biUnion.mpr ⟨v,mem_filter.mpr ⟨hvT,by omega,by omega⟩,he⟩)
  have hc:=card_le_card (root_overlap_mono_of_aux_not_missing hsw hηx hθx v hnot)
  omega

/-- A small profile after the switch comes from an old profile with one
extra unit of budget. The new theta-role is precisely the old eta-role.
No invariance of the endpoint-union missing palette is assumed. -/
theorem root_small_overlap_transport (hG : IsClassTwo G)
    {c c' : PEC G (Fin G.maxDegree)} {x y w : V}
    (hcm : IsColMinus c x y) (q : ℝ) (η θ δ : Fin G.maxDegree)
    (hηA : η∈paletteA c q x y) (hyw : c.col y w=some η)
    (hθy : c.IsFree y θ) (hδx : c.IsFree x δ)
    (hfull : SwitchingResult c c' q x y w η θ)
    (hsw : ProtectedPaletteSwitching c c' x y w η θ δ)
    (C : Finset (Fin G.maxDegree)) (hηC : η∈C) (M : ℕ) :
    rootSmallOverlapColours c' q x y C M⊆
      (rootSmallOverlapColours c q x y C (M+1)).image (Equiv.swap η θ) := by
  have hηx : η∈presentColours c x:=(mem_paletteA c q x y η).mp hηA |>.1
  have hθx : θ∈presentColours c x:=
    (mem_presentColours c x θ).mpr (fun hh => (hcm.ab_facts hG).1 θ hh hθy)
  intro γ hγ
  obtain ⟨hγCA,v,hyv,hvM⟩:=mem_filter.mp hγ
  obtain ⟨hγC,hγA⟩:=mem_inter.mp hγCA
  have hdrop:=root_overlap_drop_le_one hsw hηx hθx v
  by_cases hγθ : γ=θ
  · subst γ
    have hvw : v=w:=c'.col_proper hyv hfull.newColour
    subst v
    have hηold : η∈rootSmallOverlapColours c q x y C (M+1):=
      mem_filter.mpr ⟨mem_inter.mpr ⟨hηC,hηA⟩,w,hyw,by omega⟩
    exact mem_image.mpr ⟨η,hηold,Equiv.swap_apply_left η θ⟩
  have hγη : γ≠η := by intro he;subst γ;exact hsw.etaMissing v hyv
  have hγδ : γ≠δ := by
    intro he
    subst γ
    have hn : c'.IsFree x δ := by intro a ha;exact hδx a ((hsw.leftRow a) ▸ ha)
    exact (mem_presentColours c' x δ).mp ((mem_paletteA c' q x y δ).mp hγA).1 hn
  have hyv₀ : c.col y v=some γ := (hsw.otherEdges γ hγη hγθ hγδ y v).mp hyv
  have hγx : γ∈presentColours c x := by
    apply (mem_presentColours c x γ).mpr
    intro hn
    have hn' : c'.IsFree x γ := by intro a ha;exact hn a ((hsw.leftRow a) ▸ ha)
    exact (mem_presentColours c' x γ).mp ((mem_paletteA c' q x y γ).mp hγA).1 hn'
  obtain ⟨_,v',hyv',hvlow⟩:=(mem_paletteA c' q x y γ).mp hγA
  have hvv : v=v':=c'.col_proper hyv hyv'
  have hγA₀ : γ∈paletteA c q x y:=
    (mem_paletteA c q x y γ).mpr ⟨hγx,v,hyv₀,by rw [hvv];exact hvlow⟩
  have hγold : γ∈rootSmallOverlapColours c q x y C (M+1):=
    mem_filter.mpr ⟨mem_inter.mpr ⟨hγC,hγA₀⟩,v,hyv₀,by omega⟩
  exact mem_image.mpr ⟨γ,hγold,Equiv.swap_apply_of_ne_of_ne hγη hγθ⟩

/-- Every selected A-role after the switch is an old selected A-role,
with eta replaced by theta. This tracks roles without endpoint choices. -/
theorem paletteA_roles_subset_swap_image (hG : IsClassTwo G)
    {c c' : PEC G (Fin G.maxDegree)} {x y w : V}
    (hcm : IsColMinus c x y) (q : ℝ) (η θ δ : Fin G.maxDegree)
    (hηA : η∈paletteA c q x y) (hyw : c.col y w=some η)
    (hθy : c.IsFree y θ) (hδx : c.IsFree x δ)
    (hfull : SwitchingResult c c' q x y w η θ)
    (hsw : ProtectedPaletteSwitching c c' x y w η θ δ)
    (C : Finset (Fin G.maxDegree)) (hηC : η∈C) :
    C∩paletteA c' q x y⊆(C∩paletteA c q x y).image (Equiv.swap η θ) := by
  intro γ hγ
  obtain ⟨_,v,hyv,_⟩:=(mem_paletteA c' q x y γ).mp (mem_inter.mp hγ).2
  have hc : (missing c' v∩missing c' x).card≤G.maxDegree :=
    (card_le_card inter_subset_left).trans (by simpa using card_le_univ (missing c' v))
  have hsmall : γ∈rootSmallOverlapColours c' q x y C G.maxDegree:=
    mem_filter.mpr ⟨hγ,v,hyv,hc⟩
  obtain ⟨τ,hτ,hτγ⟩:=mem_image.mp (root_small_overlap_transport hG hcm q η θ δ
    hηA hyw hθy hδx hfull hsw C hηC G.maxDegree hsmall)
  exact mem_image.mpr ⟨τ,(mem_filter.mp hτ).1,hτγ⟩

/-- A correct root-only B3 statement. Delta avoids the boundary palette
and the switched leaf is above M+1. No existence of such a delta is claimed. -/
theorem root_small_overlap_subset_of_protected_boundary (hG : IsClassTwo G)
    {c c' : PEC G (Fin G.maxDegree)} {x y w : V}
    (hcm : IsColMinus c x y) (q : ℝ) (η θ δ : Fin G.maxDegree)
    (hηA : η∈paletteA c q x y) (hyw : c.col y w=some η)
    (hθy : c.IsFree y θ) (hδx : c.IsFree x δ)
    (hfull : SwitchingResult c c' q x y w η θ)
    (hsw : ProtectedPaletteSwitching c c' x y w η θ δ)
    (C : Finset (Fin G.maxDegree)) (hηC : η∈C) (M : ℕ)
    (hboundary : δ∉boundaryPalette c (missing c x) (paletteLeaves c q x y C) M)
    (htarget : M+1<(missing c w∩missing c x).card) :
    rootSmallOverlapColours c' q x y C M⊆rootSmallOverlapColours c q x y C M := by
  have hηx : η∈presentColours c x:=(mem_paletteA c q x y η).mp hηA |>.1
  have hθx : θ∈presentColours c x:=
    (mem_presentColours c x θ).mpr (fun hh => (hcm.ab_facts hG).1 θ hh hθy)
  have hfilter:=root_low_filter_subset_of_protected_boundary hsw hηx hθx
    (paletteLeaves c q x y C) M hboundary
  intro γ hγ
  obtain ⟨τ,hτ,hτγ⟩:=mem_image.mp (root_small_overlap_transport hG hcm q η θ δ
    hηA hyw hθy hδx hfull hsw C hηC M hγ)
  obtain ⟨hτCA,v,hyv,hvold⟩:=mem_filter.mp hτ
  by_cases hτη : τ=η
  · subst τ
    have hvw : v=w:=c.col_proper hyv hyw
    subst v
    omega
  have hτθ : τ≠θ := by intro he;subst τ;exact hθy v hyv
  have hτδ : τ≠δ := by
    intro he
    subst τ
    exact (mem_presentColours c x δ).mp ((mem_paletteA c q x y δ).mp (mem_inter.mp hτCA).2).1 hδx
  have hτγ' : τ=γ := by
    simpa only [Equiv.swap_apply_of_ne_of_ne hτη hτθ] using hτγ
  rw [←hτγ'] at hγ ⊢
  have hyv' : c'.col y v=some τ:=(hsw.otherEdges τ hτη hτθ hτδ y v).mpr hyv
  obtain ⟨_,v',hyv'',hvnew⟩:=mem_filter.mp hγ
  have hvv : v=v':=c'.col_proper hyv' hyv''
  have hvT : v∈paletteLeaves c q x y C:=mem_filter.mpr ⟨mem_univ v,τ,hτCA,hyv⟩
  have hvlow : v∈lowOverlapVertices c' (missing c' x) (paletteLeaves c q x y C) M :=
    mem_filter.mpr ⟨hvT,by rw [hvv];exact hvnew⟩
  exact mem_filter.mpr ⟨hτCA,v,hyv,(mem_filter.mp (hfilter hvlow)).2⟩

end OverfullWork.CaoChenSwitchingOverlap
