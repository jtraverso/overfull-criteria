module

public import OverfullWork.CaoChenRootPaletteNormalization
public import OverfullWork.CaoChenUniformPaletteBudgets
public import OverfullWork.CaoChenFullPaletteSwitching

@[expose] public section


/-! # Constructing the missing-right colour needed in Cao--Chen Lemma 8

A family of k+2 actual S-spines shares 3k+1 bad colours. Root-only
normalization, followed by one actual full switching, makes one selected
colour missing at y while retaining at least 3k common bad colours at all
selected spines. Neither a high-profile leaf nor a prepared colouring is
assumed as an input.
-/
namespace OverfullWork.CaoChenLemma8Preparation
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenRootPaletteNormalization CaoChenSecondarySpineNormalization
open CaoChenUniformPaletteBudgets
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- All data refer to the same actual output colouring. U is certified by
its actual root edges, so properness fixes every selected spine endpoint. -/
structure Prepared (c₀ c : PEC G (Fin G.maxDegree)) (q : ℝ) (x y : V)
    (S : Finset (Fin G.maxDegree)) (U : Fin G.maxDegree → V)
    (F F' : Finset (Fin G.maxDegree)) (η : Fin G.maxDegree) (k : ℕ) : Prop where
  cm : IsColMinus c x y
  rootRow : ∀v,c.col x v=c₀.col x v
  spines : ∀ξ∈S,c.col x (U ξ)=some ξ
  roles : S⊆paletteS c q x y∩presentColours c x
  candidate : η∈S
  candidateMissing : c.IsFree y η
  commonSubset : F'⊆F
  commonCard : 3*k≤F'.card
  commonBad : ∀ξ∈S,F'⊆badColours c q (U ξ)\{ξ}
  disjoint : Disjoint S F'

private theorem bad_iff_of_colour_classes
    {c c' : PEC G (Fin G.maxDegree)} (q : ℝ) (γ : Fin G.maxDegree)
    (hclasses : ∀a b,c'.col a b=some γ↔c.col a b=some γ) (u : V) :
    γ∈badColours c' q u↔γ∈badColours c q u := by
  simp only [mem_badColours,IsFree,ne_eq]
  simp_rw [hclasses]

/-- Actual normalization and switching prepare Lemma 8 for re-rooting.
The same uniform degree cutoff as Lemma 7 pays every finite palette budget. -/
theorem exists_missing_right_preparation (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y : V} (hcm₀ : IsColMinus c₀ x y)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (S : Finset (Fin G.maxDegree)) (U : Fin G.maxDegree → V)
    (F : Finset (Fin G.maxDegree)) (hScard : S.card=k+2)
    (hU : ∀ξ∈S,c₀.col x (U ξ)=some ξ)
    (hS : S⊆paletteS c₀ ((1-ε)*(G.maxDegree:ℝ)) x y∩presentColours c₀ x)
    (hFcard : F.card=3*k+1)
    (hCommon : ∀ξ∈S,F⊆badColours c₀ ((1-ε)*(G.maxDegree:ℝ)) (U ξ)\{ξ}) :
    ∃c : PEC G (Fin G.maxDegree),∃η F',
      Prepared c₀ c ((1-ε)*(G.maxDegree:ℝ)) x y S U F F' η k := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  have hdis : Disjoint S F := by
    apply Finset.disjoint_left.mpr
    intro ξ hξS hξF
    exact (mem_sdiff.mp (hCommon ξ hξS hξF)).2 (mem_singleton_self ξ)
  by_cases hmiss : ∃η∈S,c₀.IsFree y η
  · obtain ⟨η,hηS,hηy⟩:=hmiss
    exact ⟨c₀,η,F,⟨hcm₀,fun _ => rfl,hU,hS,hηS,hηy,subset_rfl,
      by omega,hCommon,hdis⟩⟩
  have hAllA : ∀ξ∈S,ξ∈paletteA c₀ q x y := by
    intro ξ hξ
    have hξS:=(mem_inter.mp (hS hξ)).1
    have hξx:=(mem_inter.mp (hS hξ)).2
    have hcases : ξ∈paletteA c₀ q x y ∨ c₀.IsFree x ξ ∨ c₀.IsFree y ξ := by
      simpa only [paletteS,mem_union,mem_missing,or_assoc] using hξS
    exact hcases.resolve_right (fun h => h.elim
      ((mem_presentColours c₀ x ξ).mp hξx) (fun hy => hmiss ⟨ξ,hξ,hy⟩))
  have hthN : 3*k+1+(S.card-1)*(F.card+((3*k+1)+3)*S.card+1)≤cutoff k := by
    rw [hScard,hFcard]
    convert (lemma8_budgets k).1 using 1
  have hbudN : F.card+((3*k+1)+3)*S.card+S.card*(3*k+1)≤cutoff k := by
    rw [hScard,hFcard]
    convert (lemma8_budgets k).2 using 1
  have hth : ((3*k+1:ℕ):ℝ)+((S.card-1:ℕ):ℝ)*
      ((F.card+((3*k+1)+3)*S.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) := by
    exact (by exact_mod_cast hthN : _≤(cutoff k:ℝ)).trans hlarge
  have hroot:=missing_root_gt_cutoff hcm₀ ε hε hεone k hx hlarge
  have hbud : F.card+((3*k+1)+3)*S.card+S.card*(3*k+1)<(missing c₀ x).card :=
    hbudN.trans_lt hroot
  obtain ⟨c₁,hnorm,hIcard⟩:=exists_root_normalized_palette_card_le hG c₀ hcm₀ q S F (3*k+1) k
    ε hε hεone rfl hx hscale hth hbud
  let I:=smallRootOverlapColours c₁ q x y S (3*k+1)
  have hIS : I.card<S.card := by change I.card≤k at hIcard;omega
  obtain ⟨η,hηS,hηI⟩:=exists_mem_notMem_of_card_lt_card hIS
  have hηA : η∈paletteA c₁ q x y := (hnorm.Aroles η hηS).mpr (hAllA η hηS)
  obtain ⟨_,w,hyw,_⟩:=(mem_paletteA c₁ q x y η).mp hηA
  have hwlarge : F.card<(missing c₁ w∩missing c₁ x).card := by
    rw [hFcard]
    by_contra hn
    exact hηI (mem_filter.mpr ⟨mem_inter.mpr ⟨hηS,hηA⟩,w,hyw,by omega⟩)
  obtain ⟨δ,hδ,hδF⟩:=exists_mem_notMem_of_card_lt_card hwlarge
  obtain ⟨hδw,hδx⟩:=mem_inter.mp hδ
  obtain ⟨θ,hθy⟩:=hnorm.cm.exists_free_right
  obtain ⟨c₂,hfull,hsw⟩:=exists_full_palette_switching hG hnorm.cm q η θ δ hηA hyw hθy
    (mem_missing.mp hδx) (mem_missing.mp hδw)
  let F':=F.erase θ
  have hηF : η∉F := fun hh => (Finset.disjoint_left.mp hdis) hηS hh
  have hclasses : ∀γ∈F',∀a b,c₂.col a b=some γ↔c₀.col a b=some γ := by
    intro γ hγ a b
    obtain ⟨hγθ,hγF⟩:=mem_erase.mp hγ
    have hγη : γ≠η:=fun he => hηF (he ▸ hγF)
    have hγδ : γ≠δ:=fun he => hδF (he ▸ hγF)
    exact (hsw.otherEdges γ hγη hγθ hγδ a b).trans
      (hnorm.protectedColours a b γ (mem_union_right S hγF))
  have hrow : ∀v,c₂.col x v=c₀.col x v:=
    fun v => (hfull.leftRow v).trans (hnorm.rootRow v)
  have hU₂ : ∀ξ∈S,c₂.col x (U ξ)=some ξ:=fun ξ hξ => by rw [hrow];exact hU ξ hξ
  have hS₂ : S⊆paletteS c₂ q x y∩presentColours c₂ x := by
    intro ξ hξ
    have hξA : ξ∈paletteA c₁ q x y := (hnorm.Aroles ξ hξ).mpr (hAllA ξ hξ)
    refine mem_inter.mpr ⟨?_,(presentColours_iff_coloured c₂ x ξ).mpr ⟨U ξ,hU₂ ξ hξ⟩⟩
    rw [hfull.palette_eq]
    exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl hξA)))
  have hcommon : ∀ξ∈S,F'⊆badColours c₂ q (U ξ)\{ξ} := by
    intro ξ hξ γ hγ
    have hγF : γ∈F:=(mem_erase.mp hγ).2
    obtain ⟨hbad,hne⟩:=mem_sdiff.mp (hCommon ξ hξ hγF)
    exact mem_sdiff.mpr ⟨(bad_iff_of_colour_classes q γ (hclasses γ hγ) (U ξ)).mpr hbad,hne⟩
  have hFsub : F'⊆F:=erase_subset _ _
  have hFcard' : 3*k≤F'.card := by
    have hc:=pred_card_le_card_erase (s:=F) (a:=θ)
    dsimp [F']
    omega
  exact ⟨c₂,η,F',⟨hfull.cm,hrow,hU₂,hS₂,hηS,hfull.etaMissing,hFsub,hFcard',hcommon,
    hdis.mono_right hFsub⟩⟩

end OverfullWork.CaoChenLemma8Preparation
