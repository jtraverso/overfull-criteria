module

public import OverfullWork.CaoChenFinitePaletteProgress

@[expose] public section


/-! # Large A-role profiles during actual finite palette progress

A full switching costs at most one unit of root overlap. Its new theta-role
inherits the old eta-leaf. A subsequent literal Kempe gain fixes both endpoint
rows and costs at most one further unit. These lemmas transport the selected
role invariant without postulating the final invariant or an off-component
recolouring oracle.
-/
namespace OverfullWork.CaoChenFiniteRoleInvariant
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

def LargeRoles (c : PEC G (Fin G.maxDegree)) (q : ℝ) (x y : V)
    (C I : Finset (Fin G.maxDegree)) (m : ℕ) : Prop :=
  ∀γ∈C,γ∉I → γ∈paletteA c q x y → ∀v,c.col y v=some γ →
    m<(missing c v∩missing c x).card

omit [DecidableEq V] in
private theorem mem_image_swap_of_ne (T : Finset (Fin G.maxDegree))
    (δ θ γ : Fin G.maxDegree) (hγδ : γ≠δ) (hγθ : γ≠θ) :
    γ∈T.image (Equiv.swap δ θ) ↔ γ∈T := by
  constructor
  · intro h
    obtain ⟨τ,hτ,he⟩:=mem_image.mp h
    have he' : τ=γ := (Equiv.swap δ θ).injective
      (he.trans (Equiv.swap_apply_of_ne_of_ne hγδ hγθ).symm)
    simpa only [he'] using hτ
  · intro h
    exact mem_image.mpr ⟨γ,h,Equiv.swap_apply_of_ne_of_ne hγδ hγθ⟩

/-- The new theta-role inherits the chosen eta-role; every other selected
A-role is unchanged. The margin loses at most one unit. -/
theorem largeRoles_after_full_switch (hG : IsClassTwo G)
    {c c' : PEC G (Fin G.maxDegree)} {x y w u : V}
    (hcm : IsColMinus c x y) (q : ℝ) (η θ δ : Fin G.maxDegree)
    (hηA : η∈paletteA c q x y) (hyw : c.col y w=some η)
    (hθy : c.IsFree y θ) (hδx : c.IsFree x δ)
    (hfull : SwitchingResult c c' q x y w η θ)
    (hsw : ProtectedPaletteSwitching c c' x y w η θ δ)
    (α : Fin G.maxDegree) (T T₁ I : Finset (Fin G.maxDegree)) (m m' : ℕ)
    (hηT : η∈T) (hηI : η∉I)
    (hT₁ : T₁=if (c.kempeGraph δ θ).Reachable w u then T.image (Equiv.swap δ θ) else T)
    (hlarge : LargeRoles c q x y (insert α T) I m) (hmargin : m'+1≤m) :
    LargeRoles c' q x y (insert α T₁) I m' := by
  have hηx : η∈presentColours c x:=((mem_paletteA c q x y η).mp hηA).1
  have hθx : θ∈presentColours c x:=(mem_presentColours c x θ).mpr
    (fun hf => (hcm.ab_facts hG).1 θ hf hθy)
  intro γ hγC hγI hγA v hyv
  have hdrop:=CaoChenSwitchingOverlap.root_overlap_drop_le_one hsw hηx hθx v
  by_cases hγθ : γ=θ
  · subst γ
    have hvw : v=w:=c'.col_proper hyv hfull.newColour
    have hh:=hlarge η (mem_insert_of_mem hηT) hηI hηA w hyw
    rw [hvw] at hdrop
    rw [hvw]
    omega
  have hγη : γ≠η:=by intro he;subst γ;exact hsw.etaMissing v hyv
  have hγδ : γ≠δ := by
    intro he
    subst γ
    have hf : c'.IsFree x δ := by intro a ha;exact hδx a ((hsw.leftRow a) ▸ ha)
    exact (mem_presentColours c' x δ).mp ((mem_paletteA c' q x y δ).mp hγA).1 hf
  have hγC₀ : γ∈insert α T := by
    rcases mem_insert.mp hγC with he|hγT
    · exact mem_insert.mpr (Or.inl he)
    · apply mem_insert_of_mem
      rw [hT₁] at hγT
      split_ifs at hγT
      · exact (mem_image_swap_of_ne T δ θ γ hγδ hγθ).mp hγT
      · exact hγT
  have hyv₀ : c.col y v=some γ := (hsw.otherEdges γ hγη hγθ hγδ y v).mp hyv
  have hγx : γ∈presentColours c x := by
    apply (mem_presentColours c x γ).mpr
    intro hf
    have hf' : c'.IsFree x γ := by intro a ha;exact hf a ((hsw.leftRow a) ▸ ha)
    exact (mem_presentColours c' x γ).mp ((mem_paletteA c' q x y γ).mp hγA).1 hf'
  obtain ⟨_,v',hyv',hv'⟩:=(mem_paletteA c' q x y γ).mp hγA
  have hvv : v=v':=c'.col_proper hyv hyv'
  have hγA₀ : γ∈paletteA c q x y:=
    (mem_paletteA c q x y γ).mpr ⟨hγx,v,hyv₀,by rw [hvv];exact hv'⟩
  have hh:=hlarge γ hγC₀ hγI hγA₀ v hyv₀
  omega

/-- Root-row preservation by the literal gain forces the Kempe component
to avoid both endpoints. Consequently the other row and both A and S are
fixed. No component-avoidance or palette-invariance hypothesis is supplied. -/
theorem kempe_gain_preserves_endpoint_palettes (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y : V}
    (hcm : IsColMinus c x y) (q : ℝ) (κ η : Fin G.maxDegree) (r : V)
    (hκx : c.IsFree x κ) (hηy : c.IsFree y η)
    (hrootRow : ∀v,(c.kempeSwap κ η r).col x v=c.col x v) :
    ¬(c.kempeGraph κ η).Reachable r x ∧
      (∀v,(c.kempeSwap κ η r).col y v=c.col y v) ∧
      paletteS (c.kempeSwap κ η r) q x y=paletteS c q x y ∧
      paletteA (c.kempeSwap κ η r) q x y=paletteA c q x y := by
  have hηx : ¬c.IsFree x η:=fun hf => (hcm.ab_facts hG).1 η hf hηy
  have hoff : ¬(c.kempeGraph κ η).Reachable r x := by
    intro hr
    have hf : (c.kempeSwap κ η r).IsFree x κ := by
      intro a ha
      exact hκx a ((hrootRow a) ▸ ha)
    have hh:=(isFree_kempeSwap_of_reachable c κ η hr κ).mp hf
    rw [Equiv.swap_apply_left] at hh
    exact hηx hh
  have hxy:=(hcm.ab_facts hG).2 κ η hκx hηy
  have hoffy : ¬(c.kempeGraph κ η).Reachable r y:=fun hr => hoff (hr.trans hxy.symm)
  have hyrow : ∀v,(c.kempeSwap κ η r).col y v=c.col y v:=
    fun v => kempeSwapFun_of_not_reachable c κ η hoffy v
  refine ⟨hoff,hyrow,CaoChenPaletteKempeTransport.paletteS_eq_of_endpoint_rows
    c (c.kempeSwap κ η r) q x y hrootRow hyrow,?_⟩
  ext γ
  simp only [mem_paletteA,mem_presentColours,IsFree]
  simp_rw [hrootRow,hyrow]

/-- A literal Kempe gain fixes all A-roles. Root-row preservation is
already provided by the actual gain constructions; it forces avoidance
of both root endpoints, rather than assuming that avoidance. -/
theorem largeRoles_after_kempe_gain (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y : V}
    (hcm : IsColMinus c x y) (q : ℝ) (κ η : Fin G.maxDegree) (r : V)
    (hκx : c.IsFree x κ) (hηy : c.IsFree y η)
    (hrootRow : ∀v,(c.kempeSwap κ η r).col x v=c.col x v)
    (α : Fin G.maxDegree) (T I : Finset (Fin G.maxDegree)) (m m' : ℕ)
    (hlarge : LargeRoles c q x y (insert α T) I m) (hmargin : m'+1≤m) :
    LargeRoles (c.kempeSwap κ η r) q x y (insert α (T.image (Equiv.swap κ η))) I m' := by
  let d:=c.kempeSwap κ η r
  have hηx : ¬c.IsFree x η:=fun hf => (hcm.ab_facts hG).1 η hf hηy
  obtain ⟨hoff,hyrow,_hS,hA⟩:=kempe_gain_preserves_endpoint_palettes hG hcm q κ η r hκx hηy hrootRow
  intro γ hγC hγI hγA v hyv
  have hγη : γ≠η := by intro he;subst γ;exact hηy v ((hyrow v) ▸ hyv)
  have hγκ : γ≠κ := by
    intro he
    subst γ
    have hf : d.IsFree x κ:=by intro a ha;exact hκx a ((hrootRow a) ▸ ha)
    exact (mem_presentColours d x κ).mp ((mem_paletteA d q x y κ).mp hγA).1 hf
  have hγC₀ : γ∈insert α T := by
    rcases mem_insert.mp hγC with he|hγT
    · exact mem_insert.mpr (Or.inl he)
    · exact mem_insert_of_mem ((mem_image_swap_of_ne T κ η γ hγκ hγη).mp hγT)
  have hγA₀ : γ∈paletteA c q x y:=hA ▸ hγA
  have hh:=hlarge γ hγC₀ hγI hγA₀ v ((hyrow v) ▸ hyv)
  have hdrop:=CaoChenFinitePaletteProgress.root_overlap_drop_le_one_kempe c x κ η r hoff hηx v
  omega

end OverfullWork.CaoChenFiniteRoleInvariant
