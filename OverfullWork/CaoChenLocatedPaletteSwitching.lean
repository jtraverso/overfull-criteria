module

public import OverfullWork.CaoChenFullPaletteSwitching

@[expose] public section


/-! # Full palette switching with an exact location formula

The single concrete Kempe-swap/setEdge witness satisfies both older sets of
invariants and agrees exactly with the Kempe colouring away from the one
replaced edge. This extra formula supports transport at off-edge vertices.
-/
namespace OverfullWork.CaoChenPalettes
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- A single constructed recolouring satisfies Lemma 6 and exact protection
of every colour outside eta, theta, delta simultaneously. -/
theorem exists_located_full_palette_switching (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y z : V} (hcm : IsColMinus c x y) (q : ℝ)
    (η θ δ : Fin G.maxDegree) (hηA : η ∈ paletteA c q x y)
    (hyz : c.col y z = some η) (hθy : c.IsFree y θ)
    (hδx : c.IsFree x δ) (hδz : c.IsFree z δ) :
    ∃ c' : PEC G (Fin G.maxDegree), SwitchingResult c c' q x y z η θ ∧
      ProtectedPaletteSwitching c c' x y z η θ δ ∧
      (∀a b,s(a,b)≠s(y,z) → c'.col a b=(c.kempeSwap δ θ z).col a b) ∧
      (∀u,u≠y → u≠z → ∀v,c'.col u v=(c.kempeSwap δ θ z).col u v) := by
  classical
  have hAdj := c.col_adj hyz
  have hyzNe : y ≠ z := hAdj.ne
  have hxz : x ≠ z := by
    intro he
    subst z
    have hh := hyz
    rw [c.col_symm,hcm.uncol] at hh
    cases hh
  have hzx : z ≠ x := hxz.symm
  have hzy : z ≠ y := hyzNe.symm
  have hlink := (hcm.ab_facts hG).2 δ θ hδx hθy
  have hoffx : ¬ (c.kempeGraph δ θ).Reachable z x := by
    intro hz
    exact not_three_linked c hcm.adj.ne hxz hyzNe
      (Or.inl hδx) (Or.inr hθy) (Or.inl hδz) hlink hz.symm
  have hoffy : ¬ (c.kempeGraph δ θ).Reachable z y := by
    intro hz
    exact hoffx (hz.trans hlink.symm)
  have hηδ : η ≠ δ := by
    intro he
    apply hδz y
    rw [c.col_symm,hyz,he]
  have hηθ : η ≠ θ := by intro he;exact hθy z (he ▸ hyz)
  let c₁ := c.kempeSwap δ θ z
  have hcm₁ : IsColMinus c₁ x y := hcm.kempeSwap δ θ z
  have hyz₁ : c₁.col y z = some η := kempeSwap_col_of_ne c δ θ z y z hyz hηδ hηθ
  have hθy₁ : c₁.IsFree y θ := (isFree_kempeSwap_of_not_reachable c δ θ hoffy θ).mpr hθy
  have hθz₁ : c₁.IsFree z θ := by
    rw [isFree_kempeSwap_of_reachable c δ θ (SimpleGraph.Reachable.refl z),Equiv.swap_apply_right]
    exact hδz
  let c₂ := c₁.setEdge θ hAdj hθy₁ hθz₁
  have hleft : ∀ w,c₂.col x w=c.col x w := by
    intro w
    rw [setEdge_col_of_ne_left c₁ θ hAdj hθy₁ hθz₁ hcm.adj.ne hxz,
      kempeSwap_col,kempeSwapFun_of_not_reachable c δ θ hoffx]
  have hright : ∀ v,v≠z → c₂.col y v=c.col y v := by
    intro v hv
    change updFun c₁.col y z (some θ) y v = c.col y v
    rw [updFun_of_ne _ (by tauto),kempeSwap_col,kempeSwapFun_of_not_reachable c δ θ hoffy]
  have htheta : ∀ w,c.col x w=some θ → ∀ v,c₂.col w v=c.col w v := by
    intro w hxw v
    have hoffw : ¬ (c.kempeGraph δ θ).Reachable z w := by
      intro hr
      have hwx : (c.kempeGraph δ θ).Reachable w x :=
        (kempeGraph_adj_of_col (Or.inr (show c.col w x=some θ by rw [c.col_symm];exact hxw))).reachable
      exact hoffx (hr.trans hwx)
    have hwy : w≠y := by intro he;subst w;rw [hcm.uncol] at hxw;cases hxw
    have hwz : w≠z := by
      intro he
      subst w
      exact hoffw (SimpleGraph.Reachable.refl z)
    rw [setEdge_col_of_ne_left c₁ θ hAdj hθy₁ hθz₁ hwy hwz,
      kempeSwap_col,kempeSwapFun_of_not_reachable c δ θ hoffw]
  have hlow : (G.degree z : ℝ)<q := by
    obtain ⟨_,w,hyw,hwq⟩ := (mem_paletteA c q x y η).mp hηA
    have he : z=w := c.col_proper hyz hyw
    rw [he]
    exact hwq
  have hHigh₁ : highColours c₁ q y=highColours c q y := by
    ext ε
    simp only [mem_highColours]
    simp only [c₁,kempeSwap_col,kempeSwapFun_of_not_reachable c δ θ hoffy]
  have hHigh : highColours c₂ q y=highColours c q y :=
    (highColours_setEdge_of_low c₁ q θ hAdj hθy₁ hθz₁ hlow).trans hHigh₁
  have hfreeX : ∀ ε,c₂.IsFree x ε ↔ c.IsFree x ε := by
    intro ε
    simp only [IsFree,hleft]
  have hS : paletteS c₂ q x y=paletteS c q x y := by
    ext ε
    rw [mem_paletteS_iff_free_or_bad,mem_paletteS_iff_free_or_bad,hfreeX,
      mem_badColours_iff_not_high,mem_badColours_iff_not_high,hHigh]
  have hηS : η∈paletteS c q x y := mem_union.mpr (Or.inl (mem_union.mpr (Or.inl hηA)))
  have hθS : θ∈paletteS c q x y := mem_union.mpr (Or.inr (mem_missing.mpr hθy))
  have hδS : δ∈paletteS c q x y := mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_missing.mpr hδx))))
  have hnew : c₂.col y z=some θ := by simp [c₂]
  have hthetaA : θ∈paletteA c₂ q x y := by
    apply (mem_paletteA c₂ q x y θ).mpr
    refine ⟨(mem_presentColours c₂ x θ).mpr ?_,z,hnew,hlow⟩
    intro hh
    exact (hcm.ab_facts hG).1 θ ((hfreeX θ).mp hh) hθy
  have hetaEdges : ∀ a b, c.col a b = some η → s(a,b) ≠ s(y,z) →
      c₂.col a b = some η := by
    intro a b hab hne
    have hoff : ¬ ((a=y ∧ b=z) ∨ (a=z ∧ b=y)) := by
      intro hh
      exact hne (Sym2.eq_iff.mpr hh)
    change updFun c₁.col y z (some θ) a b = some η
    rw [updFun_of_ne _ hoff]
    exact kempeSwap_col_of_ne c δ θ z a b hab hηδ hηθ
  have hresult : SwitchingResult c c₂ q x y z η θ := by
    refine ⟨?_,hnew,hleft,htheta,hright,hetaEdges,?_,hthetaA,hS,?_⟩
    · exact ⟨hcm.adj,by rw [hleft,hcm.uncol],fun u v huv hne =>
        extends_setEdge c₁ θ hAdj hθy₁ hθz₁ u v (hcm₁.total u v huv hne)⟩
    · exact isFree_setEdge_old c₁ θ hAdj hθy₁ hθz₁ hyz₁
    · intro u v
      rw [hS]
      exact (edgeInPalette_setEdge c₁ (paletteS c q x y) θ hAdj hθy₁ hθz₁ hyz₁ hηS hθS u v).trans
        (edgeInPalette_kempeSwap c (paletteS c q x y) δ θ hδS hθS z u v)

  have hpair : ∀ γ,γ≠θ → γ≠δ → ∀ a b,(c₁.col a b=some γ ↔ c.col a b=some γ) := by
    intro γ hγθ hγδ a b
    by_cases hr : (c.kempeGraph δ θ).Reachable z a
    · rw [kempeSwap_col,kempeSwapFun_of_reachable c δ θ hr b]
      cases he : c.col a b with
      | none => simp
      | some ε => simp only [Option.map_some,Option.some.injEq,Equiv.swap_apply_eq_iff,
          Equiv.swap_apply_of_ne_of_ne hγδ hγθ]
    · rw [kempeSwap_col,kempeSwapFun_of_not_reachable c δ θ hr b]
  have hprotected : ProtectedPaletteSwitching c c₂ x y z η θ δ := by
    refine ⟨hresult.cm,hresult.leftRow,hresult.etaMissing,hresult.newColour,?_,?_⟩
    · intro γ hγη hγθ hγδ a b
      by_cases he : (a=y ∧ b=z) ∨ (a=z ∧ b=y)
      · have hold : c.col a b=some η := by
          rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact hyz
          · rw [c.col_symm];exact hyz
        have hnew : c₂.col a b=some θ := by
          rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [c₂,setEdge_col,updFun]
        rw [hnew,hold]
        simp [Ne.symm hγθ,Ne.symm hγη]
      · change (updFun c₁.col y z (some θ) a b=some γ ↔ _)
        rw [updFun_of_ne _ he]
        exact hpair γ hγθ hγδ a b
    · intro a b
      by_cases he : (a=y ∧ b=z) ∨ (a=z ∧ b=y)
      · have hold : c.col a b=some η := by
          rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact hyz
          · rw [c.col_symm];exact hyz
        have hnew : c₂.col a b=some θ := by
          rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [c₂,setEdge_col,updFun]
        rw [hnew,hold]
        simp
      · change (updFun c₁.col y z (some θ) a b=none ↔ _)
        rw [updFun_of_ne _ he,kempeSwap_col]
        by_cases hr : (c.kempeGraph δ θ).Reachable z a
        · rw [kempeSwapFun_of_reachable c δ θ hr b]
          cases hec : c.col a b <;> simp
        · rw [kempeSwapFun_of_not_reachable c δ θ hr b]
  refine ⟨c₂,hresult,hprotected,?_,?_⟩
  · intro a b hab
    change updFun c₁.col y z (some θ) a b=c₁.col a b
    apply updFun_of_ne
    intro he
    exact hab (Sym2.eq_iff.mpr he)
  · intro u huy huz v
    exact setEdge_col_of_ne_left c₁ θ hAdj hθy₁ hθz₁ huy huz v

end OverfullWork.CaoChenPalettes
