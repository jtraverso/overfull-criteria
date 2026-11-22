module

public import OverfullWork.CaoChenPalettes
public import Overfull.ForkBasic

@[expose] public section


/-! # The actual (eta,theta,delta)-switching of Cao--Chen Lemma 6

The operation is a Kempe change followed by replacement of the colour on
one already coloured edge. The palette and protected edge rows are proved
invariant; no switching outcome is supplied as a hypothesis.
-/
namespace OverfullWork.CaoChenPalettes
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

/-- Membership of a coloured edge in a palette, including the uncoloured case. -/
def edgeInPalette {k : ℕ} (c : PEC G (Fin k)) (F : Finset (Fin k)) (u v : V) : Prop :=
  ∃ η, c.col u v = some η ∧ η ∈ F

theorem mem_badColours_iff_not_high {k : ℕ} (c : PEC G (Fin k)) (q : ℝ) (v : V) (η : Fin k) :
    η ∈ badColours c q v ↔ η ∉ highColours c q v := by
  have hu : η ∈ badColours c q v ∨ η ∈ highColours c q v := by
    rw [← mem_union, bad_high_partition]
    exact mem_univ _
  have hd := Finset.disjoint_left.mp (bad_high_disjoint c q v)
  tauto

theorem edgeInPalette_kempeSwap {k : ℕ} (c : PEC G (Fin k)) (F : Finset (Fin k))
    (δ θ : Fin k) (hδ : δ ∈ F) (hθ : θ ∈ F) (w u v : V) :
    edgeInPalette (c.kempeSwap δ θ w) F u v ↔ edgeInPalette c F u v := by
  have hswap : ∀ η, Equiv.swap δ θ η ∈ F ↔ η ∈ F := by
    intro η
    by_cases heδ : η = δ
    · subst η
      rw [Equiv.swap_apply_left]
      exact iff_of_true hθ hδ
    by_cases heθ : η = θ
    · subst η
      rw [Equiv.swap_apply_right]
      exact iff_of_true hδ hθ
    · rw [Equiv.swap_apply_of_ne_of_ne heδ heθ]
  unfold edgeInPalette
  by_cases hr : (c.kempeGraph δ θ).Reachable w u
  · rw [kempeSwap_col, kempeSwapFun_of_reachable c δ θ hr v]
    cases hc : c.col u v with
    | none => simp
    | some η => simpa using hswap η
  · rw [kempeSwap_col, kempeSwapFun_of_not_reachable c δ θ hr v]

theorem edgeInPalette_setEdge {k : ℕ} (c : PEC G (Fin k)) (F : Finset (Fin k))
    {y z : V} (θ : Fin k) (hyz : G.Adj y z) (hy : c.IsFree y θ) (hz : c.IsFree z θ)
    {η : Fin k} (he : c.col y z = some η) (hηF : η ∈ F) (hθF : θ ∈ F) (u v : V) :
    edgeInPalette (c.setEdge θ hyz hy hz) F u v ↔ edgeInPalette c F u v := by
  by_cases h : (u = y ∧ v = z) ∨ (u = z ∧ v = y)
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact iff_of_true ⟨θ, by simp, hθF⟩ ⟨η, he, hηF⟩
    · exact iff_of_true ⟨θ, by simp [setEdge_col,updFun], hθF⟩
        ⟨η, by rw [c.col_symm];exact he, hηF⟩
  · unfold edgeInPalette
    rw [setEdge_col,updFun_of_ne _ h]

/-- Replacing a colour on an edge to a low neighbour leaves the high
palette unchanged. The old colour need not be missing at either endpoint. -/
theorem highColours_setEdge_of_low {k : ℕ} (c : PEC G (Fin k)) (q : ℝ)
    {y z : V} (θ : Fin k) (hyz : G.Adj y z) (hy : c.IsFree y θ) (hz : c.IsFree z θ)
    (hlow : (G.degree z : ℝ) < q) :
    highColours (c.setEdge θ hyz hy hz) q y = highColours c q y := by
  ext η
  rw [mem_highColours,mem_highColours]
  have hrow : ∀ w, q ≤ (G.degree w : ℝ) →
      (c.setEdge θ hyz hy hz).col y w = c.col y w := by
    intro w hw
    have hwz : w ≠ z := by intro he;subst w;exact (not_lt_of_ge hw) hlow
    have hyzNe := hyz.ne
    rw [setEdge_col,updFun_of_ne _ (by tauto)]
  constructor
  · rintro ⟨w,hw,hq⟩
    exact ⟨w,(hrow w hq) ▸ hw,hq⟩
  · rintro ⟨w,hw,hq⟩
    exact ⟨w,(hrow w hq).symm ▸ hw,hq⟩

/-- All conclusions of Lemma 6, stated without choosing x_theta. -/
structure SwitchingResult (c c' : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y z : V) (η θ : Fin G.maxDegree) : Prop where
  cm : IsColMinus c' x y
  newColour : c'.col y z = some θ
  leftRow : ∀ w, c'.col x w = c.col x w
  thetaRow : ∀ w, c.col x w = some θ → ∀ v, c'.col w v = c.col w v
  rightRow : ∀ v, v ≠ z → c'.col y v = c.col y v
  etaEdges : ∀ a b, c.col a b = some η → s(a,b) ≠ s(y,z) →
    c'.col a b = some η
  etaMissing : c'.IsFree y η
  thetaInA : θ ∈ paletteA c' q x y
  palette_eq : paletteS c' q x y = paletteS c q x y
  edge_membership : ∀ u v, edgeInPalette c' (paletteS c' q x y) u v ↔
    edgeInPalette c (paletteS c q x y) u v

/-- Construct the genuine three-colour switching. Distinctness of its
colours follows from the free/present hypotheses and is not postulated. -/
theorem exists_palette_switching (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y z : V} (hcm : IsColMinus c x y) (q : ℝ)
    (η θ δ : Fin G.maxDegree) (hηA : η ∈ paletteA c q x y)
    (hyz : c.col y z = some η) (hθy : c.IsFree y θ)
    (hδx : c.IsFree x δ) (hδz : c.IsFree z δ) :
    ∃ c' : PEC G (Fin G.maxDegree), SwitchingResult c c' q x y z η θ := by
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
  refine ⟨c₂,⟨?_,hnew,hleft,htheta,hright,hetaEdges,?_,hthetaA,hS,?_⟩⟩
  · exact ⟨hcm.adj,by rw [hleft,hcm.uncol],fun u v huv hne =>
      extends_setEdge c₁ θ hAdj hθy₁ hθz₁ u v (hcm₁.total u v huv hne)⟩
  · exact isFree_setEdge_old c₁ θ hAdj hθy₁ hθz₁ hyz₁
  · intro u v
    rw [hS]
    exact (edgeInPalette_setEdge c₁ (paletteS c q x y) θ hAdj hθy₁ hθz₁ hyz₁ hηS hθS u v).trans
      (edgeInPalette_kempeSwap c (paletteS c q x y) δ θ hδS hθS z u v)

end OverfullWork.CaoChenPalettes
