module

public import OverfullWork.CaoChenBadColourLinkage
public import OverfullWork.CaoChenProtectedPaletteSwitching

@[expose] public section


/-! # Links forced by low continuation leaves

A low continuation from a missing-y spine is linked to x by every colour
missing at x. This is a linkage constraint, not an exclusion of every low
continuation. It will give a capacity bound once common missing sets at
different low leaves are counted.
-/
namespace OverfullWork.CaoChenR1Continuation
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenPalettes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 3000000

/-- A low continuation is linked to x for every kappa missing at x.
Kappa need not be missing at the continuation endpoint. -/
theorem low_leaf_linked_of_missing_spine_colour (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u z : V} {α β κ : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (hβα : β≠α) (huz : c.col u z=some β)
    (q : ℝ) (hq : 0<q) (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hlow : (G.degree z:ℝ)<q) (hκx : c.IsFree x κ) :
    (c.kempeGraph κ β).Reachable x z := by
  have hκα : κ≠α := by intro he;subst κ;exact hκx u hxu
  by_contra hn
  have hoff : ¬(c.kempeGraph κ β).Reachable z x := fun h => hn h.symm
  let c' := c.kempeSwap κ β z
  have hxu' : c'.col x u=some α :=
    kempeSwap_col_of_ne c κ β z x u hxu (Ne.symm hκα) (Ne.symm hβα)
  have hα' : c'.IsFree y α :=
    (kempeSwap_isFree_of_ne c κ β z y (Ne.symm hκα) (Ne.symm hβα)).mpr hα
  have hκx' : c'.IsFree x κ :=
    (isFree_kempeSwap_of_not_reachable c κ β hoff κ).mpr hκx
  have hreach : (c.kempeGraph κ β).Reachable z u :=
    (kempeGraph_adj_of_col (Or.inr (show c.col z u=some β by rw [c.col_symm];exact huz))).reachable
  have huz' : c'.col u z=some κ := by
    rw [kempeSwap_col,kempeSwapFun_of_reachable c κ β hreach z,huz]
    simp only [Option.map_some,Equiv.swap_apply_right]
  obtain ⟨w,huw,_,hhigh⟩:=exists_continuation_above_threshold hcrit (hcm.kempeSwap κ β z)
    hxu' hα' hκα (Or.inl hκx') q hq hsmall
  have hzw : z=w:=c'.col_proper huz' huw
  subst w
  linarith

/-- For an arbitrary S-spine, a low continuation whose colour is present
at y is linked to x by every colour missing at x. Two units of threshold
slack allow the switching to protect both prescribed colours. -/
theorem low_leaf_linked_of_palette_spine_present_right (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u z : V} {α β κ : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α)
    (hβα : β≠α) (huz : c.col u z=some β)
    (q : ℝ) (hq : 0<q) (hroom : (G.degree x:ℝ)+q+2≤(G.maxDegree:ℝ))
    (hαS : α∈paletteS c q x y) (hβy : β∈presentColours c y)
    (hlow : (G.degree z:ℝ)<q) (hκx : c.IsFree x κ) :
    (c.kempeGraph κ β).Reachable x z := by
  have hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ):=by linarith
  have hcases : α∈paletteA c q x y ∨ InA c x y α := by
    simpa only [paletteS,mem_union,mem_missing,InA,or_assoc] using hαS
  rcases hcases with ha|hx|hy
  · obtain ⟨_,v,hyv,hv⟩:=(mem_paletteA c q x y α).mp ha
    obtain ⟨θ,hθ⟩:=hcm.exists_free_right
    have hvx : v≠x := by
      intro he
      subst v
      have hyx : c.col y x=none := by rw [c.col_symm];exact hcm.uncol
      rw [hyx] at hyv
      contradiction
    have hsum : G.degree x+G.degree v+2<G.maxDegree := by
      exact_mod_cast (show (G.degree x:ℝ)+(G.degree v:ℝ)+2<(G.maxDegree:ℝ) by linarith)
    have hbudget : (∑w∈({x,v}:Finset V),G.degree w)+
        ({β,κ} : Finset (Fin G.maxDegree)).card<G.maxDegree := by
      have hc : ({β,κ}:Finset (Fin G.maxDegree)).card≤2:=card_le_two
      rw [sum_pair (Ne.symm hvx)]
      omega
    obtain ⟨δ,hδ,hfree⟩:=CommonMissingColour.exists_common_free_outside_of_degree_budget
      c {x,v} {β,κ} hbudget
    have hδβ : δ≠β:=by intro he;exact hδ (by simp [he])
    have hδκ : δ≠κ:=by intro he;exact hδ (by simp [he])
    have hκα : κ≠α := by intro he;subst κ;exact hκx u hxu
    have hκθ : κ≠θ := by
      intro he
      subst κ
      exact (hcm.ab_facts hcrit.2.1).1 θ hκx hθ
    have hβθ : β≠θ := by
      intro he
      subst β
      exact (mem_presentColours c y θ).mp hβy hθ
    obtain ⟨c',hsw⟩:=exists_protected_palette_switching hcrit.2.1 hcm α θ δ hyv hθ
      (hfree x (by simp)) (hfree v (by simp))
    have hxu' : c'.col x u=some α := by rw [hsw.leftRow];exact hxu
    have huz' : c'.col u z=some β :=
      (hsw.otherEdges β hβα hβθ (Ne.symm hδβ) u z).mpr huz
    have hκx' : c'.IsFree x κ := by
      intro w hw
      exact hκx w ((hsw.otherEdges κ hκα hκθ (Ne.symm hδκ) x w).mp hw)
    have hgraph : c'.kempeGraph κ β=c.kempeGraph κ β := by
      ext a b
      simp only [kempeGraph_adj,hsw.otherEdges κ hκα hκθ (Ne.symm hδκ),
        hsw.otherEdges β hβα hβθ (Ne.symm hδβ)]
    have hlink:=low_leaf_linked_of_missing_spine_colour hcrit hsw.cm hxu' hsw.etaMissing
      hβα huz' q hq hsmall hlow hκx'
    rw [hgraph] at hlink
    exact hlink
  · exact False.elim (hx u hxu)
  · exact low_leaf_linked_of_missing_spine_colour hcrit hcm hxu hy hβα huz q hq hsmall hlow hκx

end OverfullWork.CaoChenR1Continuation
