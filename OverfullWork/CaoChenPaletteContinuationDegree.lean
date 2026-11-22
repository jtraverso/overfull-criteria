module

public import OverfullWork.CaoChenPaletteContinuationExistence
public import OverfullWork.CaoChenPaletteSwitching

@[expose] public section


/-! # Palette-A continuation degrees when the right endpoint is not maximum

The second colour missing at y permits the genuine Lemma 6 switching while
keeping the spine colour missing at y. This proves the high-degree part of
Lemma 11 for palette A under d(y) < Delta. The case d(y) = Delta is not asserted.
-/
namespace OverfullWork.CaoChenR1Continuation
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenPalettes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000

/-- The palette-A continuation has the required high degree when y misses
at least two colours. Both missing colours and the switching are constructed. -/
theorem exists_high_continuation_of_paletteA_right_nonmaximum
    (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (hβα : β≠α) (q : ℝ) (hq : 0<q)
    (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hdy : G.degree y<G.maxDegree) (hβA : β∈paletteA c q x y) :
    ∃ z : V,c.col u z=some β ∧ G.maxDegree-G.degree x+2≤G.degree z ∧
      q<(G.degree z:ℝ) := by
  obtain ⟨z,huz⟩:=exists_continuation_of_paletteA hcrit hcm hxu hα hβα q hq hsmall hβA
  obtain ⟨_,v,hyv,hlow⟩:=(mem_paletteA c q x y β).mp hβA
  obtain ⟨μ,ν,hμν,hμ,hν⟩:=hcm.two_free_right hdy
  obtain ⟨θ,hθ,hθα⟩ : ∃θ,c.IsFree y θ ∧ θ≠α := by
    by_cases he : μ=α
    · exact ⟨ν,hν,by intro hn;exact hμν (he.trans hn.symm)⟩
    · exact ⟨μ,hμ,he⟩
  have hvx : v≠x := by
    intro he
    subst v
    have hyx : c.col y x=none := by rw [c.col_symm];exact hcm.uncol
    rw [hyx] at hyv
    contradiction
  have huy : u≠y := by
    intro he
    subst u
    rw [hcm.uncol] at hxu
    contradiction
  have huHigh : q<(G.degree u:ℝ) := by
    have hh:=spine_degree_bound hcrit.2.1 hcm hxu hα
    have hn : G.maxDegree+2≤G.degree x+G.degree u := by omega
    have hr : (G.maxDegree:ℝ)+2≤(G.degree x:ℝ)+(G.degree u:ℝ) := by exact_mod_cast hn
    linarith
  have huv : u≠v := by
    intro he
    rw [he] at huHigh
    linarith
  have hsum : G.degree x+G.degree v<G.maxDegree := by
    exact_mod_cast (show (G.degree x:ℝ)+(G.degree v:ℝ)<(G.maxDegree:ℝ) by linarith)
  have hbudget : (∑ w∈({x,v}:Finset V),G.degree w)+
      (∅ : Finset (Fin G.maxDegree)).card<G.maxDegree := by
    simpa [sum_pair (Ne.symm hvx)] using hsum
  obtain ⟨δ,_,hδ⟩:=CommonMissingColour.exists_common_free_outside_of_degree_budget c {x,v} ∅ hbudget
  obtain ⟨c',hsw⟩:=exists_palette_switching hcrit.2.1 hcm q β θ δ hβA hyv hθ
    (hδ x (by simp)) (hδ v (by simp))
  have hα' : c'.IsFree y α := by
    intro w hw
    by_cases hwv : w=v
    · subst w
      rw [hsw.newColour] at hw
      exact hθα (Option.some.inj hw)
    · rw [hsw.rightRow w hwv] at hw
      exact hα w hw
  have hxu' : c'.col x u=some α := by rw [hsw.leftRow];exact hxu
  have huz' : c'.col u z=some β := by
    apply hsw.etaEdges u z huz
    intro he
    rcases Sym2.eq_iff.mp he with ⟨huy',_⟩|⟨huv',_⟩
    · exact huy huy'
    · exact huv huv'
  obtain ⟨z',hz',hdeg,hhigh⟩:=exists_continuation_above_threshold hcrit hsw.cm
    hxu' hα' hβα (Or.inr hsw.etaMissing) q hq hsmall
  have hzz : z=z':=c'.col_proper huz' hz'
  subst z'
  exact ⟨z,huz,hdeg,hhigh⟩

/-- Consequently the full S-palette continuation conclusion holds when
the right endpoint is not maximum. No degree assumption on the spine is used. -/
theorem exists_high_continuation_of_paletteS_right_nonmaximum
    (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (hβα : β≠α) (q : ℝ) (hq : 0<q)
    (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hdy : G.degree y<G.maxDegree) (hβS : β∈paletteS c q x y) :
    ∃ z : V,c.col u z=some β ∧ G.maxDegree-G.degree x+2≤G.degree z ∧
      q<(G.degree z:ℝ) := by
  have hcases : β∈paletteA c q x y ∨ InA c x y β := by
    simpa only [paletteS,mem_union,mem_missing,InA,or_assoc] using hβS
  rcases hcases with ha|hb
  · exact exists_high_continuation_of_paletteA_right_nonmaximum hcrit hcm hxu hα hβα q hq hsmall hdy ha
  · exact exists_continuation_above_threshold hcrit hcm hxu hα hβα hb q hq hsmall

end OverfullWork.CaoChenR1Continuation
