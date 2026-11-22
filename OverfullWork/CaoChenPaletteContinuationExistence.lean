module

public import OverfullWork.CaoChenMissingContinuations
public import OverfullWork.CaoChenPalettes
public import Overfull.Shift

@[expose] public section


/-! # Actual continuation existence for the full Cao--Chen palette S

Moving the missing edge exposes a short Kierstead path. Its elementary
property rules out a palette-A colour missing at the spine vertex. This
proves existence for palette A and hence for all S; it does not claim the
remaining high-degree conclusion for a palette-A continuation endpoint.
-/
namespace OverfullWork.CaoChenR1Continuation
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenPalettes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000

/-- The palette-A case of existence in Lemma 11, proved by moving the
uncoloured edge and using the short Kierstead path, without Woodall as an input. -/
theorem exists_continuation_of_paletteA (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (_hβα : β≠α) (q : ℝ) (hq : 0<q)
    (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hβA : β∈paletteA c q x y) : ∃ z : V,c.col u z=some β := by
  obtain ⟨_hβx,v,hyv,hlow⟩:=(mem_paletteA c q x y β).mp hβA
  have hxy : x≠y:=hcm.adj.ne
  have hyu : y≠u := by
    intro he
    subst u
    rw [hcm.uncol] at hxu
    contradiction
  have hxuNe : x≠u:=(c.col_adj hxu).ne
  have hvx : v≠x := by
    intro he
    subst v
    have hyx : c.col y x=none := by rw [c.col_symm];exact hcm.uncol
    rw [hyx] at hyv
    contradiction
  have hyvNe : y≠v:=(c.col_adj hyv).ne
  have hdx : G.degree x<G.maxDegree := by
    exact_mod_cast (show (G.degree x:ℝ)<(G.maxDegree:ℝ) by linarith)
  have huHigh : q<(G.degree u:ℝ) := by
    have hh:=spine_degree_bound hcrit.2.1 hcm hxu hα
    have hn : G.maxDegree+2≤G.degree x+G.degree u := by omega
    have hr : (G.maxDegree:ℝ)+2≤(G.degree x:ℝ)+(G.degree u:ℝ) := by exact_mod_cast hn
    linarith
  have huv : u≠v := by intro he;rw [he] at huHigh;exact (not_lt_of_ge hlow.le) huHigh
  by_contra hn
  have hβu : c.IsFree u β := by intro z hz;exact hn ⟨z,hz⟩
  obtain ⟨ψ,hψ,hψyx,hoff,hfreeX,hαu,_hfreeOff⟩:=exists_shift hcm.symm hxu hα hyu
  have hψxy : ψ.col x y=some α := by rw [ψ.col_symm];exact hψyx
  have hψyv : ψ.col y v=some β := by
    rw [hoff y v (by tauto) (by tauto)]
    exact hyv
  have hβuψ : ψ.IsFree u β := by
    intro w hw
    by_cases hwx : w=x
    · subst w
      rw [hψ.uncol] at hw
      contradiction
    · have he : ψ.col u w=c.col u w:=hoff u w (by tauto) (by tauto)
      rw [he] at hw
      exact hβu w hw
  have hK : IsK4 ψ u x y v α β :=
    ⟨hψ,hψxy,hψyv,hαu,Or.inl hβuψ,hyu.symm,huv,Ne.symm hvx⟩
  have hsum : G.degree x+G.degree v<G.maxDegree := by
    exact_mod_cast (show (G.degree x:ℝ)+(G.degree v:ℝ)<(G.maxDegree:ℝ) by linarith)
  have hbudget : (∑ w∈({x,v}:Finset V),G.degree w)+(∅ : Finset (Fin G.maxDegree)).card<G.maxDegree := by
    simpa [sum_pair (Ne.symm hvx)] using hsum
  obtain ⟨θ,_,hθ⟩:=CommonMissingColour.exists_common_free_outside_of_degree_budget ψ {x,v} ∅ hbudget
  exact hK.not_common_of_degree_b hcrit.2.1 hdx (Or.inr (hθ x (by simp))) (hθ v (by simp))

/-- Every colour in S distinct from the spine colour has an actual
continuation. The high-degree conclusion is asserted separately only
for the endpoint-missing cases in CaoChenMissingContinuations. -/
theorem exists_continuation_of_paletteS (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (hβα : β≠α) (q : ℝ) (hq : 0<q)
    (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hβS : β∈paletteS c q x y) : ∃ z : V,c.col u z=some β := by
  have hcases : β∈paletteA c q x y ∨ InA c x y β := by
    simpa only [paletteS,mem_union,mem_missing,InA,or_assoc] using hβS
  rcases hcases with ha|hb
  · exact exists_continuation_of_paletteA hcrit hcm hxu hα hβα q hq hsmall ha
  · obtain ⟨z,hz,_,_⟩:=exists_continuation_above_threshold hcrit hcm hxu hα hβα hb q hq hsmall
    exact ⟨z,hz⟩

/-- Selector-free presence of the complete palette S at the spine vertex. -/
theorem paletteS_subset_present_at_spine (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (q : ℝ) (hq : 0<q) (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ)) :
    paletteS c q x y⊆presentColours c u := by
  intro β hβ
  apply (presentColours_iff_coloured c u β).mpr
  by_cases he : β=α
  · subst β
    exact ⟨x,by rw [c.col_symm];exact hxu⟩
  · exact exists_continuation_of_paletteS hcrit hcm hxu hα he q hq hsmall hβ

end OverfullWork.CaoChenR1Continuation
