module

public import OverfullWork.CaoChenPaletteContinuationDegree

@[expose] public section


/-! # Continuation thresholds with a nonmaximum spine vertex

Moving the uncoloured edge from xy to xu reverses the two roles of y and u.
If a beta-continuation from u went below q, the proved nonmaximum-right-end
case in the shifted colouring would force the original low beta-neighbour
of y above q. This gives the threshold needed to exclude bad colours,
without claiming the sharper degree bound in the remaining case.
-/
namespace OverfullWork.CaoChenR1Continuation
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenPalettes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000

/-- An actual palette-A continuation stays above the threshold if the
spine vertex u is not maximum, even when d(y)=Delta. -/
theorem continuation_threshold_of_paletteA_spine_nonmaximum
    (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u z : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (hβα : β≠α) (q : ℝ) (hq : 0<q)
    (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hdu : G.degree u<G.maxDegree) (hβA : β∈paletteA c q x y)
    (huz : c.col u z=some β) : q≤(G.degree z:ℝ) := by
  obtain ⟨hβx,v,hyv,hlow⟩:=(mem_paletteA c q x y β).mp hβA
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
  have hzx : z≠x := by
    intro he
    subst z
    exact hβα (Option.some.inj (huz.symm.trans ((c.col_symm u x).trans hxu)))
  obtain ⟨ψ,hψ,hψyx,hoff,hfreeX,hαu,_⟩:=exists_shift hcm.symm hxu hα hyu
  have hψxy : ψ.col x y=some α := by rw [ψ.col_symm];exact hψyx
  have hψyv : ψ.col y v=some β := by
    rw [hoff y v (by tauto) (by tauto)]
    exact hyv
  have hψuz : ψ.col u z=some β := by
    rw [hoff u z (by tauto) (by tauto)]
    exact huz
  by_contra hn
  have hlowz : (G.degree z:ℝ)<q:=lt_of_not_ge hn
  have hβAψ : β∈paletteA ψ q x u := by
    apply (mem_paletteA ψ q x u β).mpr
    refine ⟨(mem_presentColours ψ x β).mpr ?_,z,hψuz,hlowz⟩
    intro hb
    exact (mem_presentColours c x β).mp hβx ((hfreeX β).mp hb)
  obtain ⟨w,hyw,_,hw⟩:=exists_high_continuation_of_paletteA_right_nonmaximum
    hcrit hψ.symm hψxy hαu hβα q hq hsmall hdu hβAψ
  have hvw : v=w:=ψ.col_proper hψyv hyw
  subst w
  linarith

/-- Every S-colour distinct from alpha has a genuine continuation at or
above q if the spine vertex is not maximum. -/
theorem exists_continuation_at_threshold_of_paletteS_spine_nonmaximum
    (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (hβα : β≠α) (q : ℝ) (hq : 0<q)
    (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hdu : G.degree u<G.maxDegree) (hβS : β∈paletteS c q x y) :
    ∃ z : V,c.col u z=some β ∧ q≤(G.degree z:ℝ) := by
  have hcases : β∈paletteA c q x y ∨ InA c x y β := by
    simpa only [paletteS,mem_union,mem_missing,InA,or_assoc] using hβS
  rcases hcases with ha|hb
  · obtain ⟨z,huz⟩:=exists_continuation_of_paletteA hcrit hcm hxu hα hβα q hq hsmall ha
    exact ⟨z,huz,continuation_threshold_of_paletteA_spine_nonmaximum hcrit hcm hxu hα hβα
      q hq hsmall hdu ha huz⟩
  · obtain ⟨z,huz,_,hz⟩:=exists_continuation_above_threshold hcrit hcm hxu hα hβα hb q hq hsmall
    exact ⟨z,huz,hz.le⟩

/-- The bad-colour exclusion required for Lemma 12, for a missing-y spine
colour alpha, holds if y or the spine vertex u is not maximum. The case
where both degrees equal Delta is not asserted. -/
theorem badColours_spine_subset_paletteB_of_nonmaximum
    (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (q : ℝ) (hq : 0<q) (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hnonmax : G.degree y<G.maxDegree ∨ G.degree u<G.maxDegree) :
    badColours c q u\{α}⊆paletteB c q x y := by
  intro β hβ
  obtain ⟨hbad,hne⟩:=mem_sdiff.mp hβ
  have hβα : β≠α:=by simpa only [mem_singleton] using hne
  have hnotS : β∉paletteS c q x y := by
    intro hβS
    obtain ⟨z,huz,hz⟩ : ∃z,c.col u z=some β ∧ q≤(G.degree z:ℝ) := by
      rcases hnonmax with hy|hu
      · obtain ⟨z,huz,_,hz⟩:=exists_high_continuation_of_paletteS_right_nonmaximum
          hcrit hcm hxu hα hβα q hq hsmall hy hβS
        exact ⟨z,huz,hz.le⟩
      · exact exists_continuation_at_threshold_of_paletteS_spine_nonmaximum
          hcrit hcm hxu hα hβα q hq hsmall hu hβS
    exact (Finset.disjoint_left.mp (bad_high_disjoint c q u)) hbad
      ((mem_highColours c q u β).mpr ⟨z,huz,hz⟩)
  have hall : β∈paletteS c q x y∪paletteB c q x y := by
    rw [paletteS_union_paletteB]
    exact mem_univ β
  exact (mem_union.mp hall).resolve_left hnotS

end OverfullWork.CaoChenR1Continuation
