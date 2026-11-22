module

public import OverfullWork.CaoChenPaletteContinuationSpine
public import OverfullWork.CaoChenPaletteCounting

@[expose] public section


/-! # General S-spines outside the double-maximum case

The genuine palette switching preserves the set of incident edges carrying
an S-colour. Properness therefore preserves the number of present S-colours,
even though individual missing colours need not be preserved. This transports
the missing-y spine results to every S-coloured spine. The bad-colour inclusion
is asserted only when y or the spine endpoint is nonmaximum.
-/
namespace OverfullWork.CaoChenR1Continuation
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenPalettes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 3000000

/-- A palette's present-colour count depends only on its incident edges.
Individual colours on those edges may change. -/
theorem palettePresent_card_eq_of_same_edge_membership
    (c c' : PEC G (Fin G.maxDegree)) (F : Finset (Fin G.maxDegree)) (u : V)
    (he : ∀w,edgeInPalette c F u w↔edgeInPalette c' F u w) :
    (F∩presentColours c u).card=(F∩presentColours c' u).card := by
  have hcount (d : PEC G (Fin G.maxDegree)) :
      (univ.filter (fun w => edgeInPalette d F u w)).card=(F∩presentColours d u).card := by
    apply CaoChenPaletteCounting.card_leaves_eq_card_colours
    · intro w hw
      obtain ⟨η,hcol,hη⟩:=(mem_filter.mp hw).2
      exact ⟨η,mem_inter.mpr ⟨hη,(presentColours_iff_coloured d u η).mpr ⟨w,hcol⟩⟩,hcol⟩
    · intro η hη
      obtain ⟨hηF,hηP⟩:=mem_inter.mp hη
      obtain ⟨w,hw⟩:=(presentColours_iff_coloured d u η).mp hηP
      exact ⟨w,mem_filter.mpr ⟨mem_univ w,η,hw,hηF⟩,hw⟩
  rw [←hcount c,←hcount c']
  congr 1
  ext w
  simp only [mem_filter,mem_univ,true_and,he]

/-- If all palette colours are present after a switching which preserves
palette-edge membership, they were all present before it as well. -/
theorem palette_subset_present_of_same_edge_membership
    (c c' : PEC G (Fin G.maxDegree)) (F : Finset (Fin G.maxDegree)) (u : V)
    (he : ∀w,edgeInPalette c F u w↔edgeInPalette c' F u w)
    (hp : F⊆presentColours c' u) : F⊆presentColours c u := by
  have hc:=palettePresent_card_eq_of_same_edge_membership c c' F u he
  have hEq : F∩presentColours c u=F := by
    apply eq_of_subset_of_card_le inter_subset_left
    rw [hc,inter_eq_left.mpr hp]
  exact inter_eq_left.mp hEq

/-- Construct the palette switching without postulating either of its
auxiliary missing colours. The degree threshold supplies their intersection. -/
theorem exists_palette_switching_from_threshold (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (q : ℝ)
    (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hαA : α∈paletteA c q x y) :
    ∃(θ : Fin G.maxDegree) (v : V) (c' : PEC G (Fin G.maxDegree)),
      SwitchingResult c c' q x y v α θ := by
  obtain ⟨_,v,hyv,hlow⟩:=(mem_paletteA c q x y α).mp hαA
  obtain ⟨θ,hθ⟩:=hcm.exists_free_right
  have hvx : v≠x := by
    intro he
    subst v
    have hyx : c.col y x=none := by rw [c.col_symm];exact hcm.uncol
    rw [hyx] at hyv
    contradiction
  have hsum : G.degree x+G.degree v<G.maxDegree := by
    exact_mod_cast (show (G.degree x:ℝ)+(G.degree v:ℝ)<(G.maxDegree:ℝ) by linarith)
  have hbudget : (∑w∈({x,v}:Finset V),G.degree w)+
      (∅ : Finset (Fin G.maxDegree)).card<G.maxDegree := by
    simpa [sum_pair (Ne.symm hvx)] using hsum
  obtain ⟨δ,_,hδ⟩:=CommonMissingColour.exists_common_free_outside_of_degree_budget c {x,v} ∅ hbudget
  obtain ⟨c',hsw⟩:=exists_palette_switching hG hcm q α θ δ hαA hyv hθ
    (hδ x (by simp)) (hδ v (by simp))
  exact ⟨θ,v,c',hsw⟩

/-- Every S-colour is present at the endpoint of any S-coloured spine.
This existence statement has no nonmaximum-endpoint hypothesis. -/
theorem paletteS_subset_present_at_spine_of_paletteS (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α)
    (q : ℝ) (hq : 0<q) (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hαS : α∈paletteS c q x y) : paletteS c q x y⊆presentColours c u := by
  have hcases : α∈paletteA c q x y ∨ InA c x y α := by
    simpa only [paletteS,mem_union,mem_missing,InA,or_assoc] using hαS
  rcases hcases with ha|hx|hy
  · obtain ⟨θ,v,c',hsw⟩:=exists_palette_switching_from_threshold hcrit.2.1 hcm q hsmall ha
    have hxu' : c'.col x u=some α := by rw [hsw.leftRow];exact hxu
    have hp : paletteS c q x y⊆presentColours c' u := by
      rw [←hsw.palette_eq]
      exact paletteS_subset_present_at_spine hcrit hsw.cm hxu' hsw.etaMissing q hq hsmall
    apply palette_subset_present_of_same_edge_membership c c' (paletteS c q x y) u ?_ hp
    intro w
    simpa only [hsw.palette_eq] using (hsw.edge_membership u w).symm
  · exact False.elim (hx u hxu)
  · exact paletteS_subset_present_at_spine hcrit hcm hxu hy q hq hsmall

/-- Lemma 12's bad-colour exclusion for an arbitrary S-coloured spine,
outside the double-maximum case d(y)=d(u)=Delta. -/
theorem badColours_spine_subset_paletteB_of_paletteS_nonmaximum
    (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α)
    (q : ℝ) (hq : 0<q) (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (hαS : α∈paletteS c q x y)
    (hnonmax : G.degree y<G.maxDegree ∨ G.degree u<G.maxDegree) :
    badColours c q u\{α}⊆paletteB c q x y := by
  have hcases : α∈paletteA c q x y ∨ InA c x y α := by
    simpa only [paletteS,mem_union,mem_missing,InA,or_assoc] using hαS
  rcases hcases with ha|hx|hy
  · obtain ⟨θ,v,c',hsw⟩:=exists_palette_switching_from_threshold hcrit.2.1 hcm q hsmall ha
    have hxu' : c'.col x u=some α := by rw [hsw.leftRow];exact hxu
    have hnew:=badColours_spine_subset_paletteB_of_nonmaximum hcrit hsw.cm hxu'
      hsw.etaMissing q hq hsmall hnonmax
    have hp:=paletteS_subset_present_at_spine_of_paletteS hcrit hcm hxu q hq hsmall hαS
    intro β hβ
    obtain ⟨hb,hne⟩:=mem_sdiff.mp hβ
    have hβα : β≠α:=by simpa only [mem_singleton] using hne
    have hnS : β∉paletteS c q x y := by
      intro hβS
      rcases (mem_badColours c q u β).mp hb with hfree|⟨z,huz,hlow⟩
      · exact (mem_presentColours c u β).mp (hp hβS) hfree
      · have hzx : z≠x := by
          intro he
          subst z
          exact hβα (Option.some.inj (huz.symm.trans ((c.col_symm u x).trans hxu)))
        obtain ⟨γ,hγcol,hγS⟩:=(hsw.edge_membership u z).mpr ⟨β,huz,hβS⟩
        have hγα : γ≠α := by
          intro he
          subst γ
          have hux : c'.col u x=some α := by rw [c'.col_symm];exact hxu'
          exact hzx (c'.col_proper hγcol hux)
        have hγbad : γ∈badColours c' q u :=
          (mem_badColours c' q u γ).mpr (Or.inr ⟨z,hγcol,hlow⟩)
        have hγB:=hnew (mem_sdiff.mpr ⟨hγbad,by simpa only [mem_singleton] using hγα⟩)
        exact (Finset.disjoint_left.mp (disjoint_paletteS_paletteB c' q x y)) hγS hγB
    have hall : β∈paletteS c q x y∪paletteB c q x y := by
      rw [paletteS_union_paletteB]
      exact mem_univ β
    exact (mem_union.mp hall).resolve_left hnS
  · exact False.elim (hx u hxu)
  · exact badColours_spine_subset_paletteB_of_nonmaximum hcrit hcm hxu hy q hq hsmall hnonmax

end OverfullWork.CaoChenR1Continuation
