module

public import OverfullWork.CaoChenFiniteIntersection
public import OverfullWork.CaoChenLemma8

@[expose] public section


/-! # The actual reciprocal-density exceptional set of Cao--Chen Corollary 10

Lemma 8 excludes a common selected bad-colour subset. The finite double
counting theorem then constructs the exceptional colours. Properness
transports them to actual S-neighbours, with the one removed colour paid
explicitly in the final Delta+Q bound.
-/
namespace OverfullWork.CaoChenCorollary10
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenUniformPaletteBudgets
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- Corollary 10 with an actual root-edge endpoint function. The exclusion
of common subsets is proved by Lemma 8, rather than supplied as a premise. -/
theorem exceptional_colours_with_endpoints (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ) (hk : 1≤k)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (Q : ℕ) (hQ : 1≤Q) (hsize : (3*k+1)*Q*Q≤G.maxDegree)
    (U : Fin G.maxDegree → V)
    (hU : ∀η∈paletteS c ((1-ε)*(G.maxDegree:ℝ)) x y∩presentColours c x,
      c.col x (U η)=some η) :
    ∃X : Finset (Fin G.maxDegree),
      X⊆paletteS c ((1-ε)*(G.maxDegree:ℝ)) x y∩presentColours c x ∧
      X.card≤(k+1)*(Q+1)^(3*k+1) ∧
      ∀η∈(paletteS c ((1-ε)*(G.maxDegree:ℝ)) x y∩presentColours c x)\X,
        Q*((badColours c ((1-ε)*(G.maxDegree:ℝ)) (U η))\{η}).card<G.maxDegree := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  let I:=paletteS c q x y∩presentColours c x
  let A:=fun η => badColours c q (U η)\{η}
  have havoid : ∀J : Finset (Fin G.maxDegree),J⊆I → J.card=k+2 →
      ∀F : Finset (Fin G.maxDegree),F⊆univ → F.card=3*k+1 → ¬∀η∈J,F⊆A η := by
    intro J hJI hJcard F _hFU hFcard hcommon
    exact CaoChenLemma8.no_configuration hG c hcm ε hε hεone k hk hx hscale hlarge
      J U F hJcard hJI (fun η hη => hU η (hJI hη)) hFcard hcommon
  obtain ⟨X,hXI,hX,hgood⟩:=CaoChenFiniteIntersection.exists_exceptional_set_of_no_common_subset
    I (univ : Finset (Fin G.maxDegree)) A (k+2) Q (3*k+1) hQ
      (fun _ _ => subset_univ _) (by simpa only [card_univ,Fintype.card_fin] using hsize) havoid
  refine ⟨X,hXI,?_,?_⟩
  · have he : k+2-1=k+1 := by omega
    simpa only [he] using hX
  · intro η hη
    have hh:=hgood η (by simpa only [I,q,mem_sdiff] using hη)
    simpa only [card_univ,Fintype.card_fin] using hh

/-- Selector-free colour form: the exceptional set works at every actual
endpoint carrying the selected root colour. -/
theorem exceptional_colours (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ) (hk : 1≤k)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (Q : ℕ) (hQ : 1≤Q) (hsize : (3*k+1)*Q*Q≤G.maxDegree) :
    ∃X : Finset (Fin G.maxDegree),
      X⊆paletteS c ((1-ε)*(G.maxDegree:ℝ)) x y∩presentColours c x ∧
      X.card≤(k+1)*(Q+1)^(3*k+1) ∧
      ∀η∈(paletteS c ((1-ε)*(G.maxDegree:ℝ)) x y∩presentColours c x)\X,
        ∀u,c.col x u=some η →
          Q*((badColours c ((1-ε)*(G.maxDegree:ℝ)) u)\{η}).card<G.maxDegree := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  let I:=paletteS c q x y∩presentColours c x
  have hex : ∀η : Fin G.maxDegree,η∈I → ∃u,c.col x u=some η := by
    intro η hη
    exact (presentColours_iff_coloured c x η).mp (mem_inter.mp hη).2
  let U : Fin G.maxDegree → V:=fun η => if hη : η∈I then Classical.choose (hex η hη) else x
  have hU : ∀η∈I,c.col x (U η)=some η := by
    intro η hη
    simpa only [U,dif_pos hη] using Classical.choose_spec (hex η hη)
  obtain ⟨X,hXI,hX,hgood⟩:=exceptional_colours_with_endpoints hG c hcm ε hε hεone k hk
    hx hscale hlarge Q hQ hsize U hU
  refine ⟨X,hXI,hX,?_⟩
  intro η hη u hcol
  have he : U η=u := c.col_proper (hU η (mem_sdiff.mp hη).1) hcol
  simpa only [he] using hgood η hη

/-- The actual-neighbour form used in the high-root R1 estimate.
The omitted root colour costs exactly the displayed additive Q. -/
theorem exceptional_neighbours (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ) (hk : 1≤k)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (Q : ℕ) (hQ : 1≤Q) (hsize : (3*k+1)*Q*Q≤G.maxDegree) :
    ∃E : Finset V,E⊆neighboursS c ((1-ε)*(G.maxDegree:ℝ)) x y ∧
      E.card≤(k+1)*(Q+1)^(3*k+1) ∧
      ∀u∈neighboursS c ((1-ε)*(G.maxDegree:ℝ)) x y\E,
        Q*(badColours c ((1-ε)*(G.maxDegree:ℝ)) u).card<G.maxDegree+Q := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  obtain ⟨X,hXI,hX,hgood⟩:=exceptional_colours hG c hcm ε hε hεone k hk hx hscale hlarge Q hQ hsize
  let E:=(neighboursS c q x y).filter fun u => ∃η∈X,c.col x u=some η
  have hE : E⊆neighboursS c q x y:=filter_subset _ _
  have hcard : E.card=X.card := by
    apply CaoChenPaletteCounting.card_leaves_eq_card_colours x E X
    · intro u hu
      exact (mem_filter.mp hu).2
    · intro η hη
      obtain ⟨u,hcol⟩:=(presentColours_iff_coloured c x η).mp (mem_inter.mp (hXI hη)).2
      have hu : u∈neighboursS c q x y := mem_filter.mpr
        ⟨(mem_neighborFinset G x u).mpr (c.col_adj hcol),η,(mem_inter.mp (hXI hη)).1,hcol⟩
      exact ⟨u,mem_filter.mpr ⟨hu,η,hη,hcol⟩,hcol⟩
  refine ⟨E,hE,hcard.le.trans hX,?_⟩
  intro u hu
  obtain ⟨huS,huE⟩:=mem_sdiff.mp hu
  obtain ⟨_,η,hηS,hcol⟩:=mem_filter.mp huS
  have hηI : η∈paletteS c q x y∩presentColours c x :=
    mem_inter.mpr ⟨hηS,(presentColours_iff_coloured c x η).mpr ⟨u,hcol⟩⟩
  have hηX : η∉X := fun h => huE (mem_filter.mpr ⟨huS,η,h,hcol⟩)
  have hh:=hgood η (mem_sdiff.mpr ⟨hηI,hηX⟩) u hcol
  have hc : (badColours c q u).card≤((badColours c q u)\{η}).card+1 := by
    simpa only [card_singleton] using
      (card_le_card_sdiff_add_card (s:=badColours c q u) (t:={η}))
  have hm:=Nat.mul_le_mul_left Q hc
  change Q*(badColours c q u).card<G.maxDegree+Q
  nlinarith only [hh,hm]

end OverfullWork.CaoChenCorollary10
