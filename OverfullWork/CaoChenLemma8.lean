module

public import OverfullWork.CaoChenLemma8Preparation
public import OverfullWork.CaoChenLemma8Rerooting

@[expose] public section


/-! # Cao--Chen Lemma 8 with a uniform explicit cutoff

A large common bad palette is normalized and one selected colour is made
missing at the other endpoint. The actual hole shift then contradicts the
proved Lemma 7. Neither the missing colour nor the shifted colouring is
assumed as an input.
-/
namespace OverfullWork.CaoChenLemma8
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenUniformPaletteBudgets
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- The full selected-family form of Lemma 8. -/
theorem no_configuration (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ) (hk : 1≤k)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (S : Finset (Fin G.maxDegree)) (U : Fin G.maxDegree → V) (F : Finset (Fin G.maxDegree))
    (hScard : S.card=k+2)
    (hS : S⊆paletteS c ((1-ε)*(G.maxDegree:ℝ)) x y∩presentColours c x)
    (hU : ∀ξ∈S,c.col x (U ξ)=some ξ) (hFcard : F.card=3*k+1)
    (hCommon : ∀ξ∈S,F⊆badColours c ((1-ε)*(G.maxDegree:ℝ)) (U ξ)\{ξ}) : False := by
  obtain ⟨d,η,F',hp⟩:=CaoChenLemma8Preparation.exists_missing_right_preparation
    hG c hcm ε hε hεone k hx hscale hlarge S U F hScard hU hS hFcard hCommon
  exact CaoChenLemma8Rerooting.no_large_common_palette_with_missing_right
    hG d hp.cm ε hε hεone k hk hx hscale hlarge S U F' hScard hp.spines
    hp.roles hp.commonCard hp.commonBad ⟨η,hp.candidate,hp.candidateMissing⟩

/-- The common bad palette uses actual coloured root edges, without an
assumed selector for the corresponding neighbours. -/
noncomputable def commonBadColours (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x : V) (S : Finset (Fin G.maxDegree)) : Finset (Fin G.maxDegree) :=
  univ.filter fun γ => ∀ξ∈S,∀u,c.col x u=some ξ → γ∈badColours c q u\{ξ}

/-- At most 3k bad colours are shared by any k+2 selected S-spines.
All endpoints and the common subset are constructed in the proof. -/
theorem commonBadColours_card_le (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ) (hk : 1≤k)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (S : Finset (Fin G.maxDegree)) (hScard : S.card=k+2)
    (hS : S⊆paletteS c ((1-ε)*(G.maxDegree:ℝ)) x y∩presentColours c x) :
    (commonBadColours c ((1-ε)*(G.maxDegree:ℝ)) x S).card≤3*k := by
  by_contra hn
  obtain ⟨F,hFsub,hFcard⟩:=exists_subset_card_eq
    (show 3*k+1≤(commonBadColours c ((1-ε)*(G.maxDegree:ℝ)) x S).card by omega)
  have hex (ξ : Fin G.maxDegree) (hξ : ξ∈S) : ∃u,c.col x u=some ξ :=
    (presentColours_iff_coloured c x ξ).mp (mem_inter.mp (hS hξ)).2
  let U : Fin G.maxDegree → V:=fun ξ => if hξ : ξ∈S then Classical.choose (hex ξ hξ) else x
  have hU : ∀ξ∈S,c.col x (U ξ)=some ξ := by
    intro ξ hξ
    simpa only [U,dif_pos hξ] using Classical.choose_spec (hex ξ hξ)
  apply no_configuration hG c hcm ε hε hεone k hk hx hscale hlarge S U F hScard hS hU hFcard
  intro ξ hξ γ hγ
  exact (mem_filter.mp (hFsub hγ)).2 ξ hξ (U ξ) (hU ξ hξ)

end OverfullWork.CaoChenLemma8
