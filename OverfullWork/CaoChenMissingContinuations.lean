module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import OverfullWork.CommonMissingColour
public import Overfull.Kierstead4
public import Overfull.Degree

@[expose] public section


/-! # The missing-endpoint cases of Cao--Chen Lemma 11

A colour missing at x or y has an actual continuation from x_alpha.
Its endpoint is high by VAL or by the elementary short Kierstead path.
The palette-A case requires additional switching and is not assumed here.
-/
namespace OverfullWork.CaoChenR1Continuation
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000

/-- Disjointness from both endpoint missing sets gives the sharp degree
bound needed for a continuation endpoint. -/
theorem degree_bound_of_no_endpoint_missing (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y z : V} (hcm : IsColMinus c x y)
    (hdis : ∀ θ,InA c x y θ → ¬c.IsFree z θ) :
    G.maxDegree-G.degree x+2≤G.degree z := by
  have hends:=hcm.ab_facts hG
  have hdisjoint : Disjoint (missing c x) (missing c y) := by
    apply Finset.disjoint_left.mpr
    intro θ hx hy
    exact hends.1 θ (mem_missing.mp hx) (mem_missing.mp hy)
  have hsub : missing c x∪missing c y⊆univ\missing c z := by
    intro θ hθ
    refine mem_sdiff.mpr ⟨mem_univ θ,?_⟩
    intro hz
    apply hdis θ ?_ (mem_missing.mp hz)
    rcases mem_union.mp hθ with hx|hy
    · exact Or.inl (mem_missing.mp hx)
    · exact Or.inr (mem_missing.mp hy)
  have hcard:=card_le_card hsub
  rw [card_union_of_disjoint hdisjoint,CommonMissingColour.present_colour_card] at hcard
  have hcol : (colNbrs c z).card≤G.degree z :=
    (card_le_card (filter_subset (fun u => c.col z u≠none) (G.neighborFinset z))).trans_eq
      (card_neighborFinset_eq_degree G z)
  have hx:=hcm.card_missing_end (Or.inl rfl : x=x ∨ x=y)
  obtain ⟨θ,hθ⟩:=hcm.exists_free_right
  have hy : 1≤(missing c y).card := card_pos.mpr ⟨θ,mem_missing.mpr hθ⟩
  have hxmax:=G.degree_le_maxDegree x
  omega

/-- The first A-coloured spine vertex already has high degree by the
three-vertex fan, without any assumption on a continuation. -/
theorem spine_degree_bound (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α) :
    G.maxDegree-G.degree x+2≤G.degree u := by
  have hyu : y≠u := by
    intro he
    subst u
    rw [hcm.uncol] at hxu
    contradiction
  have hfan:=fan_bau hG hcm.symm hxu hα hyu
  apply degree_bound_of_no_endpoint_missing hG hcm
  intro θ hθ
  rcases hθ with hx|hy
  · exact hfan.2 θ hx
  · exact hfan.1 θ hy

/-- Cao--Chen Lemma 11 when beta is missing at either endpoint of the
uncoloured edge. Both existence and the continuation degree are proved. -/
theorem exists_high_continuation_of_missing_colours (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (hβα : β≠α) (hβ : InA c x y β) (hdx : G.degree x<G.maxDegree) :
    ∃ z : V,c.col u z=some β ∧ G.maxDegree-G.degree x+2≤G.degree z := by
  have hyu : y≠u := by
    intro he
    subst u
    rw [hcm.uncol] at hxu
    contradiction
  have hfan:=fan_bau hcrit.2.1 hcm.symm hxu hα hyu
  have hnot : ¬c.IsFree u β := by
    rcases hβ with hx|hy
    · exact hfan.2 β hx
    · exact hfan.1 β hy
  obtain ⟨z,huz⟩ : ∃ z,c.col u z=some β := by
    by_contra hn
    apply hnot
    intro z hz
    exact hn ⟨z,hz⟩
  refine ⟨z,huz,?_⟩
  by_cases hzy : z=y
  · subst z
    have hh:=deg_add hcrit hcm.adj
    have hxmax:=G.degree_le_maxDegree x
    omega
  have hzx : z≠x := by
    intro he
    subst z
    have hh : β=α := Option.some.inj (huz.symm.trans ((c.col_symm u x).trans hxu))
    exact hβα hh
  have hK : IsK4 c y x u z α β :=
    ⟨hcm.symm,hxu,huz,hα,hβ.symm,hyu,Ne.symm hzy,Ne.symm hzx⟩
  apply degree_bound_of_no_endpoint_missing hcrit.2.1 hcm
  intro θ hθ hfree
  exact hK.not_common_of_degree_b hcrit.2.1 hdx hθ.symm hfree

/-- A positive real threshold below Delta−d(x) gives the strict high-degree
conclusion, including q=(1−epsilon)Delta with d(x)≤epsilon Delta. -/
theorem exists_continuation_above_threshold (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some α) (hα : c.IsFree y α)
    (hβα : β≠α) (hβ : InA c x y β) (q : ℝ) (hq : 0<q)
    (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ)) :
    ∃ z : V,c.col u z=some β ∧ G.maxDegree-G.degree x+2≤G.degree z ∧ q<(G.degree z:ℝ) := by
  have hdx : G.degree x<G.maxDegree := by
    exact_mod_cast (show (G.degree x:ℝ)<(G.maxDegree:ℝ) by linarith)
  obtain ⟨z,hcol,hdeg⟩:=exists_high_continuation_of_missing_colours hcrit hcm hxu hα hβα hβ hdx
  have hh : G.maxDegree+2≤G.degree x+G.degree z := by omega
  have hhR : (G.maxDegree:ℝ)+2≤(G.degree x:ℝ)+(G.degree z:ℝ) := by exact_mod_cast hh
  exact ⟨z,hcol,hdeg,by linarith⟩

end OverfullWork.CaoChenR1Continuation
