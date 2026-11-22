module

public import OverfullWork.CaoChenGeneralPaletteSpine

@[expose] public section


/-! # A forced Kempe link at a low coloured neighbour

A common missing colour outside the swapped pair forces a link through a
prescribed incident colour. Otherwise a Kempe swap would turn the neighbour
into a direct fan leaf while leaving that common missing colour. The degree-sum
version constructs such a colour for EVERY colour missing at the root,
using the extra missing colour at the uncoloured-edge endpoint.

This is a structural constraint on the unresolved double-maximum case.
It does not exclude that whole configuration or prove the R1 estimate.
-/
namespace OverfullWork.CaoChenBadColourLinkage
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000

/-- A common missing colour outside the pair survives a root-avoiding swap.
The resulting direct fan would not be elementary, so the link is forced. -/
theorem linked_of_common_missing_outside_swap (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y v : V} {β δ η : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hyv : c.col y v=some β)
    (hδx : c.IsFree x δ)
    (hηx : c.IsFree x η) (hηv : c.IsFree v η) (hηδ : η≠δ) :
    (c.kempeGraph δ β).Reachable x v := by
  have hxv : x≠v := by
    intro he
    subst v
    have hyx : c.col y x=none := by rw [c.col_symm];exact hcm.uncol
    rw [hyx] at hyv
    contradiction
  have hηβ : η≠β := by
    intro he
    exact hηv y (by rw [c.col_symm,hyv,he])
  by_contra hn
  have hoff : ¬(c.kempeGraph δ β).Reachable v x := fun h => hn h.symm
  let c' := c.kempeSwap δ β v
  have hcm' : IsColMinus c' x y := hcm.kempeSwap δ β v
  have hreach : (c.kempeGraph δ β).Reachable v y :=
    (kempeGraph_adj_of_col (Or.inr (show c.col v y=some β by rw [c.col_symm];exact hyv))).reachable
  have hyv' : c'.col y v=some δ := by
    rw [kempeSwap_col,kempeSwapFun_of_reachable c δ β hreach v,hyv]
    simp only [Option.map_some,Equiv.swap_apply_right]
  have hδx' : c'.IsFree x δ :=
    (isFree_kempeSwap_of_not_reachable c δ β hoff δ).mpr hδx
  have hηx' : c'.IsFree x η :=
    (isFree_kempeSwap_of_not_reachable c δ β hoff η).mpr hηx
  have hηv' : c'.IsFree v η :=
    (kempeSwap_isFree_of_ne c δ β v v hηδ hηβ).mpr hηv
  exact (fan_bau hG hcm' hyv' hδx' hxv).1 η hηx' hηv'

/-- A genuinely low degree sum forces the link for every delta missing
at x, including the boundary case degree(x)+degree(v)=Delta-1. Delta
need not be missing at v. -/
theorem linked_of_small_degree_sum (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y v : V} {β δ : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hyv : c.col y v=some β)
    (hsmall : G.degree x+G.degree v<G.maxDegree)
    (hδx : c.IsFree x δ) :
    (c.kempeGraph δ β).Reachable x v := by
  have hxv : x≠v := by
    intro he
    subst v
    have hyx : c.col y x=none := by rw [c.col_symm];exact hcm.uncol
    rw [hyx] at hyv
    contradiction
  have hbudget : (∑w∈({x,v}:Finset V),G.degree w)+({δ}:Finset (Fin G.maxDegree)).card≤G.maxDegree := by
    simpa only [sum_pair hxv,card_singleton] using (show G.degree x+G.degree v+1≤G.maxDegree by omega)
  obtain ⟨η,hη,hfree⟩ := CommonMissingColour.exists_common_free_outside_of_colMinus_budget
    hcm {x,v} {δ} (by simp) hbudget
  exact linked_of_common_missing_outside_swap hG hcm hyv hδx
    (hfree x (by simp)) (hfree v (by simp)) (by simpa only [mem_singleton] using hη)

end OverfullWork.CaoChenBadColourLinkage
