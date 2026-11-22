module

public import OverfullWork.HeavyPairPeeling

@[expose] public section


/-! # Extend an actual subtype multigraph colouring by isolated vertices -/
namespace OverfullWork.SubtypeColouringExtension
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

def pairMult (S : Finset V) (N : MultiGraph ↥S) (x y : V) : ℕ :=
  if hx : x ∈ S then if hy : y ∈ S then N.mult s(⟨x,hx⟩,⟨y,hy⟩) else 0 else 0

theorem pairMult_symm (S : Finset V) (N : MultiGraph ↥S) (x y : V) :
    pairMult S N x y = pairMult S N y x := by
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [pairMult,hx,hy,Sym2.eq_swap]

def extend (S : Finset V) (N : MultiGraph ↥S) : MultiGraph V where
  mult := Sym2.lift ⟨pairMult S N, pairMult_symm S N⟩
  loopless t ht := by
    induction t using Sym2.inductionOn with
    | hf x y =>
      have hxy := Sym2.mk_isDiag_iff.mp ht
      subst y
      by_cases hx : x ∈ S
      · change pairMult S N x x = 0
        simp only [pairMult, dif_pos hx]
        exact N.loopless _ (Sym2.mk_isDiag_iff.mpr rfl)
      · exact (show pairMult S N x x = 0 from by simp [pairMult,hx])

theorem extend_mult (S : Finset V) (N : MultiGraph ↥S) (x y : S) :
    (extend S N).mult s(x.val,y.val) = N.mult s(x,y) := by
  change pairMult S N x.val y.val = _
  simp [pairMult,x.property,y.property]

theorem extend_mult_outside (S : Finset V) (N : MultiGraph ↥S)
    (x y : V) (hx : x ∉ S) : (extend S N).mult s(x,y) = 0 := by
  change pairMult S N x y = _
  simp [pairMult,hx]

theorem extend_degree (S : Finset V) (N : MultiGraph ↥S) (x : S) :
    (extend S N).degree x.val = N.degree x := by
  rw [MultiGraph.degree_eq_sum_mult, MultiGraph.degree_eq_sum_mult]
  calc
    _ = ∑ y ∈ S, (extend S N).mult s(x.val,y) := by
      symm
      apply sum_subset (subset_univ _)
      intro y _ hy
      rw [show s(x.val,y) = s(y,x.val) from Sym2.eq_swap]
      exact extend_mult_outside S N y x.val hy
    _ = ∑ y : S, (extend S N).mult s(x.val,y.val) := (sum_coe_sort S _).symm
    _ = _ := sum_congr rfl (fun y _ => extend_mult S N x y)

theorem extend_degree_outside (S : Finset V) (N : MultiGraph ↥S)
    (x : V) (hx : x ∉ S) : (extend S N).degree x = 0 := by
  rw [MultiGraph.degree_eq_sum_mult]
  exact sum_eq_zero (fun y _ => extend_mult_outside S N x y hx)

def extend_colouring (S : Finset V) (N : MultiGraph ↥S) {k : ℕ}
    (C : N.EdgeColoring k) : (extend S N).EdgeColoring k where
  col t i := (extend S (C.colourGraph i)).mult t
  sum_col t := by
    induction t using Sym2.inductionOn with
    | hf x y =>
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
      · change (∑ i, pairMult S (C.colourGraph i) x y) = pairMult S N x y
        simp only [pairMult, dif_pos hx, dif_pos hy, MultiGraph.EdgeColoring.colourGraph]
        exact C.sum_col _
      all_goals simp [extend, pairMult, hx, hy]
  proper x i := by
    change (extend S (C.colourGraph i)).degree x ≤ 1
    by_cases hx : x ∈ S
    · rw [extend_degree S (C.colourGraph i) ⟨x,hx⟩]
      exact C.colourGraph_degree_le_one i _
    · rw [extend_degree_outside S (C.colourGraph i) x hx]
      omega

theorem extend_ordinary (R : MultiGraph V) (a b : V) :
    extend (HeavyPairBoundary.outside a b) (HeavyPairPeeling.ordinary R a b) =
      R.restrict (HeavyPairBoundary.outside a b) := by
  apply MultiGraph.ext_mult
  intro t
  induction t using Sym2.inductionOn with
  | hf x y =>
    by_cases hx : x ∈ HeavyPairBoundary.outside a b <;>
      by_cases hy : y ∈ HeavyPairBoundary.outside a b <;>
      simp [extend,pairMult,MultiGraph.restrict,Sym2.toFinset_mk_eq,
        insert_subset_iff,singleton_subset_iff,hx,hy,
        HeavyPairPeeling.ordinary_mult]

end OverfullWork.SubtypeColouringExtension
