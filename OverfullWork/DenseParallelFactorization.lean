module

public import OverfullWork.Gate8C3

@[expose] public section


/-! # Dense regular multigraphs with bounded parallel excess off one point -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem dense_regular_parallel_factorization (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (m D : ℕ) (hm : 10000000000000≤m) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤2) (hbudget : M.HasParallelBudget x 3)
    (hD : D≤2*m) (hdense : 12*m≤7*D) :
    ∃ C : M.EdgeColoring D,C.IsFactorization := by
  obtain ⟨r,hr,hrm,hsmall,hsize⟩:=OverfullWork.Gate8C3.explicit_seed_parameters m hm
  let p:=pairEmbedding x y hxy
  have hmuR : ∀ u v,(M.mult s(u,v):ℝ)≤2:=fun u v => by exact_mod_cast hmu s(u,v)
  obtain ⟨L,hL,hB,_,hx,_,hdis⟩:=M.exists_balanced_degree_partition_center m hcard
    (by omega : 1≤m) p 0 2 (by norm_num) hmuR (r:ℝ) (Nat.cast_nonneg _) hsize
  have hp : p (0,true)=x := by
    change (if (true : Bool) then x else y)=x
    simp only [ite_true]
  have hxL : x∈L:=hp ▸ hx
  have hpalette:=palette_size_of_partition_size m D r (by omega) hD hrm hsize
  obtain ⟨k,C,hk,_,hbal,_,hvert,_,hcol⟩:=M.exists_efficient_balanced_internal L m D r hr
    hcard hL hB hreg hmu (by omega) hdis hpalette
  obtain ⟨H,q,hq,hsub,hH,hC,hcover⟩:=M.exists_dense_star_internal_cover L x m D (8*r+10) k
    (by omega) hsmall hL hB hxL hreg hmu hbudget hdense (by omega) C hbal
    (fun v => by have hh:=hvert v;omega) hcol
  exact exists_factorization_of_internal_cover M H L D q hq hsub hreg hH hC hcover

end SimpleGraph.MultiGraph
