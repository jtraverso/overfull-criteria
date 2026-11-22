module

public import OverfullWork.SeedBudgetThresholds
public import OverfullWork.EightDenseInternalCover
public import OverfullWork.Gate8F3

@[expose] public section


/-! # Lower density at multiplicity eight and an improved four-copy threshold -/
namespace OverfullWork.Gate8G
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem dense_regular_eight_factorization (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (m D : ℕ) (hm : 20000000000000000000≤m) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8)
    (hbudget : M.HasParallelBudget x 7) (hD : D≤2*m) (hdense : 4*m≤3*D) :
    ∃ C : M.EdgeColoring D,C.IsFactorization := by
  obtain ⟨r,hr,hrm,hsmall,hsize⟩:=eight_parameters m hm
  obtain ⟨s,L,k,C,hs,_,hsmall',hL,hB,hx,_,hk,_,_,hbal,_,hv,_,hc⟩:=
    exists_eight_seed_of_parameters M x y hxy m D r hr hrm hsmall hsize hcard hreg hmu (by omega) hD
  let t:=32*s+40
  obtain ⟨H,q,hq,hsub,hH,hcol,hcover⟩:=M.exists_dense_eight_internal_cover L x m D t k
    (by dsimp [t];omega) hsmall' hL hB hx hreg hmu hbudget hdense
    (by dsimp [t];omega) C hbal
    (fun v => by have hh:=hv v;dsimp [t];omega)
    (fun i => by have hh:=hc i;dsimp [t];omega)
  exact MultiGraph.exists_factorization_of_internal_cover M H L D q hq hsub hreg hH hcol hcover

theorem dense_regular_four_factorization_improved (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (m D : ℕ) (hm : 200000000000000≤m) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤4)
    (hbudget : M.HasParallelBudget x 3) (hD : D≤2*m) (hdense : 12*m≤7*D) :
    ∃ C : M.EdgeColoring D,C.IsFactorization := by
  obtain ⟨r,hr,hrm,hsmall,hsize⟩:=four_parameters_improved m hm
  obtain ⟨s,L,k,C,hs,_,hsmall',hL,hB,hx,_,hk,_,_,hbal,_,hv,_,hc⟩:=
    exists_four_seed_of_parameters M x y hxy m D r hr hrm hsmall hsize hcard hreg hmu (by omega) hD
  let t:=16*s+20
  obtain ⟨H,q,hq,hsub,hH,hcol,hcover⟩:=M.exists_dense_four_internal_cover L x m D t k
    (by dsimp [t];omega) hsmall' hL hB hx hreg hmu hbudget hdense
    (by dsimp [t];omega) C hbal
    (fun v => by have hh:=hv v;dsimp [t];omega)
    (fun i => by have hh:=hc i;dsimp [t];omega)
  exact MultiGraph.exists_factorization_of_internal_cover M H L D q hq hsub hreg hH hcol hcover

end OverfullWork.Gate8G
