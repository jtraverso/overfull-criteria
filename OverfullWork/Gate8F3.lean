module

public import OverfullWork.FourDenseInternalCover
public import OverfullWork.Gate8F2

@[expose] public section


/-! # Completed internal covers and factorization for multiplicity four

The seed, both completion phases and bipartite residual are constructed.
No factorization or internal-cover existence is assumed.
-/
namespace OverfullWork.Gate8F3
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_four_regular_internal_cover (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (m D : ℕ) (hm : 1000000000000000≤m) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤4)
    (hbudget : M.HasParallelBudget x 3) (hD : D≤2*m) (hdense : 12*m≤7*D) :
    ∃ (L : Finset V) (H : MultiGraph V) (q : ℕ),
      L.card=m ∧ Lᶜ.card=m ∧ x∈L ∧ y∉L ∧ q<D ∧
      (∀ e,H.mult e≤M.mult e) ∧ H.IsRegularOfDegree q ∧ Nonempty (H.EdgeColoring q) ∧
      ∀ u v,(u∈L ↔ v∈L) → H.mult s(u,v)=M.mult s(u,v) := by
  obtain ⟨t,L,k,C,ht,hsmall,hL,hB,hx,hy,hk,_,_,hv,hc,hinit⟩:=
    Gate8F2.exists_four_initial_state M x y hxy m D hm hcard hreg hmu (by omega) hD
  have hbal : ∀ i,(C.colourGraph i).edgesWithin L=(C.colourGraph i).edgesWithin Lᶜ:=
    hinit.balance
  obtain ⟨H,q,hq,hsub,hH,hcol,hcover⟩:=M.exists_dense_four_internal_cover L x m D t k
    ht hsmall hL hB hx hreg hmu hbudget hdense hk C hbal hv hc
  exact ⟨L,H,q,hL,hB,hx,hy,hq,hsub,hH,hcol,hcover⟩

theorem dense_regular_four_factorization (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (m D : ℕ) (hm : 1000000000000000≤m) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤4)
    (hbudget : M.HasParallelBudget x 3) (hD : D≤2*m) (hdense : 12*m≤7*D) :
    ∃ C : M.EdgeColoring D,C.IsFactorization := by
  obtain ⟨L,H,q,_,_,_,_,hq,hsub,hH,hcol,hcover⟩:=
    exists_four_regular_internal_cover M x y hxy m D hm hcard hreg hmu hbudget hD hdense
  exact MultiGraph.exists_factorization_of_internal_cover M H L D q hq hsub hreg hH hcol hcover

end OverfullWork.Gate8F3
