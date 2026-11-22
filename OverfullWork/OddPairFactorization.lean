module

public import OverfullWork.PairIdentificationControl
public import OverfullWork.LinearFactorization
public import OverfullWork.OddTwoExceptionDegreeSum

@[expose] public section


/-! A genuine factorization transfer after identifying two nonadjacent
exceptional vertices of an odd-order simple graph. The degree-sum
hypothesis is explicit here; it will be discharged by the odd cut budget.
No overfull-preservation assertion about arbitrary identifications is used.
-/
namespace OverfullWork.PairIdentification
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem colourable_of_two_exception_degree_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (huv : u≠v)
    (hnon : ¬G.Adj u v) (C m : ℕ) (hC : 4000≤C)
    (hsize : Gate8J2I.linearHalfBound C 2≤m)
    (hcard : Fintype.card V=2*m+1)
    (hsum : G.degree u+G.degree v=G.maxDegree)
    (hother : ∀w,w≠u→w≠v→G.degree w=G.maxDegree)
    (hdense : (C+64)*m≤C*G.maxDegree) : G.EdgeColorable G.maxDegree := by
  let M:=graph G u v huv hnon
  let x:=centre u v huv
  have htarget : Fintype.card (Vertices v)=2*m := by
    have hh:=card_vertices v
    omega
  have hm : 1≤m := by
    have hCp : 0<C := by omega
    have hh : 0<Gate8J2I.linearHalfBound C 2 := by
      unfold Gate8J2I.linearHalfBound
      positivity
    omega
  have : Nontrivial (Vertices v):=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨y,hy⟩:=exists_ne x
  have hreg : M.IsRegularOfDegree G.maxDegree := by
    intro w
    by_cases hw : w.val=u
    · have he : w=centre u v huv:=Subtype.ext hw
      dsimp [M]
      rw [he,degree_centre,hsum]
    · dsimp [M]
      rw [degree_other G u v huv hnon w hw,hother w.val hw w.property]
  have hmu : ∀e,M.mult e≤4^1 := fun e => (multiplicity_le_two G u v huv hnon e).trans (by norm_num)
  have : Nonempty V:=⟨u⟩
  have hD : G.maxDegree≤2*m := by
    have hh:=G.maxDegree_lt_card_verts
    omega
  obtain ⟨F,_⟩:=Gate8J2I.linear_centre_factorization M x y (Ne.symm hy)
    C 2 1 2 m G.maxDegree hC (by omega) (by norm_num) (by norm_num)
    (by omega) hsize htarget hreg hmu (parallelBudget G u v huv hnon)
    (centreControl G u v huv hnon) hD hdense
  exact colourable_of_identification G u v huv hnon F

/-- The no-overfull hypothesis supplies the exact regularity equation.
This endpoint has no bound on the original minimum degree. -/
theorem two_exception_criterion
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (huv : u≠v)
    (hnon : ¬G.Adj u v) (C m : ℕ) (hC : 4000≤C)
    (hsize : Gate8J2I.linearHalfBound C 2≤m)
    (hcard : Fintype.card V=2*m+1)
    (hother : ∀w,w≠u→w≠v→G.degree w=G.maxDegree)
    (hdense : (C+64)*m≤C*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph := by
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  have hodd : Odd (Fintype.card V):=⟨m,by omega⟩
  exact colourable_of_two_exception_degree_sum G u v huv hnon C m hC hsize hcard
    (OddTwoExceptionDegreeSum.degree_sum_eq_maxDegree G hodd hno u v huv hnon hother)
    hother hdense

end OverfullWork.PairIdentification

namespace OverfullWork.PairIdentification
open SimpleGraph
open scoped Classical
universe u

/-- Uniform above-half criterion for the odd-order two-exception branch.
The order threshold is chosen before the graph and the two vertices. -/
theorem above_half_two_exceptions (ε : ℝ) (hε : 0<ε) :
    ∃N : ℕ,∀{W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      N≤Fintype.card W → Odd (Fintype.card W) →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      ∀u v,u≠v → ¬G.Adj u v →
      (∀w,w≠u→w≠v→G.degree w=G.maxDegree) →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  obtain ⟨q,hq⟩:=exists_nat_gt ((32:ℝ)/ε)
  let C:=max 4000 q
  have hC : 4000≤C:=le_max_left _ _
  have hCp : 0<C := by omega
  have hqC : (q:ℝ)≤(C:ℝ) := by exact_mod_cast (le_max_right 4000 q)
  have hεC : (32:ℝ)≤ε*(C:ℝ) := by
    have hh:=(div_lt_iff₀ hε).mp hq
    nlinarith
  refine ⟨2*Gate8J2I.linearHalfBound C 2+1,?_⟩
  intro W _ _ G _ hsize hodd hdense u v huv hnon hother
  obtain ⟨m,hm⟩:=hodd
  have hcard : Fintype.card W=2*m+1 := by omega
  have hmsize : Gate8J2I.linearHalfBound C 2≤m := by omega
  have hden : (C+64)*m≤C*G.maxDegree := by
    have hh:=mul_le_mul_of_nonneg_left hdense (Nat.cast_nonneg C (α:=ℝ))
    have he:=mul_le_mul_of_nonneg_right hεC (Nat.cast_nonneg m (α:=ℝ))
    rw [hcard] at hh
    have hr : (((C+64)*m:ℕ):ℝ)≤((C*G.maxDegree:ℕ):ℝ) := by
      push_cast at *
      nlinarith only [hh,he,hεC,Nat.cast_nonneg C (α:=ℝ)]
    exact_mod_cast hr
  exact two_exception_criterion G u v huv hnon C m hC hmsize hcard hother hden

end OverfullWork.PairIdentification
