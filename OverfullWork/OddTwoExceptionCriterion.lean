module

public import OverfullWork.OddPairFactorization

@[expose] public section


/-! # Odd-order criterion with at most two degree exceptions

Nonadjacency is deduced from the two odd-set budgets, so it is not a
hypothesis of these endpoints. The finite criterion retains the actual
engine thresholds.
-/
namespace OverfullWork.PairIdentification
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two exceptional vertices need not be assumed nonadjacent. -/
theorem two_exception_criterion_without_nonadjacency
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (huv : u≠v)
    (C m : ℕ) (hC : 4000≤C)
    (hsize : Gate8J2I.linearHalfBound C 2≤m)
    (hcard : Fintype.card V=2*m+1)
    (hother : ∀w,w≠u→w≠v→G.degree w=G.maxDegree)
    (hdense : (C+64)*m≤C*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph := by
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  have hodd : Odd (Fintype.card V):=⟨m,by omega⟩
  have hnon:=OddTwoExceptionDegreeSum.nonadjacent_of_two_exceptions G hodd hno u v huv hother
  exact (two_exception_criterion G u v huv hnon C m hC hsize hcard hother hdense).mpr hno

/-- Enlarge the exceptional set to a pair when necessary. -/
theorem exists_pair_covering_degree_exceptions
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 2≤Fintype.card V)
    (hlow : (univ.filter fun w=>G.degree w<G.maxDegree).card≤2) :
    ∃u v,u≠v ∧ ∀w,w≠u→w≠v→G.degree w=G.maxDegree := by
  obtain ⟨T,hT,hcard⟩:=exists_superset_card_eq hlow hn
  obtain ⟨u,v,huv,hpair⟩:=card_eq_two.mp hcard
  refine ⟨u,v,huv,?_⟩
  intro w hwu hwv
  have hh:=G.degree_le_maxDegree w
  by_contra he
  have hw : w∈univ.filter fun w=>G.degree w<G.maxDegree :=
    mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hm:=hT hw
  rw [hpair] at hm
  simp only [mem_insert,mem_singleton] at hm
  tauto

/-- A cardinal bound on the set of nonmaximum vertices suffices. -/
theorem at_most_two_degree_exceptions_criterion
    (G : SimpleGraph V) [DecidableRel G.Adj] (C m : ℕ) (hC : 4000≤C)
    (hsize : Gate8J2I.linearHalfBound C 2≤m)
    (hcard : Fintype.card V=2*m+1)
    (hlow : (univ.filter fun w=>G.degree w<G.maxDegree).card≤2)
    (hdense : (C+64)*m≤C*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph := by
  have hCp : 0<C := by omega
  have hp : 0<Gate8J2I.linearHalfBound C 2 := by
    unfold Gate8J2I.linearHalfBound
    positivity
  obtain ⟨u,v,huv,hother⟩:=exists_pair_covering_degree_exceptions G (by omega) hlow
  exact two_exception_criterion_without_nonadjacency G u v huv C m hC hsize hcard hother hdense

universe u
/-- The order threshold is uniform over graphs and the exceptional pair. -/
theorem above_half_two_exceptions_without_nonadjacency (ε : ℝ) (hε : 0<ε) :
    ∃N : ℕ,∀{W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      N≤Fintype.card W → Odd (Fintype.card W) →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      ∀u v,u≠v → (∀w,w≠u→w≠v→G.degree w=G.maxDegree) →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  obtain ⟨N,hN⟩:=above_half_two_exceptions.{u} ε hε
  refine ⟨N,?_⟩
  intro W _ _ G _ hn hodd hdense u v huv hother
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  have hnon:=OddTwoExceptionDegreeSum.nonadjacent_of_two_exceptions G hodd hno u v huv hother
  exact (hN G hn hodd hdense u v huv hnon hother).mpr hno

/-- A uniform asymptotic interface expressed solely by the number of
nonmaximum vertices. -/
theorem above_half_at_most_two_degree_exceptions (ε : ℝ) (hε : 0<ε) :
    ∃N : ℕ,∀{W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      N≤Fintype.card W → Odd (Fintype.card W) →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      (univ.filter fun w=>G.degree w<G.maxDegree).card≤2 →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  obtain ⟨N,hN⟩:=above_half_two_exceptions_without_nonadjacency.{u} ε hε
  refine ⟨max N 2,?_⟩
  intro W _ _ G _ hn hodd hdense hlow
  have hsize : N≤Fintype.card W := (le_max_left N 2).trans hn
  have htwo : 2≤Fintype.card W := (le_max_right N 2).trans hn
  obtain ⟨u,v,huv,hother⟩:=exists_pair_covering_degree_exceptions G htwo hlow
  exact hN G hsize hodd hdense u v huv hother

end OverfullWork.PairIdentification
