module

public import OverfullWork.Gate8F3
public import OverfullWork.Gate8F1

@[expose] public section


/-! # Unconditional large dense degree-gap-three Overfull criteria

The former multiplicity-four factorization premise is now discharged by
the constructed seed, both completion phases and bipartite factorization.
-/
namespace OverfullWork.Gate8F4
open SimpleGraph
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem four_factorization_at (m D : ℕ) (hm : 1000000000000000≤m)
    (hD : D≤2*m) (hdense : 12*m≤7*D) : Gate8F1.FourFactorizationAt.{u} m D := by
  intro W _ _ M x hcard hreg hmu hbudget
  haveI : Nontrivial W:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨y,hy⟩:=exists_ne x
  obtain ⟨C,_⟩:=Gate8F3.dense_regular_four_factorization M x y hy.symm m D hm hcard
    hreg hmu hbudget hD hdense
  exact ⟨C⟩

theorem even_colourable_of_no_overfull (m : ℕ) (hm : 1000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V=2*m) (hgap : G.maxDegree-G.minDegree≤3)
    (hno : ¬G.HasOverfullSubgraph) (hdense : 6*Fintype.card V≤7*G.maxDegree) :
    G.EdgeColorable G.maxDegree := by
  haveI : Nonempty V:=Fintype.card_pos_iff.mp (show 0<Fintype.card V by omega)
  have hD : G.maxDegree≤2*m:=by have hh:=G.maxDegree_lt_card_verts;omega
  exact Gate8F1.even_colourable_of_four_factorization G m (by omega) hcard hgap hno
    (four_factorization_at m G.maxDegree hm hD (by omega))

theorem odd_colourable_of_edge_bound (m : ℕ) (hm : 1000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤3)
    (hedge : 2*G.edgeFinset.card≤G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) : G.EdgeColorable G.maxDegree := by
  obtain ⟨y⟩:=Fintype.card_pos_iff.mp (show 0<Fintype.card V by omega)
  haveI : Nonempty V:=⟨y⟩
  have hD : G.maxDegree≤2*m:=by have hh:=G.maxDegree_lt_card_verts;omega
  obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=GeneralRegularization.exists_odd_bounded_extension
    G m 3 (by omega) hcard hedge hgap
  have hc : Fintype.card (Option V)=2*m:=by simpa using hcard
  obtain ⟨C,_⟩:=Gate8F3.dense_regular_four_factorization M none (some y) (by simp) m
    G.maxDegree hm hc hreg hmu hbudget hD (by omega)
  exact MultigraphExtension.edgeColourable_of_regularized_colouring G M C hcontains

theorem odd_colourable_of_no_overfull (m : ℕ) (hm : 1000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤3)
    (hno : ¬G.HasOverfullSubgraph) (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) :
    G.EdgeColorable G.maxDegree := by
  have hn : Odd (Fintype.card V):=⟨m-1,by omega⟩
  exact odd_colourable_of_edge_bound m hm G hcard hgap
    (DegreeBudget.edge_bound_of_no_overfull G hn hno) hdense

theorem dense_even_gap_three_overfull_criterion (m : ℕ) (hm : 1000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V=2*m) (hgap : G.maxDegree-G.minDegree≤3)
    (hdense : 6*Fintype.card V≤7*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph :=
  ⟨Gate8D.no_overfull_of_colourable G,
    fun hno => even_colourable_of_no_overfull m hm G hcard hgap hno hdense⟩

theorem dense_odd_gap_three_overfull_criterion (m : ℕ) (hm : 1000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤3)
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph :=
  ⟨Gate8D.no_overfull_of_colourable G,
    fun hno => odd_colourable_of_no_overfull m hm G hcard hgap hno hdense⟩

theorem dense_odd_gap_three_edge_criterion (m : ℕ) (hm : 1000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤3)
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ 2*G.edgeFinset.card≤G.maxDegree*(Fintype.card V-1) := by
  constructor
  · intro hc
    exact DegreeBudget.edge_bound_of_no_overfull G (show Odd (Fintype.card V) from ⟨m-1,by omega⟩)
      (Gate8D.no_overfull_of_colourable G hc)
  · exact fun he => odd_colourable_of_edge_bound m hm G hcard hgap he hdense

/-- A common statement for both parities; the even-only result above
has the slightly weaker density premise 6*n<=7*Delta. -/
theorem dense_gap_three_overfull_criterion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsize : 2000000000000000≤Fintype.card V) (hgap : G.maxDegree-G.minDegree≤3)
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph := by
  rcases Nat.even_or_odd (Fintype.card V) with he|ho
  · obtain ⟨m,hmc⟩:=he
    exact dense_even_gap_three_overfull_criterion m (by omega) G (by omega) hgap (by omega)
  · obtain ⟨k,hkc⟩:=ho
    exact dense_odd_gap_three_overfull_criterion (k+1) (by omega) G (by omega) hgap hdense

theorem eventually_dense_gap_three :
    ∃ n₀ : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      n₀≤Fintype.card W → G.maxDegree-G.minDegree≤3 →
      6*(Fintype.card W+1)≤7*G.maxDegree →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  refine ⟨2000000000000000,?_⟩
  intro W _ _ G _ hs hg hd
  exact dense_gap_three_overfull_criterion G hs hg hd

end OverfullWork.Gate8F4
