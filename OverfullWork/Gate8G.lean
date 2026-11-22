module

public import OverfullWork.ExtendedFactorization
public import OverfullWork.Gate8F4

@[expose] public section


/-! # Larger degree gaps, lower density, and an improved previous threshold -/
namespace OverfullWork.Gate8G
open SimpleGraph
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem even_gap_seven_colourable (m : ℕ) (hm : 20000000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V=2*m) (hgap : G.maxDegree-G.minDegree≤7)
    (hno : ¬G.HasOverfullSubgraph) (hdense : 2*Fintype.card V≤3*G.maxDegree) :
    G.EdgeColorable G.maxDegree := by
  haveI : Nontrivial V:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,y,hxy⟩:=exists_pair_ne V
  have hD : G.maxDegree≤2*m:=by have hh:=G.maxDegree_lt_card_verts;omega
  obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=GeneralRegularization.exists_even_bounded_completion
    G m 7 (by omega) hcard hno hgap
  obtain ⟨C,_⟩:=dense_regular_eight_factorization M x y hxy m G.maxDegree hm hcard
    hreg hmu (fun v _ => hbudget v) hD (by omega)
  apply MultiGraph.edgeColourable_of_contained M G _ C
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v => exact hcontains u v ((mem_edgeSet G).mp he)

theorem odd_gap_seven_colourable_of_edge_bound (m : ℕ) (hm : 20000000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤7)
    (hedge : 2*G.edgeFinset.card≤G.maxDegree*(Fintype.card V-1))
    (hdense : 2*(Fintype.card V+1)≤3*G.maxDegree) : G.EdgeColorable G.maxDegree := by
  obtain ⟨y⟩:=Fintype.card_pos_iff.mp (show 0<Fintype.card V by omega)
  haveI : Nonempty V:=⟨y⟩
  have hD : G.maxDegree≤2*m:=by have hh:=G.maxDegree_lt_card_verts;omega
  obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=GeneralRegularization.exists_odd_bounded_extension
    G m 7 (by omega) hcard hedge hgap
  have hc : Fintype.card (Option V)=2*m:=by simpa using hcard
  obtain ⟨C,_⟩:=dense_regular_eight_factorization M none (some y) (by simp) m G.maxDegree hm hc
    hreg hmu hbudget hD (by omega)
  exact MultigraphExtension.edgeColourable_of_regularized_colouring G M C hcontains

theorem dense_even_gap_seven_overfull_criterion (m : ℕ) (hm : 20000000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V=2*m) (hgap : G.maxDegree-G.minDegree≤7)
    (hdense : 2*Fintype.card V≤3*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph :=
  ⟨Gate8D.no_overfull_of_colourable G,
    fun hno => even_gap_seven_colourable m hm G hcard hgap hno hdense⟩

theorem dense_odd_gap_seven_overfull_criterion (m : ℕ) (hm : 20000000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤7)
    (hdense : 2*(Fintype.card V+1)≤3*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph := by
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  have hn : Odd (Fintype.card V):=⟨m-1,by omega⟩
  exact odd_gap_seven_colourable_of_edge_bound m hm G hcard hgap
    (DegreeBudget.edge_bound_of_no_overfull G hn hno) hdense

theorem dense_gap_seven_overfull_criterion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsize : 40000000000000000000≤Fintype.card V) (hgap : G.maxDegree-G.minDegree≤7)
    (hdense : 2*(Fintype.card V+1)≤3*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph := by
  rcases Nat.even_or_odd (Fintype.card V) with he|ho
  · obtain ⟨m,hmc⟩:=he
    exact dense_even_gap_seven_overfull_criterion m (by omega) G (by omega) hgap (by omega)
  · obtain ⟨k,hkc⟩:=ho
    exact dense_odd_gap_seven_overfull_criterion (k+1) (by omega) G (by omega) hgap hdense

theorem eventually_dense_gap_seven :
    ∃ n₀ : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      n₀≤Fintype.card W → G.maxDegree-G.minDegree≤7 →
      2*(Fintype.card W+1)≤3*G.maxDegree →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  refine ⟨40000000000000000000,?_⟩
  intro W _ _ G _ hs hg hd
  exact dense_gap_seven_overfull_criterion G hs hg hd

/-- Improving the previous four-copy threshold is independent of the
larger-order, lower-density eight-copy result. -/
theorem four_factorization_at_improved (m D : ℕ) (hm : 200000000000000≤m)
    (hD : D≤2*m) (hdense : 12*m≤7*D) : Gate8F1.FourFactorizationAt.{u} m D := by
  intro W _ _ M x hcard hreg hmu hbudget
  haveI : Nontrivial W:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨y,hy⟩:=exists_ne x
  obtain ⟨C,_⟩:=dense_regular_four_factorization_improved M x y hy.symm m D hm hcard
    hreg hmu hbudget hD hdense
  exact ⟨C⟩

theorem dense_gap_three_overfull_criterion_improved
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsize : 400000000000000≤Fintype.card V) (hgap : G.maxDegree-G.minDegree≤3)
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph := by
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  haveI : Nonempty V:=Fintype.card_pos_iff.mp (show 0<Fintype.card V by omega)
  have hDup:=G.maxDegree_lt_card_verts
  rcases Nat.even_or_odd (Fintype.card V) with he|ho
  · obtain ⟨m,hmc⟩:=he
    exact Gate8F1.even_colourable_of_four_factorization G m (by omega) (by omega) hgap hno
      (four_factorization_at_improved m G.maxDegree (by omega) (by omega) (by omega))
  · obtain ⟨k,hkc⟩:=ho
    exact Gate8F1.odd_colourable_of_four_factorization G (k+1) (by omega) (by omega) hgap hno
      (four_factorization_at_improved (k+1) G.maxDegree (by omega) (by omega) (by omega))

end OverfullWork.Gate8G
