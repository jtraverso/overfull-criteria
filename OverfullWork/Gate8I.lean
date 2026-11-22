module

public import OverfullWork.ThreeFifthsCompletion
public import OverfullWork.Gate8G

@[expose] public section


/-! # Three-fifths density for bounded degree gap

The extra centre information is proved from the original simple graph,
then discharged in both parities. It is not a premise of the final criteria.
-/
namespace OverfullWork.Gate8I
open SimpleGraph Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem structured_eight_factorization (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (m D : ℕ) (hm : 20000000000000000000≤m) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8)
    (hbudget : M.HasParallelBudget x 7) (hcontrol : M.CentreControl x 7)
    (hD : D≤2*m) (hdense : 6*m≤5*D) :
    ∃ C : M.EdgeColoring D,C.IsFactorization := by
  obtain ⟨r,hr,hrm,hsmall,hsize⟩:=Gate8G.eight_parameters m hm
  obtain ⟨s,L,k,C,_,_,hsmall',hL,hB,hx,_,hk,_,_,hbal,_,hv,_,hc⟩:=
    Gate8G.exists_eight_seed_of_parameters M x y hxy m D r hr hrm hsmall hsize hcard
      hreg hmu (by omega) hD
  let t:=32*s+40
  obtain ⟨H,q,hq,hsub,hH,hcol,hcover⟩:=M.exists_dense_three_fifths_internal_cover L x m D t k
    (by dsimp [t];omega) hsmall' hL hB hx hreg hmu hbudget hcontrol hdense
    (by dsimp [t];omega) C hbal
    (fun v => by have hh:=hv v;dsimp [t];omega)
    (fun i => by have hh:=hc i;dsimp [t];omega)
  exact MultiGraph.exists_factorization_of_internal_cover M H L D q hq hsub hreg hH hcol hcover

theorem even_gap_seven_colourable (m : ℕ) (hm : 20000000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V=2*m) (hgap : G.maxDegree-G.minDegree≤7)
    (hno : ¬G.HasOverfullSubgraph) (hdense : 3*Fintype.card V≤5*G.maxDegree) :
    G.EdgeColorable G.maxDegree := by
  haveI : Nontrivial V:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,y,hxy⟩:=exists_pair_ne V
  have hD : G.maxDegree≤2*m:=by have hh:=G.maxDegree_lt_card_verts;omega
  obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=GeneralRegularization.exists_even_bounded_completion
    G m 7 (by omega) hcard hno hgap
  obtain ⟨C,_⟩:=structured_eight_factorization M x y hxy m G.maxDegree hm hcard
    hreg hmu (fun v _ => hbudget v) (Or.inr (hbudget x)) hD (by omega)
  apply MultiGraph.edgeColourable_of_contained M G _ C
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b => exact hcontains a b ((mem_edgeSet G).mp he)

theorem odd_gap_seven_colourable_of_edge_bound (m : ℕ) (hm : 20000000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤7)
    (hedge : 2*G.edgeFinset.card≤G.maxDegree*(Fintype.card V-1))
    (hdense : 3*(Fintype.card V+1)≤5*G.maxDegree) : G.EdgeColorable G.maxDegree := by
  obtain ⟨y⟩:=Fintype.card_pos_iff.mp (show 0<Fintype.card V by omega)
  haveI : Nonempty V:=⟨y⟩
  have hD : G.maxDegree≤2*m:=by have hh:=G.maxDegree_lt_card_verts;omega
  obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=GeneralRegularization.exists_odd_bounded_extension
    G m 7 (by omega) hcard hedge hgap
  have hcontrol : M.CentreControl none 7 := by
    apply Or.inl
    intro w
    cases w with
    | none => rw [M.loopless s(none,none) (by simp)];exact Nat.zero_le _
    | some v =>
      have hh:=GeneralRegularization.centre_mult_le_deficit G M G.maxDegree hreg hcontains v
      have hmin:=G.minDegree_le_degree v
      omega
  have hc : Fintype.card (Option V)=2*m:=by simpa using hcard
  obtain ⟨C,_⟩:=structured_eight_factorization M none (some y) (by simp) m G.maxDegree hm hc
    hreg hmu hbudget hcontrol hD (by omega)
  exact MultigraphExtension.edgeColourable_of_regularized_colouring G M C hcontains

theorem dense_even_gap_seven_overfull_criterion (m : ℕ) (hm : 20000000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V=2*m) (hgap : G.maxDegree-G.minDegree≤7)
    (hdense : 3*Fintype.card V≤5*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph :=
  ⟨Gate8D.no_overfull_of_colourable G,
    fun hno => even_gap_seven_colourable m hm G hcard hgap hno hdense⟩

theorem dense_odd_gap_seven_overfull_criterion (m : ℕ) (hm : 20000000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤7)
    (hdense : 3*(Fintype.card V+1)≤5*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph := by
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  have hn : Odd (Fintype.card V):=⟨m-1,by omega⟩
  exact odd_gap_seven_colourable_of_edge_bound m hm G hcard hgap
    (DegreeBudget.edge_bound_of_no_overfull G hn hno) hdense

theorem dense_odd_gap_seven_edge_criterion (m : ℕ) (hm : 20000000000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤7)
    (hdense : 3*(Fintype.card V+1)≤5*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ 2*G.edgeFinset.card≤G.maxDegree*(Fintype.card V-1) := by
  constructor
  · intro hc
    exact DegreeBudget.edge_bound_of_no_overfull G (show Odd (Fintype.card V) from ⟨m-1,by omega⟩)
      (Gate8D.no_overfull_of_colourable G hc)
  · exact fun he => odd_gap_seven_colourable_of_edge_bound m hm G hcard hgap he hdense

theorem dense_gap_seven_overfull_criterion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsize : 40000000000000000000≤Fintype.card V) (hgap : G.maxDegree-G.minDegree≤7)
    (hdense : 3*(Fintype.card V+1)≤5*G.maxDegree) :
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
      3*(Fintype.card W+1)≤5*G.maxDegree →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  refine ⟨40000000000000000000,?_⟩
  intro W _ _ G _ hs hg hd
  exact dense_gap_seven_overfull_criterion G hs hg hd

end OverfullWork.Gate8I
