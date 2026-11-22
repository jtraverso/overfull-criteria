module

public import OverfullWork.DenseParallelFactorization
public import OverfullWork.GapTwoRegularization

@[expose] public section


/-! # Removing saturation from the dense odd degree-gap-two case

The whole-graph edge inequality replaces equality. Old-vertex additions
are permitted as explicitly controlled parallel copies in the extension.
-/
namespace OverfullWork.Gate8D
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No saturation equality and no overfull-preserving simple completion
are assumed. The regularized multigraph and its colouring are constructed. -/
theorem edgeColourable_of_edge_bound (m : ℕ) (hm : 10000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤2)
    (hedge : 2*G.edgeFinset.card≤G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) : G.EdgeColorable G.maxDegree := by
  have hn : 0<Fintype.card V:=by omega
  obtain ⟨y⟩:=Fintype.card_pos_iff.mp hn
  haveI : Nonempty V:=⟨y⟩
  have hD : 6≤G.maxDegree:=by omega
  obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=MultigraphExtension.exists_bounded_parallel_extension
    G m hcard hgap hedge hD
  have hc : Fintype.card (Option V)=2*m:=by simpa only [Fintype.card_option] using hcard
  have hDupper : G.maxDegree≤2*m:=by have h:=G.maxDegree_lt_card_verts;omega
  obtain ⟨C,_⟩:=M.dense_regular_parallel_factorization none (some y) (by simp) m G.maxDegree hm hc
    hreg hmu hbudget hDupper (by omega)
  exact MultigraphExtension.edgeColourable_of_regularized_colouring G M C hcontains

/-- The whole-graph edge bound is exact in this dense, large odd family. -/
theorem dense_odd_gap_two_criterion (m : ℕ) (hm : 10000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤2)
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ 2*G.edgeFinset.card≤G.maxDegree*(Fintype.card V-1) := by
  constructor
  · intro hc
    classical
    cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
      (fun a b => Classical.propDecidable (G.Adj a b)))
    have hn : Odd (Fintype.card V):=⟨m-1,by omega⟩
    have h:=Plantholt.two_mul_eIn_le_of_colorable (G:=G) hc (S:=univ) (by simpa using hn)
    simpa [Plantholt.eIn_univ] using h
  · exact fun he => edgeColourable_of_edge_bound m hm G hcard hgap he hdense

/-- The Overfull hard direction now holds in the large dense odd
near-regular family without a saturation premise. -/
theorem edgeColourable_of_no_overfull (m : ℕ) (hm : 10000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤2)
    (hno : ¬G.HasOverfullSubgraph)
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) : G.EdgeColorable G.maxDegree := by
  have hn : Odd (Fintype.card V):=⟨m-1,by omega⟩
  exact edgeColourable_of_edge_bound m hm G hcard hgap (DegreeBudget.edge_bound_of_no_overfull G hn hno) hdense

/-- Proper edge colourings exclude every overfull vertex subset. -/
theorem no_overfull_of_colourable (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.EdgeColorable G.maxDegree) : ¬G.HasOverfullSubgraph := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b => Classical.propDecidable (G.Adj a b)))
  rintro ⟨S,hS⟩
  rw [←MultigraphExtension.eIn_eq_edge_filter G S] at hS
  have hdegree : 2*Plantholt.eIn G S≤G.maxDegree*S.card := by
    rw [Plantholt.two_mul_eIn]
    calc
      _ ≤ ∑ v∈S,G.degree v := by
        apply sum_le_sum
        intro v _
        rw [←card_neighborFinset_eq_degree]
        exact card_le_card (filter_subset _ _)
      _ ≤ ∑ _v∈S,G.maxDegree:=sum_le_sum (fun v _ => G.degree_le_maxDegree v)
      _ = _ := by simp [Nat.mul_comm]
  rcases Nat.even_or_odd S.card with he|ho
  · have hh : 2*(S.card/2)=S.card:=by obtain ⟨r,hr⟩:=he;omega
    have hm : G.maxDegree*S.card=2*(G.maxDegree*(S.card/2)) := by
      calc
        _ = G.maxDegree*(2*(S.card/2)):=congrArg (fun n : ℕ => G.maxDegree*n) hh.symm
        _ = _ := by ring
    rw [hm] at hdegree
    omega
  · have hh : 2*(S.card/2)=S.card-1:=by obtain ⟨r,hr⟩:=ho;omega
    have hm : G.maxDegree*(S.card-1)=2*(G.maxDegree*(S.card/2)) := by rw [←hh];ring
    have hb:=Plantholt.two_mul_eIn_le_of_colorable (G:=G) hc ho
    rw [hm] at hb
    omega

/-- Both directions of Overfull hold in the stated dense odd gap-two
family, without saturation and without an auxiliary completion premise. -/
theorem dense_odd_gap_two_overfull_criterion (m : ℕ) (hm : 10000000000000≤m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤2)
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph :=
  ⟨no_overfull_of_colourable G,fun hno => edgeColourable_of_no_overfull m hm G hcard hgap hno hdense⟩

/-- The conditional asymptotic threshold is uniform over all finite
vertex types and graphs, and saturation has been removed. -/
theorem eventually_dense_odd_gap_two :
    ∃ m₀ : ℕ,∀ m : ℕ,m₀≤m → ∀ {W : Type*} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      Fintype.card W+1=2*m → G.maxDegree-G.minDegree≤2 →
      2*G.edgeFinset.card≤G.maxDegree*(Fintype.card W-1) →
      6*(Fintype.card W+1)≤7*G.maxDegree → G.EdgeColorable G.maxDegree := by
  exact ⟨10000000000000,fun m hm _ _ _ G _ hc hg he hd =>
    edgeColourable_of_edge_bound m hm G hc hg he hd⟩

end OverfullWork.Gate8D
