module

public import OverfullWork.DenseSpanningPaths
public import OverfullWork.PathGraphRealization
public import OverfullWork.RobustExpansionDeletion

@[expose] public section


/-! # Actual simultaneous packing of prescribed dense path covers

Each completed round removes maximum degree at most two. A single
minimum-degree reserve therefore constructs every round successively,
with edge-disjointness between rounds and no path-selection oracle.
The endpoints may be reused in different rounds. This is a dense
restricted case of the configuration machinery, not its robust
below-half version or its general shared-endpoint layout statement.
-/
namespace OverfullWork.DenseBatchPathPacking
open SimpleGraph Finset PathGraphRealization RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

structure Packing (G : SimpleGraph V) (ℓ p : ℕ)
    (a b : Fin ℓ → Fin p → V) where
  paths : ∀j,∀i,G.Walk (a j i) (b j i)
  simple : ∀j i,(paths j i).IsPath
  vertex_disjoint : ∀j i k,i≠k → ∀v,v∈(paths j i).support → v∉(paths j k).support
  spanning : ∀j v,∃i,v∈(paths j i).support
  rounds_disjoint : ∀j k,j≠k → Disjoint (pathUnion (paths j)) (pathUnion (paths k))

def Packing.usedGraph {G : SimpleGraph V} {ℓ p : ℕ} {a b : Fin ℓ → Fin p → V}
    (s : Packing G ℓ p a b) : SimpleGraph V := ⨆j,pathUnion (s.paths j)

theorem degree_iSup_le_sum {I : Type*} [Fintype I] (L : I → SimpleGraph V) (v : V) :
    (⨆i,L i).degree v≤∑i,(L i).degree v := by
  have he : (⨆i,L i).neighborFinset v=univ.biUnion (fun i => (L i).neighborFinset v) := by
    ext w
    simp only [mem_neighborFinset,iSup_adj,mem_biUnion,mem_univ,true_and]
  rw [←card_neighborFinset_eq_degree,he]
  exact card_biUnion_le

theorem Packing.usedGraph_le {G : SimpleGraph V} {ℓ p : ℕ} {a b : Fin ℓ → Fin p → V}
    (s : Packing G ℓ p a b) : s.usedGraph≤G :=
  iSup_le (fun j => pathUnion_le_original (s.paths j))

theorem Packing.usedGraph_degree_le {G : SimpleGraph V} {ℓ p : ℕ}
    {a b : Fin ℓ → Fin p → V} (s : Packing G ℓ p a b) (v : V) :
    s.usedGraph.degree v≤2*ℓ := by
  calc
    _ ≤ ∑j,(pathUnion (s.paths j)).degree v := degree_iSup_le_sum _ v
    _ ≤ ∑_j : Fin ℓ,2 := sum_le_sum (fun j _ =>
      pathUnion_degree_le_two (s.paths j) (s.simple j) (s.vertex_disjoint j) v)
    _ = _ := by simp [Nat.mul_comm]

private theorem exists_paths_positive (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℕ) (hp : 0<p) (a b : Fin p → V)
    (hab : ∀i j,a i≠b j) (ha : Function.Injective a) (hb : Function.Injective b)
    (hmargin : Fintype.card V+6*p+2≤2*G.minDegree) (hsize : 3*p+5≤Fintype.card V) :
    ∃P : ∀i,G.Walk (a i) (b i),(∀i,(P i).IsPath) ∧
      (∀i j,i≠j → ∀v,v∈(P i).support → v∉(P j).support) ∧
      ∀v,∃i,v∈(P i).support := by
  rcases p with _|t
  · omega
  · exact DenseHamilton.exists_paths t G a b hab ha hb hmargin hsize

/-- Construct successive disjoint path covers from a linkage theorem on
the simple residue. The bound on the removed degree is supplied by the
actual preceding rounds. -/
theorem exists_packing_of_residual_linkage (G : SimpleGraph V)
    (ℓ p : ℕ) (a b : Fin ℓ → Fin p → V)
    (hLink : ∀ (Q : SimpleGraph V) (t : ℕ), t < ℓ →
      Q ≤ G → (∀ v, Q.degree v ≤ 2*t) →
      ∀ j : Fin ℓ, ∃ P : ∀ i, (G\Q).Walk (a j i) (b j i),
        (∀ i, (P i).IsPath) ∧
        (∀ i k, i ≠ k → ∀ v, v ∈ (P i).support → v ∉ (P k).support) ∧
        ∀ v, ∃ i, v ∈ (P i).support) :
    Nonempty (Packing G ℓ p a b) := by
  induction ℓ with
  | zero =>
    refine ⟨⟨?_,?_,?_,?_,?_⟩⟩
    all_goals intro j; exact Fin.elim0 j
  | succ ℓ ih =>
    obtain ⟨s⟩ := ih (fun j => a j.succ) (fun j => b j.succ)
      (fun Q t ht hQ hDeg j => hLink Q t (by omega) hQ hDeg j.succ)
    let Q := s.usedGraph
    let R := G\Q
    have hRG : R ≤ G := sdiff_le
    obtain ⟨T,hT,hTd,hTs⟩ := hLink Q ℓ (by omega) s.usedGraph_le s.usedGraph_degree_le 0
    let T' := fun i => (T i).mapLe hRG
    have hT' : ∀i,(T' i).IsPath:=fun i => (hT i).mapLe hRG
    have hT'd : ∀i k,i≠k → ∀v,v∈(T' i).support → v∉(T' k).support := by
      simpa only [T',Walk.support_mapLe_eq_support] using hTd
    have hT's : ∀v,∃i,v∈(T' i).support := by
      simpa only [T',Walk.support_mapLe_eq_support] using hTs
    have hnew : pathUnion T'≤R := by
      intro x y hxy
      obtain ⟨i,hi⟩:=pathUnion_adj_iff T' |>.mp hxy
      have he : (T i).toSubgraph.Adj x y :=
        (Walk.adj_toSubgraph_mapLe hRG).mp hi
      exact (T i).toSubgraph.adj_sub he
    have hcross : ∀j,Disjoint (pathUnion T') (pathUnion (s.paths j)) := by
      intro j
      apply disjoint_iff_inf_le.mpr
      intro x y ⟨hn,ho⟩
      have hnot : ¬Q.Adj x y := (hnew hn).2
      exact (hnot ((le_iSup (fun j => pathUnion (s.paths j)) j) ho)).elim
    let P : ∀j:Fin (ℓ+1),∀i,G.Walk (a j i) (b j i):=
      Fin.cases T' (fun j => s.paths j)
    refine ⟨{paths:=P,simple:=?_,vertex_disjoint:=?_,spanning:=?_,rounds_disjoint:=?_}⟩
    · intro j
      induction j using Fin.cases with
      | zero => exact hT'
      | succ j => exact s.simple j
    · intro j
      induction j using Fin.cases with
      | zero => exact hT'd
      | succ j => exact s.vertex_disjoint j
    · intro j
      induction j using Fin.cases with
      | zero => exact hT's
      | succ j => exact s.spanning j
    · intro j k hjk
      induction j using Fin.cases with
      | zero =>
        induction k using Fin.cases with
        | zero => exact False.elim (hjk rfl)
        | succ k => exact hcross k
      | succ j =>
        induction k using Fin.cases with
        | zero => exact (hcross j).symm
        | succ k => exact s.rounds_disjoint j k (fun he => hjk (congrArg Fin.succ he))

/-- The entire batch is constructed from the displayed degree margin.
Vertex disjointness is within a round; edge disjointness is across rounds. -/
theorem exists_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (ℓ p : ℕ) (hp : 0<p) (a b : Fin ℓ → Fin p → V)
    (hab : ∀j i k,a j i≠b j k)
    (ha : ∀j,Function.Injective (a j)) (hb : ∀j,Function.Injective (b j))
    (hmargin : Fintype.card V+6*p+2+4*ℓ≤2*G.minDegree)
    (hsize : 3*p+5≤Fintype.card V) : Nonempty (Packing G ℓ p a b) := by
  apply exists_packing_of_residual_linkage G ℓ p a b
  intro Q t ht hQ hQdeg j
  let R := G\Q
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hmin : G.minDegree ≤ R.minDegree+2*t := by
    obtain ⟨v,hv⟩ := R.exists_minimal_degree_vertex
    have hs := MaximumMatching.degree_sdiff_add_of_le G Q hQ v
    have hd := G.minDegree_le_degree v
    have hq := hQdeg v
    change R.degree v+Q.degree v=G.degree v at hs
    omega
  exact exists_paths_positive R p hp (a j) (b j) (hab j) (ha j) (hb j)
    (by omega) hsize

/-- Robust expansion survives the constructed batch whenever its
total two-degree deletion budget is smaller than the initial threshold. -/
theorem Packing.robust_remainder {G : SimpleGraph V} [DecidableRel G.Adj]
    {ℓ p : ℕ} {a b : Fin ℓ → Fin p → V} (s : Packing G ℓ p a b)
    (r t : ℕ) (hrobust : IsRobustAt G r t) (hbudget : 2*ℓ<r) :
    0<r-2*ℓ ∧ IsRobustAt (G\s.usedGraph) (r-2*ℓ) t ∧
      ∀S : Finset V,t≤S.card → S.card+t≤Fintype.card V →
        S.card+r≤(neighbourhood (G\s.usedGraph) (r-2*ℓ) S).card := by
  exact ⟨by omega,
    isRobustAt_sdiff G s.usedGraph r (2*ℓ) t hrobust s.usedGraph_degree_le,
    robust_gain_after_deletion G s.usedGraph r (2*ℓ) t hrobust s.usedGraph_degree_le⟩

/-- A simultaneous packing and its robust residue are both outputs.
Initial robustness is an input, but no reserved subgraph or path cover
is assumed. -/
theorem exists_packing_with_robust_remainder (G : SimpleGraph V) [DecidableRel G.Adj]
    (ℓ p : ℕ) (hp : 0<p) (a b : Fin ℓ → Fin p → V)
    (hab : ∀j i k,a j i≠b j k)
    (ha : ∀j,Function.Injective (a j)) (hb : ∀j,Function.Injective (b j))
    (hmargin : Fintype.card V+6*p+2+4*ℓ≤2*G.minDegree)
    (hsize : 3*p+5≤Fintype.card V) (r t : ℕ)
    (hrobust : IsRobustAt G r t) (hbudget : 2*ℓ<r) :
    ∃s : Packing G ℓ p a b,0<r-2*ℓ ∧ IsRobustAt (G\s.usedGraph) (r-2*ℓ) t ∧
      ∀S : Finset V,t≤S.card → S.card+t≤Fintype.card V →
        S.card+r≤(neighbourhood (G\s.usedGraph) (r-2*ℓ) S).card := by
  obtain ⟨s⟩:=exists_packing G ℓ p hp a b hab ha hb hmargin hsize
  exact ⟨s,s.robust_remainder r t hrobust hbudget⟩

end OverfullWork.DenseBatchPathPacking
