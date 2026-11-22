module

public import OverfullWork.CriticalReductionStop

@[expose] public section


/-! # An actual bounded run of critical-copy two-colour reductions

Every transition stores the constructed layer and the critical witness
inside its actual residue. The only stopping branch stores an actual odd
overfull set and its tiny star complement. The number of transitions is
limited by the original density margin; no transition oracle or absence
of residual overfull sets is postulated.
-/
namespace OverfullWork.BoundedCriticalReductionRun
open SimpleGraph Finset SparseDeficitCore
open scoped Classical
universe u
set_option maxHeartbeats 5000000

structure CriticalGraph where
  vertices : Type u
  [finiteVertices : Fintype vertices]
  [decidableVertices : DecidableEq vertices]
  graph : SimpleGraph vertices
  [decidableAdjacency : DecidableRel graph.Adj]
  critical : Overfull.IsDeltaCritical graph
  no_overfull : ¬graph.HasOverfullSubgraph

attribute [instance] CriticalGraph.finiteVertices CriticalGraph.decidableVertices
  CriticalGraph.decidableAdjacency

def CriticalGraph.order (C : CriticalGraph.{u}) : ℕ := Fintype.card C.vertices

def ofWitness {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : Critical.CriticalWitness G) :
    CriticalGraph.{u} where
  vertices:=w.vertices
  graph:=w.graph
  critical:=w.critical
  no_overfull:=w.no_overfull

def initial {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (hno : ¬G.HasOverfullSubgraph) :
    CriticalGraph.{u} where
  vertices:=V
  graph:=G
  critical:=hc
  no_overfull:=hno

/-- A step stores actual constructed objects, including the successful
absence-of-overfull test on the actual residue. -/
structure Step (C : CriticalGraph.{u}) where
  reduction : CriticalTwoColourReduction.Reduction C.graph
  residue_no_overfull : ¬(C.graph\reduction.layer).HasOverfullSubgraph
  witness : Critical.CriticalWitness (C.graph\reduction.layer)

noncomputable def Step.target {C : CriticalGraph.{u}} (s : Step C) : CriticalGraph.{u} :=
  ofWitness s.witness

theorem Step.degree_eq {C : CriticalGraph.{u}} (s : Step C) :
    s.target.graph.maxDegree=C.graph.maxDegree-2 :=
  s.witness.maxDegree_eq.trans s.reduction.residual_maxDegree

theorem Step.order_le {C : CriticalGraph.{u}} (s : Step C) : s.target.order≤C.order :=
  s.witness.order_le

theorem critical_degree_two_le (C : CriticalGraph.{u}) : 2≤C.graph.maxDegree := by
  obtain ⟨v⟩:=C.critical.1.nonempty
  exact (OddLowSmallCases.critical_two_le_degree C.graph C.critical v).trans
    (C.graph.degree_le_maxDegree v)

theorem Step.degree_add_two {C : CriticalGraph.{u}} (s : Step C) :
    s.target.graph.maxDegree+2=C.graph.maxDegree := by
  rw [s.degree_eq]
  have hh:=critical_degree_two_le C
  omega

/-- Each constructor contains an actual layer and an actual extracted
critical witness on its own effective vertex type. -/
inductive Run : CriticalGraph.{u} → CriticalGraph.{u} → ℕ → Type (u+1)
  | nil (C : CriticalGraph.{u}) : Run C C 0
  | snoc {B C : CriticalGraph.{u}} {j : ℕ} (p : Run B C j) (s : Step C) :
      Run B s.target (j+1)

theorem Run.order_le {B C : CriticalGraph.{u}} {j : ℕ} (p : Run B C j) : C.order≤B.order := by
  induction p with
  | nil => exact le_rfl
  | snoc p s ih => exact s.order_le.trans ih

theorem Run.degree_exact {B C : CriticalGraph.{u}} {j : ℕ} (p : Run B C j) :
    C.graph.maxDegree+2*j=B.graph.maxDegree := by
  induction p with
  | nil => omega
  | snoc p s ih => have hh:=s.degree_add_two;omega

/-- A stop retains its actual layer and actual odd overfull witness. -/
structure Stop (q : ℕ) (C : CriticalGraph.{u}) where
  reduction : CriticalTwoColourReduction.Reduction C.graph
  set : Finset C.vertices
  geometry : CriticalReductionStop.IsStoppingSet C.graph reduction.layer
    (exceptions C.graph C.graph.maxDegree (C.order/(8*q)))
    (C.order/(4096*q^2)) set

/-- The two elementary invariants give the fixed density margin needed
at every stage. The threshold is checked on the actual critical copy. -/
theorem run_margins (ε : ℝ) (hε : 0<ε) (N m : ℕ)
    {B C : CriticalGraph.{u}} {j : ℕ} (p : Run B C j)
    (hn : 2*N+2≤B.order)
    (hdense : ((1:ℝ)/2+ε)*(B.order:ℝ)≤(B.graph.maxDegree:ℝ))
    (hbudget : 4*(m:ℝ)≤ε*(B.order:ℝ)) (hj : j≤m) :
    N≤C.order ∧ ((1:ℝ)/2+ε/2)*(C.order:ℝ)≤(C.graph.maxDegree:ℝ) := by
  have heq:=p.degree_exact
  have heqR : (C.graph.maxDegree:ℝ)+2*(j:ℝ)=(B.graph.maxDegree:ℝ) := by
    exact_mod_cast heq
  have hjR : (j:ℝ)≤(m:ℝ) := by exact_mod_cast hj
  have habsolute : ((1:ℝ)/2+ε/2)*(B.order:ℝ)≤(C.graph.maxDegree:ℝ) := by
    nlinarith only [hdense,hbudget,hjR,heqR]
  have hoR : (C.order:ℝ)≤(B.order:ℝ) := by exact_mod_cast p.order_le
  have hnR : 2*(N:ℝ)+2≤(B.order:ℝ) := by exact_mod_cast hn
  have heps : 0≤ε*(B.order:ℝ) := by positivity
  have hNdegree : (N:ℝ)≤(C.graph.maxDegree:ℝ) := by
    nlinarith only [habsolute,hnR,heps]
  have hNat : N≤C.graph.maxDegree := by exact_mod_cast hNdegree
  have : Nonempty C.vertices:=C.critical.1.nonempty
  have horder:=C.graph.maxDegree_lt_card_verts
  refine ⟨by change N≤Fintype.card C.vertices;omega,?_⟩
  have hm:=mul_le_mul_of_nonneg_left hoR
    (by positivity : 0≤(1:ℝ)/2+ε/2)
  exact hm.trans habsolute

/-- For any allowed linear budget, the run is constructed and either
completes all m reductions or reaches an actual overfull stop earlier.
The common threshold and q are selected before the graph and the budget. -/
theorem above_half_bounded_actual_run (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (hc : Overfull.IsDeltaCritical G) (hno : ¬G.HasOverfullSubgraph),
        2*N+2≤Fintype.card V →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ∀m : ℕ,4*(m:ℝ)≤ε*(Fintype.card V:ℝ) →
        ∃j : ℕ,j≤m ∧ ∃C : CriticalGraph.{u},
          Nonempty (Run (initial G hc hno) C j) ∧
          (j=m ∨ Nonempty (Stop q C)) := by
  obtain ⟨q,hq,N,hfork⟩:=CriticalReductionStop.above_half_next_witness_or_stop.{u}
    (ε/2) (by positivity)
  refine ⟨q,hq,N,?_⟩
  intro V _ _ G _ hc hno hn hdense m hbudget
  let B:=initial G hc hno
  have build : ∀t j : ℕ,j+t=m → ∀C : CriticalGraph.{u},Run B C j →
      ∃i : ℕ,i≤m ∧ ∃D : CriticalGraph.{u},
        Nonempty (Run B D i) ∧ (i=m ∨ Nonempty (Stop q D)) := by
    intro t
    induction t with
    | zero =>
      intro j hj C p
      exact ⟨j,by omega,C,⟨p⟩,Or.inl (by omega)⟩
    | succ t ih =>
      intro j hj C p
      have hjm : j≤m := by omega
      obtain ⟨hsize,hd⟩:=run_margins ε hε N m p hn hdense hbudget hjm
      obtain ⟨r,hnext⟩:=hfork C.graph hsize C.critical hd C.no_overfull
      rcases hnext with hnext|hstop
      · obtain ⟨hnoR,w,_,_,_⟩:=hnext
        let s : Step C:=⟨r,hnoR,w⟩
        exact ih (j+1) (by omega) s.target (Run.snoc p s)
      · obtain ⟨X,hX⟩:=hstop
        exact ⟨j,hjm,C,⟨p⟩,Or.inr ⟨⟨r,X,hX⟩⟩⟩
  exact build m 0 (by omega) B (Run.nil B)

end OverfullWork.BoundedCriticalReductionRun
