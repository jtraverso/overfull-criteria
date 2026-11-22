module

public import OverfullWork.GeneralRegularization

@[expose] public section


/-! # A precise remaining factorization target for degree gap three

The regularization theorems are unconditional. Colourability in this file
has an explicit additional premise, `FourFactorizationAt`. No theorem
asserting that premise is introduced here.
-/
namespace OverfullWork.Gate8F1
open SimpleGraph
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The target extends the multiplicity-two motor while retaining its
parallel-excess budget. It is a proposition, not an axiom or theorem. -/
def FourFactorizationAt (m D : ℕ) : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (M : MultiGraph W) (x : W),
    Fintype.card W=2*m → M.IsRegularOfDegree D →
    (∀ e,M.mult e≤4) → M.HasParallelBudget x 3 → Nonempty (M.EdgeColoring D)

/-- Conditional reduction: the new multigraph factorization premise is
stated explicitly; no gap-three colourability theorem is claimed alone. -/
theorem even_colourable_of_four_factorization (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1≤m) (hcard : Fintype.card V=2*m)
    (hgap : G.maxDegree-G.minDegree≤3) (hno : ¬G.HasOverfullSubgraph)
    (hfactor : FourFactorizationAt.{u} m G.maxDegree) : G.EdgeColorable G.maxDegree := by
  obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=GeneralRegularization.exists_even_bounded_completion
    G m 3 hm hcard hno hgap
  obtain ⟨x⟩:=Fintype.card_pos_iff.mp (show 0<Fintype.card V by omega)
  obtain ⟨C⟩:=hfactor M x hcard hreg hmu (fun v _ => hbudget v)
  apply MultiGraph.edgeColourable_of_contained M G _ C
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v => exact hcontains u v ((mem_edgeSet G).mp he)

theorem odd_colourable_of_four_factorization (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1≤m) (hcard : Fintype.card V+1=2*m)
    (hgap : G.maxDegree-G.minDegree≤3) (hno : ¬G.HasOverfullSubgraph)
    (hfactor : FourFactorizationAt.{u} m G.maxDegree) : G.EdgeColorable G.maxDegree := by
  have hn : Odd (Fintype.card V):=⟨m-1,by omega⟩
  have hedge:=DegreeBudget.edge_bound_of_no_overfull G hn hno
  obtain ⟨M,hreg,hmu,hbudget,hcontains⟩:=GeneralRegularization.exists_odd_bounded_extension
    G m 3 hm hcard hedge hgap
  have hc : Fintype.card (Option V)=2*m:=by simpa using hcard
  obtain ⟨C⟩:=hfactor M none hc hreg hmu hbudget
  exact MultigraphExtension.edgeColourable_of_regularized_colouring G M C hcontains

end OverfullWork.Gate8F1
