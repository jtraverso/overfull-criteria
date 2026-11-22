module

public import OverfullWork.CriticalTwoColourReduction
public import OverfullWork.ResidualOverfullLocalization

@[expose] public section


/-! # Actual next critical witness or a localized overfull stopping set

The already constructed two-colour layer is used in both branches. If
the actual residue has no overfull subset, a critical copy is extracted
and its smaller maximum degree and density margin are proved. Otherwise
an actual odd stopping set with a tiny star complement is constructed.
This does not claim that the stopping branch has been eliminated.
-/
namespace OverfullWork.CriticalReductionStop
open SimpleGraph Finset SparseDeficitCore OddCutDeficit
open scoped Classical
universe u

def IsStoppingSet {V : Type u} [Fintype V] [DecidableEq V]
    (G L : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel L.Adj]
    (U : Finset V) (k : ℕ) (X : Finset V) : Prop :=
  Odd X.card ∧ (G.maxDegree-2)*(X.card/2) < internalEdges (G\L) X ∧
    G.maxDegree≤X.card+1 ∧ cutEdges (G\L) X+3≤G.maxDegree ∧
      Xᶜ.card≤2*k ∧ (Xᶜ\U).card≤1 ∧
      (Xᶜ=∅ ∨ ∃v∈Xᶜ,∀a∈Xᶜ,∀b∈Xᶜ,G.Adj a b → a=v ∨ b=v)

/-- There is no assumed stopping oracle or next witness. The branch is
decided on the actual residue and each required object is constructed. -/
theorem above_half_next_witness_or_stop (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        let U:=exceptions G G.maxDegree (Fintype.card V/(8*q))
        let k:=Fintype.card V/(4096*q^2)
        ∃r : CriticalTwoColourReduction.Reduction G,
          (¬(G\r.layer).HasOverfullSubgraph ∧
            ∃w : Critical.CriticalWitness (G\r.layer),
              w.graph.maxDegree=G.maxDegree-2 ∧ G.maxDegree≤Fintype.card w.vertices+1 ∧
              ((1:ℝ)/2+ε/2)*(Fintype.card w.vertices:ℝ)≤(w.graph.maxDegree:ℝ)) ∨
          ∃X : Finset V,IsStoppingSet G r.layer U k X := by
  obtain ⟨q,hq,NS,hstop⟩:=ResidualOverfullLocalization.above_half_residual_overfull_stop.{u} ε hε
  obtain ⟨NR,hreduce⟩:=CriticalTwoColourReduction.above_half_critical_two_colour_reduction.{u} ε hε
  obtain ⟨NE,hNE⟩:=exists_nat_gt (4/ε)
  refine ⟨q,hq,max NS (max NR NE),?_⟩
  intro V _ _ G _ hn hc hdense hno
  have hnS:NS≤Fintype.card V:=(le_max_left _ _).trans hn
  have hnRE:max NR NE≤Fintype.card V:=(le_max_right _ _).trans hn
  have hnR:NR≤Fintype.card V:=(le_max_left _ _).trans hnRE
  have hnE:NE≤Fintype.card V:=(le_max_right _ _).trans hnRE
  have hlarge : (4:ℝ)≤ε*(Fintype.card V:ℝ) := by
    have he : 4/ε<(Fintype.card V:ℝ):=hNE.trans_le (by exact_mod_cast hnE)
    have hh:=(div_lt_iff₀ hε).mp he
    nlinarith only [hh]
  have hD : 2≤G.maxDegree := by
    exact_mod_cast (show (2:ℝ)≤(G.maxDegree:ℝ) by
      nlinarith only [hdense,hlarge,Nat.cast_nonneg (Fintype.card V) (α:=ℝ)])
  obtain ⟨r⟩:=hreduce G hnR hc hdense hno
  dsimp only
  refine ⟨r,?_⟩
  by_cases hOF:(G\r.layer).HasOverfullSubgraph
  · right
    obtain ⟨_,hs⟩:=hstop G hnS hc hdense
    have hL:r.layer.maxDegree≤2:=r.layer.maxDegree_le_of_forall_degree_le 2 r.degree_le_two
    obtain ⟨X,hX⟩:=hs r.layer r.le_original hL r.residual_maxDegree hOF
    exact ⟨X,hX⟩
  · left
    obtain ⟨w⟩:=Critical.exists_criticalWitness (G\r.layer) r.residual_uncolourable hOF
    refine ⟨hOF,w,w.maxDegree_eq.trans r.residual_maxDegree,?_,?_⟩
    · have : Nonempty w.vertices:=w.critical.1.nonempty
      have hs:=w.graph.maxDegree_lt_card_verts
      rw [w.maxDegree_eq,r.residual_maxDegree] at hs
      omega
    · have ho : (Fintype.card w.vertices:ℝ)≤(Fintype.card V:ℝ) := by exact_mod_cast w.order_le
      have hm : (w.graph.maxDegree:ℝ)=(G.maxDegree:ℝ)-2 := by
        rw [w.maxDegree_eq,r.residual_maxDegree,Nat.cast_sub hD]
        norm_num
      have hh:=mul_le_mul_of_nonneg_left ho (by positivity : 0≤(1:ℝ)/2+ε/2)
      nlinarith only [hh,hdense,hlarge,hm]

end OverfullWork.CriticalReductionStop
