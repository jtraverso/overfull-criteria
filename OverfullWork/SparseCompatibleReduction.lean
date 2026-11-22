module

public import OverfullWork.SparseLargeLowLayer
public import OverfullWork.SparseSmallLowLayer
public import OverfullWork.AlmostOverfullLayerCompatibility

@[expose] public section


/-! # Sparse actual reductions and the explicit almost-overfull alternative

The four low-set cases share one conservative missing-degree scale chosen
before the graph. The reduction scale and the stopping scale remain
separate. Either the original graph has an almost-overfull set at the
explicit combined budget, or an actual reduction has a no-overfull residue.
This does not eliminate the almost-overfull branch or assert unlimited
iteration.
-/
namespace OverfullWork.SparseCompatibleReduction
open SimpleGraph Finset LowVertexMatchingAbsorption
open CriticalTwoColourReduction AlmostOverfullLayerCompatibility
open scoped Classical
universe u
set_option maxHeartbeats 5000000

/-- Decreasing the chosen q only increases the permitted integer scale. -/
theorem integer_scale_antitone (n q q' : ℕ) (hq : 0<q) (hqq : q≤q') :
    n/(4096*q'^2)≤n/(4096*q^2) := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0<4096*q^2)).mpr
  have hd:4096*q^2≤4096*q'^2:=Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left hqq 2)
  calc
    _ ≤ (n/(4096*q'^2))*(4096*q'^2) := Nat.mul_le_mul_left _ hd
    _ ≤ n := by
      have hh:=Nat.mul_div_le n (4096*q'^2)
      nlinarith only [hh]

/-- Every low-set cardinality admits an actual reduction with one uniform
missing-degree bound. The minimum of the three fixed scales is paid only
in that numerical bound; no equality of constructed exceptional sets is
assumed. -/
theorem above_half_sparse_reduction (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        ∃r : Reduction G,(∑v:V,(2-r.layer.degree v))≤2*(Fintype.card V/(4096*q^2))+2 := by
  obtain ⟨qE,hqE,NE,hE⟩:=SparseLowLayer.above_half_even_low_sparse.{u} ε hε
  obtain ⟨qO,hqO,NO,hO⟩:=SparseLowLayer.above_half_odd_low_sparse.{u} ε hε
  obtain ⟨qS,hqS,NS,hS⟩:=SparseSmallLowLayer.above_half_small_low_layer_sparse.{u} ε hε
  let q:=min qE (min qO qS)
  have hq:2≤q:=le_min hqE (le_min hqO hqS)
  have hqE':q≤qE:=min_le_left _ _
  have hqO':q≤qO:=(min_le_right _ _).trans (min_le_left _ _)
  have hqS':q≤qS:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨q,hq,max NE (max NO NS),?_⟩
  intro V _ _ G _ hn hc hdense hno
  have hnE:NE≤Fintype.card V:=(le_max_left _ _).trans hn
  have hnOS:max NO NS≤Fintype.card V:=(le_max_right _ _).trans hn
  have hnO:NO≤Fintype.card V:=(le_max_left _ _).trans hnOS
  have hnS:NS≤Fintype.card V:=(le_max_right _ _).trans hnOS
  have hscaleE:=integer_scale_antitone (Fintype.card V) q qE (by omega) hqE'
  have hscaleO:=integer_scale_antitone (Fintype.card V) q qO (by omega) hqO'
  have hscaleS:=integer_scale_antitone (Fintype.card V) q qS (by omega) hqS'
  by_cases htwo:2≤(lowVertices G).card
  · by_cases heven:Even (lowVertices G).card
    · obtain ⟨r,hr⟩:=hE G hnE hc hdense heven htwo
      refine ⟨r,?_⟩
      change (∑v:V,(2-r.layer.degree v))≤_ at hr
      omega
    · have hodd:Odd (lowVertices G).card:=Nat.not_even_iff_odd.mp heven
      have hthree:3≤(lowVertices G).card:=by obtain ⟨k,hk⟩:=hodd;omega
      obtain ⟨r,hr⟩:=hO G hnO hc hdense hodd hthree
      refine ⟨r,?_⟩
      change (∑v:V,(2-r.layer.degree v))≤_ at hr
      omega
  · obtain ⟨c,_,hMissing⟩:=hS G hnS hc hdense hno (by omega)
    let r:Reduction G:={
      layer:=c.layer,le_original:=c.le_original,acyclic:=c.acyclic,
      degree_le_two:=c.degree_le_two,colourable:=c.colourable,demands:=c.demands,
      low_positive:=by intro w hw;rw [c.low_one_cover w hw],
      residual_maxDegree:=c.residual_maxDegree,residual_uncolourable:=c.residual_uncolourable }
    refine ⟨r,?_⟩
    have hb:(∑v:V,(2-r.layer.degree v))≤2*(Fintype.card V/(4096*qS^2))+2:=by
      simpa only [r] using hMissing
    omega

/-- Both scales are fixed before the graph. A residue with an overfull
set is detected through a proved almost-overfull set of the original;
otherwise the actual sparse reduction is compatible. -/
theorem above_half_sparse_compatible_or_almost (ε : ℝ) (hε : 0<ε) :
    ∃qR qS : ℕ,2≤qR ∧ 2≤qS ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        let kR:=Fintype.card V/(4096*qR^2)
        let kS:=Fintype.card V/(4096*qS^2)
        HasOddAlmostOverfullSet G ((2*kR+2)+8*kS) ∨
          ∃r : Reduction G,(∑v:V,(2-r.layer.degree v))≤2*kR+2 ∧
            ¬(G\r.layer).HasOverfullSubgraph := by
  obtain ⟨qR,hqR,NR,hR⟩:=above_half_sparse_reduction.{u} ε hε
  obtain ⟨qS,hqS,NS,hS⟩:=above_half_overfull_residue_implies_almost.{u} ε hε
  refine ⟨qR,qS,hqR,hqS,max NR NS,?_⟩
  intro V _ _ G _ hn hc hdense hno
  obtain ⟨r,hMissing⟩:=hR G ((le_max_left _ _).trans hn) hc hdense hno
  have hs:=hS G ((le_max_right _ _).trans hn) hc hdense
  dsimp only
  by_cases hOF:(G\r.layer).HasOverfullSubgraph
  · left
    exact hs r.layer r.le_original
      (r.layer.maxDegree_le_of_forall_degree_le 2 r.degree_le_two)
      r.residual_maxDegree _ hMissing hOF
  · exact Or.inr ⟨r,hMissing,hOF⟩

/-- The original no-almost-overfull test yields an actual sparse
reduction whose residue has no overfull subgraph. It does not posit such
a compatible layer as an input. -/
theorem above_half_sparse_compatible_of_no_almost (ε : ℝ) (hε : 0<ε) :
    ∃qR qS : ℕ,2≤qR ∧ 2≤qS ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        let kR:=Fintype.card V/(4096*qR^2)
        let kS:=Fintype.card V/(4096*qS^2)
        ¬HasOddAlmostOverfullSet G ((2*kR+2)+8*kS) →
          ∃r : Reduction G,(∑v:V,(2-r.layer.degree v))≤2*kR+2 ∧
            ¬(G\r.layer).HasOverfullSubgraph := by
  obtain ⟨qR,qS,hqR,hqS,N,hN⟩:=above_half_sparse_compatible_or_almost.{u} ε hε
  refine ⟨qR,qS,hqR,hqS,N,?_⟩
  intro V _ _ G _ hn hc hdense hno
  dsimp only
  intro hNoAlmost
  exact (hN G hn hc hdense hno).resolve_left hNoAlmost

end OverfullWork.SparseCompatibleReduction
