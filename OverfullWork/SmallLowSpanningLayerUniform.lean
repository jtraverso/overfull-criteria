module

public import OverfullWork.SmallLowSpanningLayer
public import OverfullWork.CriticalDeficientVertices
public import OverfullWork.CriticalDenseCoreTrimming

@[expose] public section


/-! # Uniform actual spanning layers when there are no low vertices

The critical deficit theorem constructs the dense core, the deficient
vertex theorem constructs charged endpoints, and Hamilton-connectedness
constructs the path. The threshold precedes the graph and both parities
of its order are included.
-/
namespace OverfullWork.SmallLowSpanningLayerUniform
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open scoped Classical
universe u
set_option maxHeartbeats 4000000

/-- Uniform critical graphs have all numerical margins required by the
finite constructions for zero or one low vertex. -/
theorem above_half_small_low_margins (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        let U:=exceptions G G.maxDegree (Fintype.card V/(8*q))
        2≤G.maxDegree ∧
        (∀v∈U,G.degree v+2≤G.maxDegree) ∧
        3*(U.card+4)≤G.maxDegree ∧
        5≤Fintype.card ↥((U:Set V)ᶜ) ∧
        Fintype.card ↥((U:Set V)ᶜ)+2≤2*(G.induce ((U:Set V)ᶜ)).minDegree := by
  obtain ⟨q,hq,N,hcore⟩:=CriticalDenseCoreTrimming.above_half_critical_sparse_trimming.{u} ε hε
  refine ⟨q,hq,max N (4096*q^2),?_⟩
  intro V _ _ G _ hn hc hdense
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun x y => Classical.propDecidable (G.Adj x y)))
  have hn₀ : N≤Fintype.card V := (le_max_left N _).trans hn
  have hnscale : 4096*q^2≤Fintype.card V := (le_max_right N _).trans hn
  obtain ⟨hk,hU,htrim⟩:=hcore G hn₀ hc hdense
  let a:=Fintype.card V/(8*q)
  let k:=Fintype.card V/(4096*q^2)
  let U:=exceptions G G.maxDegree a
  change 0<k at hk
  change U.card≤k at hU
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by
      nlinarith only [hdense,he])
  have h32 : 32≤4096*q^2 := by nlinarith [sq_nonneg (q:ℤ)]
  have hkn : 32*k≤Fintype.card V :=
    (Nat.mul_le_mul_right k h32).trans (Nat.mul_div_le (Fintype.card V) (4096*q^2))
  obtain ⟨_,_,hra,_,_⟩:=RobustExpansion.sparse_deficit_integer_scales
    (Fintype.card V) q hq hnscale
  change 2*k+1≤a at hra
  have hexception : ∀v∈U,G.degree v+2≤G.maxDegree := by
    intro v hv
    have hd:=(mem_filter.mp hv).2
    change G.degree v+a<G.maxDegree at hd
    omega
  have hbudget : 3*(U.card+4)≤G.maxDegree := by omega
  have hm := htrim (⊥ : SimpleGraph V) bot_le (by simp)
  have hm' : Fintype.card ↥((U:Set V)ᶜ)+6*k+2≤
      2*(G.induce ((U:Set V)ᶜ)).minDegree ∧
      3*k+5≤Fintype.card ↥((U:Set V)ᶜ) := by
    simpa only [sdiff_bot] using hm
  have hsize : 5≤Fintype.card ↥((U:Set V)ᶜ) := by omega
  have hdegree : Fintype.card ↥((U:Set V)ᶜ)+2≤
      2*(G.induce ((U:Set V)ᶜ)).minDegree := by omega
  refine ⟨by omega,hexception,hbudget,?_,?_⟩
  · convert hsize using 1
  · convert hdegree using 1

/-- Both parities of a large above-half critical graph with W empty have
an actual two-colour forest satisfying every degree demand. The residual
maximum degree is exactly two less and its obstruction is preserved. -/
theorem above_half_zero_low_layer (ε : ℝ) (hε : 0<ε) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      ¬G.HasOverfullSubgraph → lowVertices G=∅ →
      Nonempty (SmallLowSpanningLayer.Certificate G) := by
  obtain ⟨q,hq,N₀,hmargins⟩:=above_half_small_low_margins.{u} ε hε
  obtain ⟨N₁,hdef⟩:=CriticalDeficientVertices.above_half_critical_two_deficient.{u} ε hε
  refine ⟨max N₀ N₁,?_⟩
  intro V _ _ G _ hn hc hdense hno hW
  have hn₀ : N₀≤Fintype.card V := (le_max_left N₀ N₁).trans hn
  have hn₁ : N₁≤Fintype.card V := (le_max_right N₀ N₁).trans hn
  obtain ⟨hD,hexception,hbudget,hsize,hcore⟩:=hmargins G hn₀ hc hdense
  let U:=exceptions G G.maxDegree (Fintype.card V/(8*q))
  have hbudgetU : 3*(U.card+4)≤G.maxDegree := by convert hbudget using 1
  have hdeficient:=hdef G hn₁ hc hdense hno
  obtain ⟨P⟩:=OddLowSmallCases.exists_charged_pair_of_lowVertices_eq_empty
    G U hW hdeficient (by omega)
  exact SmallLowSpanningLayer.exists_zero_low_layer_finite G hc hD U hW
    hexception P hsize hcore

end OverfullWork.SmallLowSpanningLayerUniform
