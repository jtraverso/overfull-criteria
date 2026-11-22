module

public import OverfullWork.FlexibleSparseReduction
public import OverfullWork.FlexibleCriticalExceptionCount
public import OverfullWork.NormalizedAlmostStoppingRun

@[expose] public section


/-! # A freely chosen almost-overfull stopping scale

G1 bounds the actual exceptional set of an existing construction at any
fixed target scale Q. The same improvement localizes a residual overfull
set to at most k+1 complementary vertices. Thus the constructed sparse
reduction is compatible or has an original almost-stop with budget 6k+6,
where k=n/(4096Q^2) and Q is chosen before the graph.
-/
namespace OverfullWork.FlexibleAlmostReduction
open SimpleGraph Finset SparseDeficitCore OddCutDeficit
open AlmostOverfullLayerCompatibility
open scoped Classical
universe u
set_option maxHeartbeats 5000000

/-- The desired error scale is supplied before the threshold and graph;
no no-overfull property of a residue is an input. -/
theorem above_half_compatible_or_almost_at_budget (ε : ℝ) (hε : 0<ε)
    (Q : ℕ) (hQ : 2≤Q) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      ¬G.HasOverfullSubgraph →
      let k:=Fintype.card V/(4096*Q^2)
      HasOddAlmostOverfullSet G (6*k+6) ∨
        ∃r : CriticalTwoColourReduction.Reduction G,
          (∑v:V,(2-r.layer.degree v))≤2*k+2 ∧
          ¬(G\r.layer).HasOverfullSubgraph := by
  obtain ⟨NR,hReduce⟩:=FlexibleSparseReduction.above_half_sparse_reduction_at_budget.{u} ε hε Q hQ
  obtain ⟨q,hq,NS,hStop⟩:=ResidualOverfullLocalization.above_half_residual_overfull_stop.{u} ε hε
  obtain ⟨NC,hCount⟩:=FlexibleCriticalExceptionCount.exception_count_at_scales.{u} q Q hq hQ
  refine ⟨max NR (max NS (max NC 4)),?_⟩
  intro V _ _ G _ hn hc hdense hno
  have hnR:NR≤Fintype.card V:=(le_max_left _ _).trans hn
  have hnS:NS≤Fintype.card V:=by omega
  have hnC:NC≤Fintype.card V:=by omega
  have hn4:4≤Fintype.card V:=by omega
  have hnD:Fintype.card V≤2*G.maxDegree:=by
    have he:0≤ε*(Fintype.card V:ℝ):=by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hD:2≤G.maxDegree:=by omega
  obtain ⟨r,hMissing⟩:=hReduce G hnR hc hdense hno
  have hUk:=hCount G hnC hc hnD
  obtain ⟨_,hs⟩:=hStop G hnS hc hdense
  dsimp only
  by_cases hOF:(G\r.layer).HasOverfullSubgraph
  · left
    obtain ⟨X,ho,hof,_,_,_,hOutside,hStar⟩:=hs r.layer r.le_original
      (r.layer.maxDegree_le_of_forall_degree_le 2 r.degree_le_two) r.residual_maxDegree hOF
    have hCard:=card_le_card_sdiff_add_card (s:=Xᶜ)
      (t:=exceptions G G.maxDegree (Fintype.card V/(8*q)))
    have hTiny:Xᶜ.card≤Fintype.card V/(4096*Q^2)+1:=by omega
    have hb:=budget_of_residual_overfull G r.layer r.le_original r.degree_le_two hD
      r.residual_maxDegree X ho hof hStar _ hMissing
    exact ⟨X,ho,by omega⟩
  · exact Or.inr ⟨r,hMissing,hOF⟩

/-- Every almost-stop at this freely chosen scale can be normalized to
an independent, degree-ordered complement of at most k+1 vertices. -/
theorem above_half_normalized_fork_at_budget (ε : ℝ) (hε : 0<ε)
    (Q : ℕ) (hQ : 2≤Q) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      ¬G.HasOverfullSubgraph →
      let k:=Fintype.card V/(4096*Q^2)
      Nonempty (NormalizedAlmostStoppingRun.Certificate G (6*k+6) (k+1)) ∨
        ∃r : CriticalTwoColourReduction.Reduction G,
          (∑v:V,(2-r.layer.degree v))≤2*k+2 ∧
          ¬(G\r.layer).HasOverfullSubgraph := by
  obtain ⟨NF,hFork⟩:=above_half_compatible_or_almost_at_budget.{u} ε hε Q hQ
  obtain ⟨NC,hCount⟩:=FlexibleCriticalExceptionCount.exception_count_at_scales.{u} 2 Q (by omega) hQ
  refine ⟨max NF (max NC 32),?_⟩
  intro V _ _ G _ hn hc hdense hno
  have hnF:NF≤Fintype.card V:=by omega
  have hnC:NC≤Fintype.card V:=by omega
  have hn32:32≤Fintype.card V:=by omega
  dsimp only
  rcases hFork G hnF hc hdense hno with hAlmost|hReduction
  · left
    let n:=Fintype.card V
    let k:=n/(4096*Q^2)
    let a:=n/16
    have hnD:n≤2*G.maxDegree:=by
      have he:0≤ε*(n:ℝ):=by positivity
      exact_mod_cast (show (n:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
    have hk:64*k≤n:=(Nat.mul_le_mul_right k (show 64≤4096*Q^2 by nlinarith)).trans
      (Nat.mul_div_le n (4096*Q^2))
    have ha:16*a≤n:=Nat.mul_div_le n 16
    have hGap:2*a+(6*k+6)<G.maxDegree:=by omega
    have hB:6*k+6<G.maxDegree+4:=by omega
    have hUk:=hCount G hnC hc hnD
    obtain ⟨X,ho,hb⟩:=hAlmost
    have hSmall:=AlmostOverfullOriginalGeometry.complement_card_le_exceptions_add_one
      G X a (6*k+6) hGap hb
    have hSmall':Xᶜ.card≤k+1:=by
      have hU:(exceptions G G.maxDegree a).card≤k:=by simpa only [a,n,k] using hUk
      omega
    exact NormalizedAlmostStoppingRun.exists_certificate G hc X ho (6*k+6) (k+1) hB hSmall' hb
  · exact Or.inr hReduction

/-- Choosing Q from the fixed density margin pays the numerical gap
needed for identifying the independent complement. This gap is proved
for the actual normalized cut, rather than assumed as an extra input. -/
theorem above_half_normalized_fork_with_gap (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        let k:=Fintype.card V/(4096*Q^2)
        (∃c : NormalizedAlmostStoppingRun.Certificate G (6*k+6) (k+1),
          c.set.card+(6*k+6)+2*c.setᶜ.card≤2*G.maxDegree+2) ∨
        ∃r : CriticalTwoColourReduction.Reduction G,
          (∑v:V,(2-r.layer.degree v))≤2*k+2 ∧
          ¬(G\r.layer).HasOverfullSubgraph := by
  obtain ⟨Q,hQ⟩:=exists_nat_gt (max (2:ℝ) (1/ε))
  have hQR:(2:ℝ)≤(Q:ℝ):=(le_max_left _ _).trans hQ.le
  have hQN:2≤Q:=by exact_mod_cast hQR
  have hQε:1≤ε*(Q:ℝ):=by
    have hh:1/ε<(Q:ℝ):=(le_max_right _ _).trans_lt hQ
    have ht:=(div_lt_iff₀ hε).mp hh
    nlinarith only [ht]
  obtain ⟨NF,hFork⟩:=above_half_normalized_fork_at_budget.{u} ε hε Q hQN
  obtain ⟨NE,hNE⟩:=exists_nat_gt (5/ε)
  refine ⟨Q,hQN,max NF NE,?_⟩
  intro V _ _ G _ hn hc hdense hno
  have hnF:NF≤Fintype.card V:=by omega
  have hnE:NE≤Fintype.card V:=by omega
  dsimp only
  rcases hFork G hnF hc hdense hno with hCert|hr
  · obtain ⟨c⟩:=hCert
    left
    refine ⟨c,?_⟩
    let n:=Fintype.card V
    let k:=n/(4096*Q^2)
    have hk:4096*Q^2*k≤n:=Nat.mul_div_le n (4096*Q^2)
    have hkR:(4096:ℝ)*(Q:ℝ)^2*(k:ℝ)≤(n:ℝ):=by exact_mod_cast hk
    have hCoeff:(7:ℝ)≤ε*(4096*(Q:ℝ)^2):=by
      have hh:=mul_le_mul_of_nonneg_left hQε (show 0≤4096*(Q:ℝ) by positivity)
      nlinarith only [hh,hQR]
    have hSeven:7*(k:ℝ)≤ε*(n:ℝ):=by
      have h₁:=mul_le_mul_of_nonneg_right hCoeff (Nat.cast_nonneg k : (0:ℝ)≤(k:ℝ))
      have h₂:=mul_le_mul_of_nonneg_left hkR hε.le
      nlinarith only [h₁,h₂]
    have hFive:(5:ℝ)≤ε*(n:ℝ):=by
      have hh:5/ε<(n:ℝ):=hNE.trans_le (by exact_mod_cast hnE)
      have ht:=(div_lt_iff₀ hε).mp hh
      nlinarith only [ht]
    have hGap:n+7*k+5≤2*G.maxDegree:=by
      exact_mod_cast (show (n:ℝ)+7*(k:ℝ)+5≤2*(G.maxDegree:ℝ) by
        nlinarith only [hdense,hSeven,hFive])
    have hCards:=card_add_card_compl c.set
    have hSmall:=c.complement_small
    change c.set.card+(6*k+6)+2*c.setᶜ.card≤2*G.maxDegree+2
    dsimp only [k,n] at hGap ⊢
    omega
  · exact Or.inr hr

end OverfullWork.FlexibleAlmostReduction
