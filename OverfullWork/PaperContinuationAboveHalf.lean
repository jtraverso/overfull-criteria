module

public import OverfullWork.ClassTwoMatchingRun

@[expose] public section


/-! # Uniform finite margins for the next matching on the cleaned graph

Doubling the freely chosen sparse-scale parameter pays the additional
core-degree loss of cleanup. The graph, the normalized cut, the anchor
and the actual cleaned step all occur after the uniform choices.
-/
namespace OverfullWork.PaperFirstRoundAboveHalf
open SimpleGraph Finset NormalizedAlmostStoppingRun ClassTwoMatchingRound PaperTopDegreeMatching
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u
set_option maxHeartbeats 6000000

theorem uniform_continuation_margins (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀n D : ℕ,N≤n →
      ((1:ℝ)/2+ε)*(n:ℝ)≤(D:ℝ) →
      let k:=n/(4096*Q^2)
      n+2*(6*k+6)+(k+1)+3≤2*D ∧
      n+(6*k+6)+(k+1)+5≤2*D ∧
      4*((6*k+6)+(k+1)+2)+1≤D ∧
      n+2*((6*k+6)+(k+1))+(k+1)+5≤2*D := by
  obtain ⟨q,hq,N,hM⟩:=uniform_margins ε hε
  refine ⟨2*q,by omega,max N (4096*(2*q)^2),?_⟩
  intro n D hn hdense
  let k:=n/(4096*(2*q)^2)
  let t:=n/(4096*q^2)
  have hnN:N≤n:=by omega
  have hBase:=hM n D hnN hdense
  change n+2*(6*t+6)+(t+1)+3≤2*D ∧
    n+(6*t+6)+(t+1)+5≤2*D ∧ 4*((6*t+6)+(t+1)+2)+1≤D at hBase
  have hDen:0<4096*q^2:=by positivity
  have hDen':0<4096*(2*q)^2:=by positivity
  have hkFloor:4096*(2*q)^2*k≤n:=Nat.mul_div_le n _
  have hDenEq:4096*(2*q)^2=4*(4096*q^2):=by ring
  have hFour:4*k≤t:=by
    apply (Nat.le_div_iff_mul_le hDen).mpr
    rw [hDenEq] at hkFloor
    nlinarith only [hkFloor]
  have hkPos:1≤k:=by
    apply (Nat.le_div_iff_mul_le hDen').mpr
    simp only [Nat.one_mul]
    omega
  change n+2*(6*k+6)+(k+1)+3≤2*D ∧
    n+(6*k+6)+(k+1)+5≤2*D ∧ 4*((6*k+6)+(k+1)+2)+1≤D ∧
    n+2*((6*k+6)+(k+1))+(k+1)+5≤2*D
  omega

/-- The same actual first cleaned graph either meets an explicit stop
test or has a constructed next matching. The second matching residue
is class two with maximum lowered by one, as recorded in CoreRound.
Its no-overfullness and ability to undergo further rounds are not claimed. -/
theorem above_half_stopping_or_next_matching (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        let k:=Fintype.card V/(4096*Q^2)
        ∀(c : Certificate G (6*k+6) (k+1)) (x : V) (s : CleanStep G c x),
          x∈c.set → G.degree x<(∑w∈c.setᶜ,G.degree w) →
          ∃a∈c.set,(∀v∈c.set,s.graph.degree a≤s.graph.degree v) ∧
            ((c.setᶜ.filter fun w=>0<s.graph.degree w).card≤1 ∨
             (∑w∈c.setᶜ,s.graph.degree w)≤s.graph.degree a ∨
             (∃v∈c.set,v≠a ∧ s.graph.degree v≤s.graph.maxDegree-s.graph.degree a) ∨
             (∀v∈c.set,s.graph.degree v=s.graph.maxDegree) ∨
             ∃y z,IsTopPair s.graph c.setᶜ y z ∧ Nonempty (CoreRound s.graph c.set a y z)) := by
  obtain ⟨Q,hQ,N,hM⟩:=uniform_continuation_margins ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro V _ _ G _ hn hdense
  dsimp only
  intro c x s hx hLarge
  apply s.stopping_or_next_matching hx hLarge
  have hBounds:=hM (Fintype.card V) G.maxDegree hn hdense
  dsimp only at hBounds
  have hY:=c.complement_small
  have hMax:=s.maximum
  omega

theorem above_half_stopping_or_next_clean_round (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        let k:=Fintype.card V/(4096*Q^2)
        ∀(c : Certificate G (6*k+6) (k+1)) (x : V) (s : CleanStep G c x),
          x∈c.set → G.degree x<(∑w∈c.setᶜ,G.degree w) →
          ∃a∈c.set,(∀v∈c.set,s.graph.degree a≤s.graph.degree v) ∧
            ((c.setᶜ.filter fun w=>0<s.graph.degree w).card≤1 ∨
             (∑w∈c.setᶜ,s.graph.degree w)≤s.graph.degree a ∨
             (∃v∈c.set,v≠a ∧ s.graph.degree v≤s.graph.maxDegree-s.graph.degree a) ∨
             (∀v∈c.set,s.graph.degree v=s.graph.maxDegree) ∨
             ∃t : ClassTwoCleanupRound.CleanRound s.graph c.set,t.anchor=a) := by
  obtain ⟨Q,hQ,N,hM⟩:=uniform_continuation_margins ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro V _ _ G _ hn hdense
  dsimp only
  intro c x s hx hLarge
  have hBounds:=hM (Fintype.card V) G.maxDegree hn hdense
  dsimp only at hBounds
  have hY:=c.complement_small
  have hMax:=s.maximum
  apply s.stopping_or_next_clean_round hx hLarge
  · omega
  · omega
  · omega

end OverfullWork.PaperFirstRoundAboveHalf
