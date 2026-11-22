module

public import OverfullWork.CanonicalBipartiteExpansion
public import OverfullWork.BipartiteScaleParameters

@[expose] public section


/-! # Uniform direct bipartite expansion at a fixed above-half scale

All expansion parameters are constructed and their inequalities are
discharged. The remaining assumptions are finite density, budget and
complement-size bounds on the actual candidate, not expansion oracles.
No edge-colouring or G2 closure is asserted.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun BipartiteRobustMargin
open scoped Classical
universe u

theorem exists_fixed_density_candidate_robust_cut (Q : ℕ) (hQ : 1≤Q) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),
      let m:=p.pairIndex+1
      N≤m → B≤m → G.maxDegree≤3*m → c.setᶜ.card≤m/(1024*Q) →
      m+16*(m/(1024*Q))+4≤G.maxDegree →
      ∃A : Finset (Fin (p.pairIndex+1)×Bool),A.card=m ∧ Aᶜ.card=m ∧
        (∀i : Fin m,((i,true)∈A ↔ (i,false)∉A)) ∧
        IsBipartiteRobustAt p.orderedBase.supportGraph A
          (m/(2^30*Q^3)) (m/(1024*Q)) ∧
        (0<m/(2^30*Q^3) ∧ 2*(m/(1024*Q))≤m) ∧
        ∀v,|(p.completed.degreeInto A v:ℝ)-(p.completed.degreeInto Aᶜ v:ℝ)|<
          (1/(1024*(Q:ℝ)))*(m:ℝ)+((G.maxDegree-p.orderedBase.supportGraph.degree v:ℕ):ℝ) := by
  have hQR:0<(Q:ℝ):=by exact_mod_cast (show 0<Q by omega)
  let ε:ℝ:=1/(1024*(Q:ℝ))
  have hε:0<ε:=by dsimp only [ε];positivity
  obtain ⟨m₀,hm₀⟩:=exists_uniform_candidate_robust_cut.{u} ε hε
  refine ⟨max m₀ (2^50*Q^4),?_⟩
  intro V _ _ G _ B K c p
  dsimp only
  intro hn hB hD hY hDense
  let m:=p.pairIndex+1
  let q:=m/(1024*Q)
  let r:=m/(2^30*Q^3)
  let δ:=(m+1)/2+q
  have hLarge:2^50*Q^4≤m:=by omega
  have hN:m₀≤m:=by omega
  obtain ⟨hRoom,hδ,hMargin,hr,hrq,hrt,hScale⟩:=
    BipartiteScaleParameters.bounds Q m G.maxDegree B c.setᶜ.card hQ hLarge hD hB hY hDense
  have hRoom':2*(δ:ℝ)+ε*(m:ℝ)+3*((q+c.setᶜ.card:ℕ):ℝ)≤G.maxDegree:=by
    have he:ε*(m:ℝ)=(m:ℝ)/(1024*(Q:ℝ)):=by dsimp only [ε];ring
    rw [he]
    exact hRoom
  obtain ⟨A,hA,hAc,hSep,hRobust,hDis⟩:=hm₀ G c p hN q δ q r q hRoom' hδ hMargin hr hrq hrt hScale
  have ht:2*q≤m:=by
    have hh:1024*Q*q≤m:=Nat.mul_div_le m (1024*Q)
    have hc:2≤1024*Q:=by omega
    exact (Nat.mul_le_mul_right q hc).trans hh
  exact ⟨A,hA,hAc,hSep,hRobust,⟨hr,ht⟩,hDis⟩

end OverfullWork.NormalizedCanonicalCandidate
