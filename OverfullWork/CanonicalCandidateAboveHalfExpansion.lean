module

public import OverfullWork.CanonicalBipartiteExpansionUniform

@[expose] public section


/-! # Direct bipartite expansion for the above-half canonical branch

The source size, sparse budgets, image order and density are related
explicitly. All remaining arithmetic assumptions of the constructed
candidate cut are discharged. This proves expansion, not factorization.
-/
namespace OverfullWork.CanonicalCandidateAboveHalfExpansion
open SimpleGraph Finset
open scoped Classical
set_option maxHeartbeats 12000000

theorem source_bounds (Q n m D Y B : ℕ) (hQ : 2≤Q) (hm : 2^50*Q^4≤m)
    (hCard : n+1=2*m+Y) (hY : Y≤n/(4096*Q^2)+1)
    (hB : B≤6*(n/(4096*Q^2))+6) (hD : D<n)
    (hDense : (Q+2)*n≤2*Q*D) :
    B≤m ∧ D≤3*m ∧ Y≤m/(1024*Q) ∧ m+16*(m/(1024*Q))+4≤D := by
  let k:=n/(4096*Q^2)
  change Y≤k+1 at hY
  change B≤6*k+6 at hB
  have hk:4096*Q^2*k≤n:=Nat.mul_div_le n (4096*Q^2)
  have hPow:Q≤Q^4:=by simpa only [pow_one] using Nat.pow_le_pow_right (show 0<Q by omega) (by decide : 1≤4)
  have hLinear:16384*Q≤m:=by nlinarith only [hm,hPow]
  have hCoef:4096*Q+1≤4096*Q^2:=by nlinarith only [hQ]
  have hMul:=Nat.mul_le_mul_right k hCoef
  have hkM:2048*Q*k≤m:=by nlinarith only [hk,hMul,hY,hCard]
  have hY':Y≤m/(1024*Q):=by
    apply (Nat.le_div_iff_mul_le (show 0<1024*Q by positivity)).mpr
    have hMulY:=Nat.mul_le_mul_left (1024*Q) hY
    have hBound:1024*Q*(k+1)≤m:=by nlinarith only [hkM,hLinear]
    nlinarith only [hMulY,hBound]
  have hB':B≤m:=by
    have hc:12≤2048*Q:=by omega
    have hh:12*k≤m:=(Nat.mul_le_mul_right k hc).trans hkM
    omega
  have hD':D≤3*m:=by
    have hy:Y≤m:=hY'.trans (Nat.div_le_self _ _)
    omega
  have hDensity:m+16*(m/(1024*Q))+4≤D:=by
    let q:=m/(1024*Q)
    have hq:1024*Q*q≤m:=Nat.mul_div_le m (1024*Q)
    have hqWeak:32*Q*q≤m:=by
      have hc:32*Q≤1024*Q:=by omega
      exact (Nat.mul_le_mul_right q hc).trans hq
    by_contra hn
    have hBad:D≤m+16*q+3:=by omega
    have hBadMul:=Nat.mul_le_mul_left (2*Q) hBad
    have h2m:2*m≤n+1:=by omega
    have h2mMul:=Nat.mul_le_mul_left (Q+2) h2m
    nlinarith only [hBadMul,h2mMul,hDense,hqWeak,hLinear,hQ]
  exact ⟨hB',hD',hY',hDensity⟩

end OverfullWork.CanonicalCandidateAboveHalfExpansion

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification BipartiteRobustMargin
open scoped Classical
universe u
set_option maxHeartbeats 12000000

theorem exists_scale_candidate_robust_cut (Q : ℕ) (hQ : 2≤Q) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),
      N≤Fintype.card V → B≤6*(Fintype.card V/(4096*Q^2))+6 →
      K≤Fintype.card V/(4096*Q^2)+1 →
      (Q+2)*Fintype.card V≤2*Q*G.maxDegree →
      ∃A : Finset (Fin (p.pairIndex+1)×Bool),A.card=p.pairIndex+1 ∧ Aᶜ.card=p.pairIndex+1 ∧
        (∀i : Fin (p.pairIndex+1),((i,true)∈A ↔ (i,false)∉A)) ∧
        IsBipartiteRobustAt p.orderedBase.supportGraph A
          ((p.pairIndex+1)/(2^30*Q^3)) ((p.pairIndex+1)/(1024*Q)) ∧
        (0<(p.pairIndex+1)/(2^30*Q^3) ∧ 2*((p.pairIndex+1)/(1024*Q))≤p.pairIndex+1) ∧
        ∀v,|(p.completed.degreeInto A v:ℝ)-(p.completed.degreeInto Aᶜ v:ℝ)|<
          (1/(1024*(Q:ℝ)))*((p.pairIndex+1:ℕ):ℝ)+
            ((G.maxDegree-p.orderedBase.supportGraph.degree v:ℕ):ℝ) := by
  obtain ⟨N₀,hN₀⟩:=exists_fixed_density_candidate_robust_cut.{u} Q (by omega)
  refine ⟨3*(max N₀ (2^50*Q^4)),?_⟩
  intro V _ _ G _ B K c p hn hB hK hDense
  let n:=Fintype.card V
  let m:=p.pairIndex+1
  let Y:=c.setᶜ.card
  have hCoords:=Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts:=card_add_card_compl c.set
  have hCard:n+1=2*m+Y:=by dsimp only [n,m,Y];omega
  have hY:Y≤n/(4096*Q^2)+1:=c.complement_small.trans hK
  have hk:4096*Q^2*(n/(4096*Q^2))≤n:=Nat.mul_div_le n (4096*Q^2)
  have hc:3≤4096*Q^2:=by nlinarith only [hQ]
  have hk3:3*(n/(4096*Q^2))≤n:=
    (Nat.mul_le_mul_right (n/(4096*Q^2)) hc).trans hk
  have hnm:n≤3*m:=by omega
  have hN:N₀≤m:=by change 3*(max N₀ (2^50*Q^4))≤n at hn;omega
  have hLarge:2^50*Q^4≤m:=by change 3*(max N₀ (2^50*Q^4))≤n at hn;omega
  have hNonempty:c.set.Nonempty:=card_pos.mp (by obtain ⟨a,ha⟩:=c.odd;omega)
  have : Nonempty V:=by obtain ⟨v,_⟩:=hNonempty;exact ⟨v⟩
  have hD:G.maxDegree<n:=G.maxDegree_lt_card_verts
  obtain ⟨hBm,hDm,hYm,hDensity⟩:=CanonicalCandidateAboveHalfExpansion.source_bounds
    Q n m G.maxDegree Y B hQ hLarge hCard hY hB hD hDense
  exact hN₀ G c p hN hBm hDm hYm hDensity

/-- For every fixed positive above-half margin, the sparse scale and
threshold precede the original graph. Every actual candidate with the
existing sparse budgets has a constructed bipartite robust cut. -/
theorem exists_above_half_candidate_robust_cut (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),N≤Fintype.card V →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*Q^2))+6 → K≤Fintype.card V/(4096*Q^2)+1 →
      ∃A : Finset (Fin (p.pairIndex+1)×Bool),A.card=p.pairIndex+1 ∧ Aᶜ.card=p.pairIndex+1 ∧
        (∀i : Fin (p.pairIndex+1),((i,true)∈A ↔ (i,false)∉A)) ∧
        IsBipartiteRobustAt p.orderedBase.supportGraph A
          ((p.pairIndex+1)/(2^30*Q^3)) ((p.pairIndex+1)/(1024*Q)) ∧
        (0<(p.pairIndex+1)/(2^30*Q^3) ∧ 2*((p.pairIndex+1)/(1024*Q))≤p.pairIndex+1) ∧
        ∀v,|(p.completed.degreeInto A v:ℝ)-(p.completed.degreeInto Aᶜ v:ℝ)|<
          (1/(1024*(Q:ℝ)))*((p.pairIndex+1:ℕ):ℝ)+
            ((G.maxDegree-p.orderedBase.supportGraph.degree v:ℕ):ℝ) := by
  obtain ⟨Q,hQ⟩:=exists_nat_gt (max (2:ℝ) (1/ε))
  have hQR:(2:ℝ)≤Q:=(le_max_left _ _).trans hQ.le
  have hQN:2≤Q:=by exact_mod_cast hQR
  have hQε:1≤ε*(Q:ℝ):=by
    have hh:1/ε<(Q:ℝ):=(le_max_right _ _).trans_lt hQ
    have ht:=(div_lt_iff₀ hε).mp hh
    nlinarith only [ht]
  obtain ⟨N,hN⟩:=exists_scale_candidate_robust_cut.{u} Q hQN
  refine ⟨Q,hQN,N,?_⟩
  intro V _ _ G _ B K c p hn hdense hB hK
  apply hN G c p hn hB hK
  have h₁:=mul_le_mul_of_nonneg_left hdense (show 0≤2*(Q:ℝ) by positivity)
  have h₂:=mul_le_mul_of_nonneg_right hQε (Nat.cast_nonneg (Fintype.card V))
  exact_mod_cast (show ((Q:ℝ)+2)*(Fintype.card V:ℝ)≤2*(Q:ℝ)*(G.maxDegree:ℝ) by
    nlinarith only [h₁,h₂])

end OverfullWork.NormalizedCanonicalCandidate
