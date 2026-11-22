module

public import OverfullWork.CanonicalGlobalRobust

@[expose] public section


/-! # Global expansion at a scale chosen independently of local profile eta

The scale P can be fixed from the original density margin before any
local error eta is selected. All graph and counting inequalities are
discharged from the original sparse certificate budgets.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
universe u
set_option maxHeartbeats 12000000

theorem above_half_global_robust_at_fixed_scale (ε : ℝ) (_hε : 0<ε)
    (P : ℕ) (hP : 2≤P) (hPε : 1≤ε*(P:ℝ)) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),N≤Fintype.card V →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*P^2))+6 → K≤Fintype.card V/(4096*P^2)+1 →
      RobustExpansion.IsRobustAt p.completed.supportGraph
        ((p.pairIndex+1)/(2^30*P^3)) ((p.pairIndex+1)/(1024*P)) ∧
        (0<(p.pairIndex+1)/(2^30*P^3) ∧ 2*((p.pairIndex+1)/(1024*P))≤2*(p.pairIndex+1)) := by
  refine ⟨3*(2^50*P^4),?_⟩
  intro V _ _ G _ B K c p hn hdense hB hK
  let n:=Fintype.card V
  let m:=p.pairIndex+1
  let Y:=c.setᶜ.card
  have hCoords:=Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts:=card_add_card_compl c.set
  have hCard:n+1=2*m+Y:=by dsimp only [n,m,Y];omega
  have hY:Y≤n/(4096*P^2)+1:=c.complement_small.trans hK
  have hk:4096*P^2*(n/(4096*P^2))≤n:=Nat.mul_div_le n (4096*P^2)
  have hCoef:3≤4096*P^2:=by nlinarith only [hP]
  have hk3:3*(n/(4096*P^2))≤n:=
    (Nat.mul_le_mul_right (n/(4096*P^2)) hCoef).trans hk
  have hnm:n≤3*m:=by omega
  have hm:2^50*P^4≤m:=by change 3*(2^50*P^4)≤n at hn;omega
  have hNonempty:c.set.Nonempty:=card_pos.mp (by obtain ⟨a,ha⟩:=c.odd;omega)
  have : Nonempty V:=by obtain ⟨v,_⟩:=hNonempty;exact ⟨v⟩
  have hD:G.maxDegree<n:=G.maxDegree_lt_card_verts
  have hDense:(P+2)*n≤2*P*G.maxDegree:=by
    have h₁:=mul_le_mul_of_nonneg_left hdense (show 0≤2*(P:ℝ) by positivity)
    have h₂:=mul_le_mul_of_nonneg_right hPε (Nat.cast_nonneg n)
    exact_mod_cast (show ((P:ℝ)+2)*(n:ℝ)≤2*(P:ℝ)*(G.maxDegree:ℝ) by
      nlinarith only [h₁,h₂])
  obtain ⟨hBm,hDm,hYm,hDensity⟩:=CanonicalCandidateAboveHalfExpansion.source_bounds
    P n m G.maxDegree Y B hP hm hCard hY hB hD hDense
  have hBq:=CanonicalGlobalRobust.source_budget_le_four_q P n m B Y hP hm hCard hY hB
  exact p.global_robust_at_scales P hP hm hDm hBq hDensity

end OverfullWork.NormalizedCanonicalCandidate
