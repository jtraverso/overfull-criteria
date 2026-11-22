module

public import OverfullWork.CanonicalOddCutScales

@[expose] public section


/-! # Uniform no-overfull reduction to centre triples

For a fixed above-half margin, all size inequalities are discharged
before the original graph is chosen. This identifies the remaining local
no-overfull obligation and proves a sufficient actual centre-mass case.
It neither assumes nor concludes an edge colouring.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
universe u
set_option maxHeartbeats 12000000

theorem above_half_completion_no_overfull_iff_triples (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),N≤Fintype.card V →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*Q^2))+6 → K≤Fintype.card V/(4096*Q^2)+1 →
      ((¬p.completed.HasOverfullSubset G.maxDegree) ↔
        ∀S : Finset (Fin (p.pairIndex+1)×Bool),S.card=3 → p.centre∈S →
          G.maxDegree≤p.completed.cutSize S) ∧
      (B+4*c.setᶜ.card+6≤2*(∑y∈c.setᶜ,G.degree y) →
        ¬p.completed.HasOverfullSubset G.maxDegree) := by
  obtain ⟨Q,hQ,N₀,hN₀⟩:=exists_above_half_completed_robust_cut.{u} ε hε
  refine ⟨Q,hQ,3*(max N₀ (2^66*Q^6)),?_⟩
  intro V _ _ G _ B K c p hn hdense hB hK
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
  have hm:2^66*Q^6≤m:=by change 3*(max N₀ (2^66*Q^6))≤n at hn;omega
  have hN:N₀≤Fintype.card V:=by omega
  have hWeak:n≤2*G.maxDegree:=by
    have hNonneg:0≤(Fintype.card V:ℝ):=Nat.cast_nonneg _
    have hMul:0≤ε*(Fintype.card V:ℝ):=mul_nonneg hε.le hNonneg
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,hMul])
  have hΔ:m≤G.maxDegree:=by omega
  have hNonempty:c.set.Nonempty:=card_pos.mp (by obtain ⟨a,ha⟩:=c.odd;omega)
  have :Nonempty V:=by obtain ⟨v,_⟩:=hNonempty;exact ⟨v⟩
  have hΔm:G.maxDegree≤3*m:=by have hh:=G.maxDegree_lt_card_verts;omega
  obtain ⟨hLarge,hSmall⟩:=CanonicalOddCutScales.source_bounds Q n m G.maxDegree B Y
    hQ hm hnm hΔ hΔm hB hY
  obtain ⟨A,hA,hAc,hSep,hRobust,⟨hPos,hThreshold⟩,hDis⟩:=hN₀ G c p hN hdense hB hK
  refine ⟨p.completion_no_overfull_iff_triples A _ _ hA hAc hRobust hThreshold hLarge hSmall,?_⟩
  intro hCentre
  exact p.completion_no_overfull_of_centre_mass A _ _ hA hAc hRobust hThreshold
    hLarge hSmall hCentre

/-- If the completion still has an overfull set, both an actual centre
triple and a small source centre degree are necessary. -/
theorem above_half_completion_overfull_witness (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),N≤Fintype.card V →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*Q^2))+6 → K≤Fintype.card V/(4096*Q^2)+1 →
      p.completed.HasOverfullSubset G.maxDegree →
      (∃S : Finset (Fin (p.pairIndex+1)×Bool),S.card=3 ∧ p.centre∈S ∧
        p.completed.cutSize S<G.maxDegree) ∧
      2*(∑y∈c.setᶜ,G.degree y)<B+4*c.setᶜ.card+6 := by
  obtain ⟨Q,hQ,N,hN⟩:=above_half_completion_no_overfull_iff_triples.{u} ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro V _ _ G _ B K c p hn hdense hB hK hOF
  obtain ⟨hIff,hMass⟩:=hN G c p hn hdense hB hK
  have hBad:¬∀S : Finset (Fin (p.pairIndex+1)×Bool),S.card=3 → p.centre∈S →
      G.maxDegree≤p.completed.cutSize S:=fun hh=>hIff.mpr hh hOF
  push Not at hBad
  refine ⟨hBad,?_⟩
  by_contra hh
  exact hMass (by omega) hOF

end OverfullWork.NormalizedCanonicalCandidate
