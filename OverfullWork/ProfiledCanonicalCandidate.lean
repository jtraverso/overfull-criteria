module

public import OverfullWork.CanonicalImageDegreeRange

@[expose] public section


/-! # One actual candidate has the local CMS profiles and no overfull set

The sparse scale is reconciled before the original graph is chosen.
The order bound refers to the compressed image, not the source order.
No colouring or global robust-expansion premise is asserted here.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
set_option maxHeartbeats 10000000

theorem exists_profiled_no_overfull_candidate (ε η : ℝ) (hε : 0<ε) (hη : 0<η) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ} (c : Certificate G B K),
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*Q^2))+6 → K≤Fintype.card V/(4096*Q^2)+1 →
      ¬G.HasOverfullSubgraph → c.set.card+B+2*c.setᶜ.card≤2*G.maxDegree+2 →
      (∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) →
      ∃p : Candidate c,p.CMSLocalProfiles η ∧ G.maxDegree<2*(p.pairIndex+1) ∧
        2*(p.pairIndex+1)≤3*G.maxDegree ∧ ¬p.completed.HasOverfullSubset G.maxDegree := by
  obtain ⟨Q₀,hQ₀,N₀,hN₀⟩:=above_half_small_centre_completion_no_overfull.{u} ε hε
  obtain ⟨Q₁,hQ₁,N₁,hN₁⟩:=exists_centred_cms_local_profiles.{u} η hη
  let Q:=max Q₀ Q₁
  have hQ:2≤Q:=hQ₀.trans (le_max_left _ _)
  have hDiv₀:∀n : ℕ,n/(4096*Q^2)≤n/(4096*Q₀^2):=by
    intro n
    exact Nat.div_le_div_left
      (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left (show Q₀≤Q from le_max_left _ _) 2))
      (by positivity)
  have hDiv₁:∀n : ℕ,n/(4096*Q^2)≤n/(4096*Q₁^2):=by
    intro n
    exact Nat.div_le_div_left
      (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left (show Q₁≤Q from le_max_right _ _) 2))
      (by positivity)
  refine ⟨Q,hQ,max (max N₀ N₁) (64*Q),?_⟩
  intro V _ _ G _ B K c hn hc hdense hB hK hNo hGap hMin
  have hB₀:B≤6*(Fintype.card V/(4096*Q₀^2))+6:=by have hh:=hDiv₀ (Fintype.card V);omega
  have hK₀:K≤Fintype.card V/(4096*Q₀^2)+1:=by have hh:=hDiv₀ (Fintype.card V);omega
  have hB₁:B≤6*(Fintype.card V/(4096*Q₁^2))+6:=by have hh:=hDiv₁ (Fintype.card V);omega
  have hK₁:K≤Fintype.card V/(4096*Q₁^2)+1:=by have hh:=hDiv₁ (Fintype.card V);omega
  obtain ⟨p,hProfiles⟩:=hN₁ G c (by omega) hB₁ hK₁ hNo hGap hMin
  have hWeak:Fintype.card V≤2*G.maxDegree:=by
    have hMul:0≤ε*(Fintype.card V:ℝ):=by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,hMul])
  exact ⟨p,hProfiles,p.maxDegree_lt_image_order_at_source_scale Q hQ (by omega) hB hK,
    p.image_order_le_three_delta hWeak,hN₀ G c p (by omega) hc hdense hB₀ hK₀ hMin⟩

end OverfullWork.NormalizedCanonicalCandidate
