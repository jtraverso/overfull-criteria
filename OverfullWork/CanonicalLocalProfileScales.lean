module

public import OverfullWork.CanonicalRankProfile

@[expose] public section


/-! # Pay the local CMS profile errors from the original source budgets -/
namespace OverfullWork.CanonicalLocalProfileScales
set_option maxHeartbeats 8000000

theorem source_loss_bound (Q n l B Y : ℕ) (hQ : 2≤Q) (hn : 64*Q≤n)
    (hCard : n+1=l+Y) (hB : B≤6*(n/(4096*Q^2))+6)
    (hY : Y≤n/(4096*Q^2)+1) : Q*(B+Y)≤l := by
  let k:=n/(4096*Q^2)
  have hCoeff:64*Q≤4096*Q^2:=by nlinarith only [hQ]
  have hk:64*Q*k≤n:=
    (Nat.mul_le_mul_right k hCoeff).trans (Nat.mul_div_le n (4096*Q^2))
  change B≤6*k+6 at hB
  change Y≤k+1 at hY
  have hE:B+Y≤7*k+7:=by omega
  have hMul:=Nat.mul_le_mul_left Q hE
  have hK:k≤Q*k:=by nlinarith only [hQ,Nat.zero_le k]
  nlinarith only [hMul,hY,hCard,hk,hn,hK]

end OverfullWork.CanonicalLocalProfileScales

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 8000000

theorem Candidate.local_profile_loss_at_source_scale (p : Candidate c) (Q : ℕ) (hQ : 2≤Q)
    (hn : 64*Q≤Fintype.card V) (hB : B≤6*(Fintype.card V/(4096*Q^2))+6)
    (hK : K≤Fintype.card V/(4096*Q^2)+1) : Q*(B+c.setᶜ.card)≤2*(p.pairIndex+1) := by
  have hCoords:=Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts:=card_add_card_compl c.set
  have hCard:Fintype.card V+1=2*(p.pairIndex+1)+c.setᶜ.card:=by omega
  exact CanonicalLocalProfileScales.source_loss_bound Q (Fintype.card V) (2*(p.pairIndex+1))
    B c.setᶜ.card hQ hn hCard hB (c.complement_small.trans hK)

end OverfullWork.NormalizedCanonicalCandidate
