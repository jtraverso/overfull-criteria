module

public import OverfullWork.CanonicalCMSLocalProfiles

@[expose] public section


/-! # The compressed image still has order strictly larger than Delta

This upper-degree hypothesis is required by CMS Theorem 4.2. It cannot
be inferred merely from Delta being below the original source order.
Simplicity off the centre and the actual deficit budget discharge it.
-/
namespace OverfullWork.CanonicalImageDegreeRange
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

omit [Fintype V] in
theorem internal_bound_away_from_star (D : MultiGraph V) (z : V) (hStar : D.IsStarAt z)
    (S : Finset V) (hz : z∉S) : D.twiceInternal S≤S.card*(S.card-1) := by
  have hRow:∀v∈S,(∑w∈S,D.mult s(v,w))≤S.card-1:=by
    intro v hv
    have hSum:=sum_erase_add S (fun w=>D.mult s(v,w)) hv
    have hLoop:D.mult s(v,v)=0:=D.loopless _ (by simp)
    have hBound:(∑w∈S.erase v,D.mult s(v,w))≤S.card-1:=by
      calc
        _ ≤ ∑_w∈S.erase v,1 :=by
          apply sum_le_sum
          intro w hw
          exact hStar v w (fun he=>hz (he ▸ hv)) (fun he=>hz (he ▸ (mem_erase.mp hw).2))
        _ = _ :=by simp [card_erase_of_mem hv]
    omega
  calc
    _ ≤ ∑_v∈S,(S.card-1) :=sum_le_sum hRow
    _ = _ :=by simp

theorem degree_le_ordinary_order (D : MultiGraph V) (Δ B : ℕ) (z : V)
    (hdeg : ∀v,D.degree v≤Δ) (hStar : D.IsStarAt z)
    (hBudget : (∑v∈univ.erase z,(Δ-D.degree v))+D.degree z≤Δ+B)
    (hLarge : B+2≤(univ.erase z).card) : Δ≤(univ.erase z).card := by
  let S:=univ.erase z
  have hInternal:=internal_bound_away_from_star D z hStar S (notMem_erase _ _)
  have hCut:D.cutSize S=D.degree z:=by
    have hSet:S=({z}:Finset V)ᶜ:=by ext v;simp [S]
    rw [hSet,MultiGraph.cutSize_compl,CanonicalAdmissibility.cut_singleton]
  have hId:=D.sum_degree_eq_internal_add_cut S
  rw [hCut] at hId
  have hDef:(∑v∈S,(Δ-D.degree v))+(∑v∈S,D.degree v)=Δ*S.card:=by
    rw [←sum_add_distrib]
    calc
      _ = ∑_v∈S,Δ :=sum_congr rfl (fun v _=>Nat.sub_add_cancel (hdeg v))
      _ = _ :=by simp [Nat.mul_comm]
  change (∑v∈S,(Δ-D.degree v))+D.degree z≤Δ+B at hBudget
  change B+2≤S.card at hLarge
  by_contra hn
  change ¬Δ≤S.card at hn
  have hBad:S.card+1≤Δ:=by omega
  have hPositive:1≤S.card:=by omega
  have hSub:S.card-1+1=S.card:=Nat.sub_add_cancel hPositive
  have hMul:=Nat.mul_le_mul_right (S.card-1) hBad
  have hSplit:Δ*(S.card-1)+Δ=Δ*S.card:=by
    calc
      _ = Δ*(S.card-1+1) :=by ring
      _ = _ :=by rw [Nat.sub_add_cancel hPositive]
  nlinarith only [hInternal,hId,hDef,hBudget,hLarge,hMul,hSplit,hSub]

end OverfullWork.CanonicalImageDegreeRange

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 8000000

theorem Candidate.maxDegree_lt_image_order (p : Candidate c)
    (hLarge : B+2≤c.set.card) : G.maxDegree<2*(p.pairIndex+1) := by
  have hh:=CanonicalImageDegreeRange.degree_le_ordinary_order p.orderedBase G.maxDegree B
    p.centre p.ordered_degree_le p.ordered_star p.ordinary_deficit_budget
  have hCoords:=Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hCard:(univ.erase p.centre:Finset (Fin (p.pairIndex+1)×Bool)).card=c.set.card:=by
    rw [card_erase_of_mem (mem_univ _),card_univ]
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  have hOrdinary:=hh (by rwa [hCard])
  rw [hCard] at hOrdinary
  omega

theorem Candidate.maxDegree_lt_image_order_at_source_scale (p : Candidate c)
    (Q : ℕ) (hQ : 2≤Q) (hn : 64*Q≤Fintype.card V)
    (hB : B≤6*(Fintype.card V/(4096*Q^2))+6)
    (hK : K≤Fintype.card V/(4096*Q^2)+1) : G.maxDegree<2*(p.pairIndex+1) := by
  apply p.maxDegree_lt_image_order
  have hLoss:=p.local_profile_loss_at_source_scale Q hQ hn hB hK
  have hTwice:2*(B+c.setᶜ.card)≤2*(p.pairIndex+1):=
    (Nat.mul_le_mul_right (B+c.setᶜ.card) hQ).trans hLoss
  have hCoords:=Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts:=card_add_card_compl c.set
  omega

theorem Candidate.image_order_le_three_delta (p : Candidate c)
    (hWeak : Fintype.card V≤2*G.maxDegree) :
    2*(p.pairIndex+1)≤3*G.maxDegree := by
  have hCoords:=Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hCore:=card_le_univ c.set
  omega

end OverfullWork.NormalizedCanonicalCandidate
