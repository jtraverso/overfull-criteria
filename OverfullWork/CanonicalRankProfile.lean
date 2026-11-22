module

public import OverfullWork.CentredCanonicalCandidate
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section


/-! # Ordered simple-degree profile of the actual completed candidate

Ranks are zero-based. The constructed interval of preceding non-centre
vertices pays the deficit at rank r, giving the (r-1)/r profile of CMS
Theorem 4.2(1b), with the original certificate losses explicit.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 10000000

def Candidate.rank (p : Candidate c) (v : Fin (p.pairIndex+1)×Bool) : ℕ :=
  (OrderedCanonicalTransport.pairedIndex (p.pairIndex+1) v).val

theorem Candidate.ordered_rank_mono (p : Candidate c)
    (v w : Fin (p.pairIndex+1)×Bool) (hRank : p.rank v≤p.rank w) :
    p.orderedBase.degree v≤p.orderedBase.degree w := by
  obtain ⟨i,b⟩:=v
  obtain ⟨j,d⟩:=w
  have hIndex:i.val≤j.val:=by
    cases b <;> cases d <;> simp [Candidate.rank,OrderedCanonicalTransport.pairedIndex] at hRank <;> omega
  by_cases hij:i.val<j.val
  · exact p.ordered_pair_mono _ _ hij
  · have he:i=j:=Fin.ext (by omega)
    subst j
    cases b <;> cases d
    · exact le_refl _
    · simpa only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex] using p.ordered_pair i
    · simp [Candidate.rank,OrderedCanonicalTransport.pairedIndex] at hRank
    · exact le_refl _

theorem Candidate.rank_deficit_bound (p : Candidate c) (hCentre : p.centre=(0,false))
    (v : Fin (p.pairIndex+1)×Bool) :
    p.rank v*(G.maxDegree-p.orderedBase.degree v)≤G.maxDegree+B := by
  let m:=p.pairIndex+1
  let e:=OrderedCanonicalTransport.pairedIndex m
  let T:Finset (Fin m×Bool):=(Ioc (0:Fin (2*m)) (e v)).map e.symm.toEmbedding
  have hCard:T.card=p.rank v:=by simp [T,Candidate.rank,e,m]
  have hSub:T⊆univ.erase p.centre:=by
    intro u hu
    obtain ⟨j,hj,rfl⟩:=mem_map.mp hu
    refine mem_erase.mpr ⟨?_,mem_univ _⟩
    intro hh
    have he:=congrArg e hh
    change e (e.symm j)=e p.centre at he
    rw [e.apply_symm_apply,hCentre] at he
    change j=0 at he
    have hPos: (0:Fin (2*m))<j:=(mem_Ioc.mp hj).1
    rw [he] at hPos
    exact lt_irrefl _ hPos
  have hPoint:∀u∈T,G.maxDegree-p.orderedBase.degree v≤G.maxDegree-p.orderedBase.degree u:=by
    intro u hu
    obtain ⟨j,hj,rfl⟩:=mem_map.mp hu
    have hOrder:p.orderedBase.degree (e.symm j)≤p.orderedBase.degree v:=by
      apply p.ordered_rank_mono
      change (e (e.symm j)).val≤(e v).val
      rw [e.apply_symm_apply]
      exact (mem_Ioc.mp hj).2
    change G.maxDegree-p.orderedBase.degree v≤G.maxDegree-p.orderedBase.degree (e.symm j)
    omega
  have hBudget:=p.ordinary_deficit_budget
  calc
    _ = ∑_u∈T,(G.maxDegree-p.orderedBase.degree v) :=by simp [hCard,Nat.mul_comm]
    _ ≤ ∑u∈T,(G.maxDegree-p.orderedBase.degree u) :=sum_le_sum hPoint
    _ ≤ ∑u∈univ.erase p.centre,(G.maxDegree-p.orderedBase.degree u) :=
      sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _=>Nat.zero_le _)
    _ ≤ _ :=by omega

theorem Candidate.base_support_degree_le_completed (p : Candidate c)
    (v : Fin (p.pairIndex+1)×Bool) :
    p.orderedBase.supportGraph.degree v≤p.completed.supportGraph.degree v := by
  rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
  apply card_le_card
  intro w hw
  exact (mem_neighborFinset _ v w).mpr (p.completion.support_le ((mem_neighborFinset _ v w).mp hw))

/-- Integer form of CMS (1b), before division by the positive rank. -/
theorem Candidate.completed_rank_profile (p : Candidate c) (hCentre : p.centre=(0,false))
    (v : Fin (p.pairIndex+1)×Bool) (hr : 1≤p.rank v) :
    (p.rank v-1)*G.maxDegree≤p.rank v*p.completed.supportGraph.degree v+B+p.rank v*c.setᶜ.card := by
  have hv:v≠p.centre:=by
    intro hh
    rw [hh,hCentre] at hr
    simp [Candidate.rank,OrderedCanonicalTransport.pairedIndex] at hr
  have hDef:=p.rank_deficit_bound hCentre v
  have hBase:=MultiGraph.star_degree_le_support_add p.orderedBase p.centre v
    p.ordered_star hv c.setᶜ.card (p.centre_multiplicity v)
  have hMono:=p.base_support_degree_le_completed v
  have hBound:p.orderedBase.degree v≤p.completed.supportGraph.degree v+c.setᶜ.card:=by omega
  have hD:=p.ordered_degree_le v
  have hMul:=Nat.mul_le_mul_left (p.rank v) hBound
  have hDefId:p.rank v*(G.maxDegree-p.orderedBase.degree v)+p.rank v*p.orderedBase.degree v=
      p.rank v*G.maxDegree:=by rw [←Nat.mul_add,Nat.sub_add_cancel hD]
  have hRankId:(p.rank v-1)*G.maxDegree+G.maxDegree=p.rank v*G.maxDegree:=by
    calc
      _ = (p.rank v-1+1)*G.maxDegree :=by ring
      _ = _ :=by rw [Nat.sub_add_cancel hr]
  nlinarith only [hDef,hMul,hDefId,hRankId]

theorem Candidate.completed_rank_profile_real (p : Candidate c) (hCentre : p.centre=(0,false))
    (v : Fin (p.pairIndex+1)×Bool) (hr : 1≤p.rank v) :
    (((p.rank v-1:ℕ):ℝ)/(p.rank v:ℝ))*(G.maxDegree:ℝ)-((B+c.setᶜ.card:ℕ):ℝ)≤
      (p.completed.supportGraph.degree v:ℝ) := by
  have hNat:=p.completed_rank_profile hCentre v hr
  have hBudget:B≤p.rank v*B:=by nlinarith only [hr]
  have hRoom:(p.rank v-1)*G.maxDegree≤p.rank v*(p.completed.supportGraph.degree v+B+c.setᶜ.card):=by
    nlinarith only [hNat,hBudget]
  have hCast:((p.rank v-1:ℕ):ℝ)*(G.maxDegree:ℝ)≤
      (p.rank v:ℝ)*((p.completed.supportGraph.degree v:ℝ)+(B:ℝ)+(c.setᶜ.card:ℝ)):=by exact_mod_cast hRoom
  have hPositive:(0:ℝ)<p.rank v:=by exact_mod_cast (show 0<p.rank v by omega)
  apply (sub_le_iff_le_add).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hPositive).mpr
  push_cast
  nlinarith only [hCast]

end OverfullWork.NormalizedCanonicalCandidate
