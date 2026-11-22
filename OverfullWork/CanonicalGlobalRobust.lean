module

public import OverfullWork.GlobalRobustMargin

@[expose] public section


/-! # Global robustness of the actual completed support

The exceptional set is constructed from heavy completed centre bundles.
Its size is paid by the actual regular centre degree. The finite scales
reuse the already proved counting estimates for the dense regime.
-/
namespace OverfullWork.CanonicalGlobalRobust
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 12000000

def heavyNeighbours (M : MultiGraph V) (z : V) (s : ℕ) : Finset V :=
  univ.filter fun v=>s<M.mult s(z,v)

theorem heavyNeighbours_card (M : MultiGraph V) (z : V) (s D : ℕ)
    (hDegree : M.degree z=D) : (heavyNeighbours M z s).card≤D/(s+1) := by
  have h₁:(s+1)*(heavyNeighbours M z s).card≤∑v∈heavyNeighbours M z s,M.mult s(z,v):=by
    calc
      _ = ∑_v∈heavyNeighbours M z s,(s+1) :=by simp [Nat.mul_comm]
      _ ≤ _ :=by
        apply sum_le_sum
        intro v hv
        have hh:=(mem_filter.mp hv).2
        omega
  have h₂:(∑v∈heavyNeighbours M z s,M.mult s(z,v))≤D:=by
    calc
      _ ≤ ∑v:V,M.mult s(z,v) :=sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)
      _ = D :=by rw [←M.degree_eq_sum_mult,hDegree]
  apply (Nat.le_div_iff_mul_le (by omega : 0<s+1)).mpr
  nlinarith only [h₁,h₂]

theorem source_budget_le_four_q (P n m B Y : ℕ) (hP : 2≤P) (hm : 2^50*P^4≤m)
    (hCard : n+1=2*m+Y) (hY : Y≤n/(4096*P^2)+1)
    (hB : B≤6*(n/(4096*P^2))+6) : B≤4*(m/(1024*P)) := by
  let k:=n/(4096*P^2)
  let q:=m/(1024*P)
  have hk:4096*P^2*k≤n:=Nat.mul_div_le n (4096*P^2)
  have hCoef:4096*P+1≤4096*P^2:=by nlinarith only [hP]
  have hMul:=Nat.mul_le_mul_right k hCoef
  change Y≤k+1 at hY
  change B≤6*k+6 at hB
  have hkM:2048*P*k≤m:=by nlinarith only [hk,hMul,hY,hCard]
  have hkq:2*k≤q:=by
    apply (Nat.le_div_iff_mul_le (show 0<1024*P by positivity)).mpr
    nlinarith only [hkM]
  have hPow:P≤P^4:=by simpa only [pow_one] using Nat.pow_le_pow_right (show 0<P by omega) (by decide : 1≤4)
  have hq:6≤q:=by
    apply (Nat.le_div_iff_mul_le (show 0<1024*P by positivity)).mpr
    nlinarith only [hm,hPow]
  change B≤4*q
  omega

end OverfullWork.CanonicalGlobalRobust

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun CanonicalGlobalRobust
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 12000000

noncomputable def Candidate.completedBundleExceptions (p : Candidate c) (s : ℕ) :
    Finset (Fin (p.pairIndex+1)×Bool) := insert p.centre (heavyNeighbours p.completed p.centre s)

theorem Candidate.completedBundleExceptions_card (p : Candidate c) (s : ℕ) :
    (p.completedBundleExceptions s).card≤1+G.maxDegree/(s+1) := by
  have hh:=heavyNeighbours_card p.completed p.centre s G.maxDegree (p.completion.regular p.centre)
  have hI:=card_insert_le p.centre (heavyNeighbours p.completed p.centre s)
  change (insert p.centre (heavyNeighbours p.completed p.centre s)).card≤_
  omega

theorem Candidate.good_completed_degree (p : Candidate c) (s δ : ℕ)
    (hRoom : δ+s+B≤G.maxDegree) (v : Fin (p.pairIndex+1)×Bool)
    (hv : v∉p.completedBundleExceptions s) : δ≤p.completed.supportGraph.degree v := by
  have hCentre:v≠p.centre:=by intro he;subst v;exact hv (mem_insert_self _ _)
  have hBundle:p.completed.mult s(p.centre,v)≤s:=by
    by_contra hn
    exact hv (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,by omega⟩))
  have hh:=p.completed_neighbour_profile v hCentre
  omega

theorem Candidate.global_robust_at_scales (p : Candidate c) (P : ℕ) (hP : 2≤P)
    (hm : 2^50*P^4≤p.pairIndex+1)
    (hD : G.maxDegree≤3*(p.pairIndex+1))
    (hB : B≤4*((p.pairIndex+1)/(1024*P)))
    (hDense : p.pairIndex+1+16*((p.pairIndex+1)/(1024*P))+4≤G.maxDegree) :
    RobustExpansion.IsRobustAt p.completed.supportGraph
      ((p.pairIndex+1)/(2^30*P^3)) ((p.pairIndex+1)/(1024*P)) ∧
      (0<(p.pairIndex+1)/(2^30*P^3) ∧ 2*((p.pairIndex+1)/(1024*P))≤2*(p.pairIndex+1)) := by
  let m:=p.pairIndex+1
  let q:=m/(1024*P)
  let r:=m/(2^30*P^3)
  let a:=1+G.maxDegree/(q+1)
  let a₀:=1+(2*G.maxDegree)/(q+1)
  obtain ⟨hRoom,hδ,hMargin,hr,hrq,hBudget,hScale⟩:=BipartiteScaleParameters.bounds
    P m G.maxDegree 0 0 (by omega) hm hD (Nat.zero_le _) (Nat.zero_le _) hDense
  simp only [Nat.add_zero] at hBudget hScale
  have ha:a≤a₀:=by
    have hh:G.maxDegree/(q+1)≤(2*G.maxDegree)/(q+1):=
      Nat.div_le_div_right (show G.maxDegree≤2*G.maxDegree by omega)
    dsimp only [a,a₀]
    omega
  have hq:2*q≤m:=by
    have hh:=Nat.mul_div_le m (1024*P)
    change (1024*P)*q≤m at hh
    have hc:2≤1024*P:=by omega
    exact (Nat.mul_le_mul_right q hc).trans hh
  refine ⟨?_,hr,by omega⟩
  apply GlobalRobustMargin.isRobustAt_of_margin p.completed.supportGraph
    (p.completedBundleExceptions q) (2*m) (m+2*q) (2*q) r q a
  · simp [m,Nat.mul_comm]
  · exact p.completedBundleExceptions_card q
  · apply p.good_completed_degree q (m+2*q)
    change B≤4*q at hB
    change m+16*q+4≤G.maxDegree at hDense
    omega
  · omega
  · omega
  · exact hr
  · omega
  · change r+a₀≤q at hBudget
    omega
  · change 4*r*m+2*m*a₀≤q*q at hScale
    have hh:=Nat.mul_le_mul_left (4*m) ha
    nlinarith only [hScale,hh]

end OverfullWork.NormalizedCanonicalCandidate
