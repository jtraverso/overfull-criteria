module

public import OverfullWork.RegularHeavyCutRepair
public import OverfullWork.BipartiteScaleParameters

@[expose] public section


/-! # Construct and adjust a robust cut of the actual completed support

All graph-theoretic inputs of the repair are discharged for the same
canonical candidate. The explicit finite scale hypotheses are paid
from source parameters in the subsequent uniform interface.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun PrunedCore RobustExpansion BipartiteRobustMargin
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 12000000

theorem Candidate.exists_completed_support_robust_cut (p : Candidate c) (P : ℕ) (hP : 2 ≤ P)
    (hm : 2^50*P^4 ≤ p.pairIndex+1)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1))
    (hB : B ≤ (p.pairIndex+1)/(1024*P))
    (hDense : p.pairIndex+1+16*((p.pairIndex+1)/(1024*P))+4 ≤ G.maxDegree)
    (b : Fin (p.pairIndex+1) × Bool) (hab : p.centre ≠ b)
    (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hξcap : ξ ≤ ((p.pairIndex+1:ℕ):ℝ)/(1024*(P:ℝ)))
    (hMoment : 30*((p.pairIndex+1:ℕ):ℝ)^4 < ξ^6) :
    ∃ A : Finset (Fin (p.pairIndex+1) × Bool),
      A.card = p.pairIndex+1 ∧ Aᶜ.card = p.pairIndex+1 ∧ p.centre ∈ A ∧ b ∉ A ∧
      IsBipartiteRobustAt p.completed.supportGraph A
        ((p.pairIndex+1)/(2^30*P^3)) ((p.pairIndex+1)/(1024*P)) ∧
      ∀ v, |(neighboursIn p.completed.supportGraph A v:ℝ)-
        (neighboursIn p.completed.supportGraph Aᶜ v:ℝ)| < ξ := by
  let m := p.pairIndex+1
  let q := m/(1024*P)
  let r := m/(2^30*P^3)
  let δ := (m+1)/2+q
  let e := 1+2*G.maxDegree/(q+1)
  have hE : (p.completedBundleExceptions q).card ≤ e := by
    have hh := p.completedBundleExceptions_card q
    have hd : G.maxDegree/(q+1) ≤ (2*G.maxDegree)/(q+1) :=
      Nat.div_le_div_right (show G.maxDegree ≤ 2*G.maxDegree by omega)
    dsimp only [e]
    omega
  have hDef : ∀ v, v ∉ p.completedBundleExceptions q →
      G.maxDegree-p.completed.supportGraph.degree v ≤ q+B := by
    intro v hv
    have hvc : v ≠ p.centre := by intro he;subst v;exact hv (mem_insert_self _ _)
    have hBundle : p.completed.mult s(p.centre,v) ≤ q := by
      by_contra hn
      exact hv (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,by omega⟩))
    have hh := p.completed_neighbour_profile v hvc
    omega
  obtain ⟨hRoom,hδ,hMargin,hr,hrq,hrt,hScale⟩ :=
    BipartiteScaleParameters.bounds P m G.maxDegree 0 B (by omega) hm hD (Nat.zero_le _) hB hDense
  simp only [Nat.add_zero] at hrt hScale
  have hξRoom : 2*(δ:ℝ)+ξ+3*((q+B:ℕ):ℝ) ≤ G.maxDegree := by
    change 2*(δ:ℝ)+(m:ℝ)/(1024*(P:ℝ))+3*((q+B:ℕ):ℝ) ≤ G.maxDegree at hRoom
    change ξ ≤ (m:ℝ)/(1024*(P:ℝ)) at hξcap
    linarith
  apply RegularSupportRobustCut.exists_cut p.completed G.maxDegree m p.centre b hab
    (by omega) (by simp [m,Nat.mul_comm]) p.completion.regular
    (p.completedBundleExceptions q) e (q+B) δ q r q ξ hξ hMoment hE hDef hξRoom
    hδ hMargin hr hrq hrt hScale

theorem Candidate.exists_case_two_adjusted_cut (p : Candidate c) (P T : ℕ)
    (hP : 2 ≤ P) (hT : 1 ≤ T) (hm : 2^50*P^4 ≤ p.pairIndex+1)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1))
    (hB : B ≤ (p.pairIndex+1)/(1024*P))
    (hDense : p.pairIndex+1+16*((p.pairIndex+1)/(1024*P))+4 ≤ G.maxDegree)
    (hReserve : 2*(3*T+1) < (p.pairIndex+1)/(2^30*P^3))
    (hRoom : 3*T+1 ≤ p.pairIndex+1)
    (b : Fin (p.pairIndex+1) × Bool) (hab : p.centre ≠ b)
    (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hξcap : ξ ≤ ((p.pairIndex+1:ℕ):ℝ)/(1024*(P:ℝ)))
    (hMoment : 30*((p.pairIndex+1:ℕ):ℝ)^4 < ξ^6) :
    ∃ A : Finset (Fin (p.pairIndex+1) × Bool),
      A.card = p.pairIndex+1 ∧ Aᶜ.card = p.pairIndex+1 ∧ p.centre ∈ A ∧ b ∉ A ∧
      (∀ v, v ≠ b → (p.pairIndex+1)/T < p.completed.mult s(p.centre,v) → v ∉ A) ∧
      2*p.completed.degreeInto A p.centre ≤ G.maxDegree ∧
      IsBipartiteRobustAt p.completed.supportGraph A
        ((p.pairIndex+1)/(2^30*P^3)-2*(3*T+1)) ((p.pairIndex+1)/(1024*P)+(3*T+1)) ∧
      (0 < (p.pairIndex+1)/(2^30*P^3)-2*(3*T+1)) ∧
      ∀ v, |(neighboursIn p.completed.supportGraph A v:ℝ)-
        (neighboursIn p.completed.supportGraph Aᶜ v:ℝ)| < ξ+2*((3*T+1:ℕ):ℝ) := by
  obtain ⟨A,hA,hAc,ha,hb,hRobust,hDis⟩ := p.exists_completed_support_robust_cut
    P hP hm hD hB hDense b hab ξ hξ hξcap hMoment
  have hCount := RegularHeavyCutRepair.heavySet_card_at_scale p.completed p.centre b
    G.maxDegree (p.pairIndex+1) T p.completion.regular hD hT
  obtain ⟨A',hA',hAc',ha',hb',hAcross,hHalf,hRobust',hDis'⟩ :=
    RegularHeavyCutRepair.exists_adjusted_cut p.completed G.maxDegree (p.pairIndex+1)
      ((p.pairIndex+1)/T) (3*T+1) ((p.pairIndex+1)/(2^30*P^3))
      ((p.pairIndex+1)/(1024*P)) p.completion.regular p.centre b A hA hAc ha hb
      (by omega) hRoom (by omega) ξ hDis hRobust
  exact ⟨A',hA',hAc',ha',hb',hAcross,hHalf,hRobust',by omega,hDis'⟩

end OverfullWork.NormalizedCanonicalCandidate
