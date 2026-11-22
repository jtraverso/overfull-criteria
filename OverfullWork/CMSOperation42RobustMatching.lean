module

public import OverfullWork.RealRobustSpanningLinkage
public import OverfullWork.EvenHamiltonFactorization
public import OverfullWork.CMSOperation41ProjectedLayers

@[expose] public section


/-! The even ordinary core in CMS Operation 4.2 receives a perfect
matching from the robust Hamilton linkage theorem. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion
open scoped Classical
universe u

theorem perfect_matching_of_even_robust_core (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → IsRealRobust G ν τ →
      α*(Fintype.card V:ℝ) ≤ (G.minDegree:ℝ) →
      Even (Fintype.card V) → ∃ J : SimpleGraph V, J ≤ G ∧ ∀ v, J.degree v = 1 := by
  obtain ⟨N,hN⟩ := RobustSpanningLinkage.cms_lemma_3_15.{u} ν τ α hν hντ hτα hα
  obtain ⟨M,hM⟩ := exists_nat_ge (1/ν^4)
  refine ⟨max (max N M) 2,?_⟩
  intro V _ _ G _ hn hR hMin hEven
  have hN' : N ≤ Fintype.card V := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hM' : (M:ℝ) ≤ Fintype.card V := by
    exact_mod_cast (le_max_right N M).trans ((le_max_left _ _).trans hn)
  have hBound : (1:ℝ) ≤ ν^4*(Fintype.card V:ℝ) := by
    have h := (div_le_iff₀ (show 0 < ν^4 by positivity)).mp (hM.trans hM')
    linarith only [h]
  have hTwo : 2 ≤ Fintype.card V := (le_max_right _ _).trans hn
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,b,hab⟩ := exists_pair_ne V
  obtain ⟨P,hP,_,hSpan⟩ := hN G hN' hR hMin (p := 1) (by decide) (by exact_mod_cast hBound)
    (fun _ => a) (fun _ => b) (fun i j _ => Subsingleton.elim i j)
    (fun i j _ => Subsingleton.elim i j) (fun _ _ => hab)
  exact EvenHamiltonFactorization.one_factor_of_spanning_path (P 0) (hP 0)
    (fun v => by obtain ⟨i,hi⟩ := hSpan v; rwa [Subsingleton.elim i 0] at hi)
    hab hEven

theorem exists_matching_on_even_robust_core (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
      N ≤ S.card → Even S.card → IsRealRobust (G.induce (S:Set V)) ν τ →
      α*(S.card:ℝ) ≤ ((G.induce (S:Set V)).minDegree:ℝ) →
      ∃ J : SimpleGraph V, Plantholt.IsMatchingOn G J S := by
  obtain ⟨N,hN⟩ := perfect_matching_of_even_robust_core.{u} ν τ α hν hντ hτα hα
  refine ⟨N,?_⟩
  intro V _ _ G _ S hN' hEven hR hMin
  have hCard : Fintype.card ↥(S : Set V) = S.card := Fintype.card_coe S
  obtain ⟨J,hLe,hD⟩ := hN (G.induce (S:Set V)) (by rwa [hCard]) hR
    (by rwa [hCard]) (by rwa [hCard])
  let w : ↥(S : Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  refine ⟨J.map w,?_,?_,?_⟩
  · intro u v h
    obtain ⟨x,y,hxy,rfl,rfl⟩ := (map_adj w J u v).mp h
    exact hLe hxy
  · intro v hv
    exact (CMSTrimmingRound.map_degree_at_embedding J w (dMap := Classical.decRel _) ⟨v,hv⟩).trans
      (hD ⟨v,hv⟩)
  · intro v hv
    exact CMSTrimmingRound.map_degree_outside_embedding J w (dMap := Classical.decRel _) v
      (fun ⟨x,hx⟩ => hv (hx ▸ x.property))

end OverfullWork.CMSMatchingRemoval
