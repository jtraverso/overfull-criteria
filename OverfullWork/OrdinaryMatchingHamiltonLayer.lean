module

public import OverfullWork.OrdinaryMatchingEndpoints

@[expose] public section


/-! One prescribed parallel matching is absorbed into an even
Hamilton cycle in the ordinary support of CMS §5.2, Case 1. -/
namespace OverfullWork.EvenHamiltonFactorization

open SimpleGraph MultiGraph PathGraphRealization
open scoped Classical
universe u

/-- Use CMS Lemma 3.15 on the cyclically shifted endpoints of a
nonempty matching. The support edges remain a simple graph below the
given host. Each extra copy in the matching is retained in the layer. -/
theorem exists_coloured_hamilton_layer_through_matching
    (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (J : MultiGraph V),
      N ≤ Fintype.card V → Even (Fintype.card V) → RobustExpansion.IsRealRobust G ν τ →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (G.degree v:ℝ)) → (∀ v, J.degree v ≤ 1) →
      0 < J.edgeCount → (J.edgeCount:ℝ) ≤ ν^4*(Fintype.card V:ℝ) →
      ∃ F : SimpleGraph V, F ≤ G ∧
        let L := (ofSimpleGraph F).addCopies J
        L.IsRegularOfDegree 2 ∧ Nonempty (L.EdgeColoring 2) := by
  obtain ⟨N,hN⟩ := RobustSpanningLinkage.exists_spanning_linkage_threshold.{u} ν τ α
    hν (by linarith only [hντ,hτα,hα]) hντ hτα hα
  refine ⟨N,?_⟩
  intro V _ _ G _ J hSize hEven hRob hDegree hMatch hNonempty hCount
  obtain ⟨k,hk⟩ : ∃ k, J.edgeCount = k+1 := ⟨J.edgeCount-1,by omega⟩
  let e : Fin (k+1) ≃ Fin J.edgeCount := finCongr hk.symm
  obtain ⟨a₀,b₀,ha,hb,hab,hJoin,hEndpoints⟩ := exists_matching_endpoint_enumeration J hMatch
  let a := a₀ ∘ e
  let b := b₀ ∘ e
  let rot := finRotate (k+1)
  have hCount' : ((k+1:ℕ):ℝ) ≤ ν^4*(Fintype.card V:ℝ) := by
    rwa [←hk]
  obtain ⟨P,hPath,hDisj,hSpan⟩ := hN G hSize hRob hDegree (p := k+1) (by omega) hCount'
    b (a ∘ rot) (hb.comp e.injective) ((ha.comp e.injective).comp rot.injective)
    (fun i j => (hab (e (rot j)) (e i)).symm)
  have hEnd (w : V) : (∃ j, w = a₀ j ∨ w = b₀ j) ↔ ∃ j, w = a j ∨ w = b j := by
    constructor
    · rintro ⟨j,hj⟩
      obtain ⟨i,rfl⟩ := e.surjective j
      exact ⟨i,hj⟩
    · rintro ⟨i,hi⟩
      exact ⟨e i,hi⟩
  have hCover (i : Fin (k+1)) (v : V) (hv : v ∈ (P i).support) :
      J.degree v = if v = b i ∨ v = a (rot i) then 1 else 0 := by
    have hLocal : (∃ j, v = a j ∨ v = b j) ↔ v = b i ∨ v = a (rot i) := by
      constructor
      · rintro ⟨j,hj | hj⟩
        · have hv' : v ∈ (P (rot.symm j)).support := by
            rw [hj]
            simpa only [Function.comp_apply,Equiv.apply_symm_apply] using
              Walk.end_mem_support (P (rot.symm j))
          have he : i = rot.symm j := by
            by_contra h
            exact hDisj i _ h v hv hv'
          rw [he,rot.apply_symm_apply]
          exact Or.inr hj
        · have hv' : v ∈ (P j).support := by
            rw [hj]
            exact Walk.start_mem_support (P j)
          have he : i = j := by
            by_contra h
            exact hDisj i _ h v hv hv'
          exact Or.inl (he.symm ▸ hj)
      · rintro (h | h)
        · exact ⟨i,Or.inr h⟩
        · exact ⟨rot i,Or.inl h⟩
    have hPair := (hEnd v).trans hLocal
    by_cases hAt : v = b i ∨ v = a (rot i)
    · rw [hEndpoints,if_pos (hPair.mpr hAt),if_pos hAt]
    · rw [hEndpoints,if_neg (fun h => hAt (hPair.mp h)),if_neg hAt]
  refine ⟨pathUnion P,pathUnion_le_original P,?_⟩
  exact colourable_layer_of_cyclic_linkage k a b P hPath hDisj hSpan
    (fun i => (hab (e (rot i)) (e i)).symm) J (fun i => hJoin (e i)) hCover hEven

end OverfullWork.EvenHamiltonFactorization
