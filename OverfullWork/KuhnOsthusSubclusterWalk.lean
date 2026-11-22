module

public import OverfullWork.KuhnOsthusUniversalWalkOrdering

@[expose] public section


/-! Kühn–Osthus (ST2). Index the fine cells by the occurrences of
their coarse cluster in the universal walk. -/
namespace OverfullWork.DirectedRobustExpansion

/-- Every occurrence of a coarse cluster in the universal walk is
assigned a distinct fine index. The fine successor visits every
fine index exactly once and projects to the original walk. -/
theorem exists_universal_subcluster_walk {I : Type*} {L : ℕ} (F : Fin L → Equiv.Perm I)
    (hWalk : HasSpanningCycle (fun e f : (Σ _ : Fin L, I) => F e.1 e.2 = f.2)) :
    ∃ ρ : Equiv.Perm (Fin L × I), (∀ a, (ρ a).2 = F a.1 a.2) ∧
      HasSpanningCycle (fun a b => ρ a = b) := by
  let e := Equiv.sigmaEquivProd (Fin L) I
  obtain ⟨s,hs,T,x,hN,hAll,hHead,hChain⟩ := exists_spanning_successor hWalk
  refine ⟨e.permCongr s,fun a => (hs (e.symm a)).symm,T.map e,e x,
    hN.map e.injective,?_,?_,?_⟩
  · intro a
    exact List.mem_map.mpr ⟨e.symm a,hAll _,e.apply_symm_apply a⟩
  · rw [List.head?_map,hHead]
    rfl
  · rw [← List.map_singleton,← List.map_append]
    apply List.isChain_map_of_isChain e _ hChain
    intro a b h
    rw [Equiv.permCongr_apply,e.symm_apply_apply,h]

end OverfullWork.DirectedRobustExpansion
