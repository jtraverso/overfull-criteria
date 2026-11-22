module

public import OverfullWork.KuhnOsthusPhysicalChordBalance
public import OverfullWork.KuhnOsthusOriginalInterval
public import OverfullWork.KuhnOsthusExceptionalContraction

@[expose] public section


/-! CEPS1 and CEPS3 of Kühn–Osthus. Cutting the interval at its
first and last cells gives the equal local source and target counts
used in Lemma 9.5. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedDemandHall
open scoped Classical
variable {V I : Type*} [Fintype V]

private theorem mem_physical_cell {Z : Finset V} (X : Finset ↥Zᶜ) (v : ↥Zᶜ) :
    v.val ∈ X.map (Function.Embedding.subtype (· ∈ Zᶜ)) ↔ v ∈ X := by
  rw [mem_map]
  constructor
  · rintro ⟨w,hw,he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · exact fun h => ⟨v,h,rfl⟩

/-- A complete exceptional interval with equal cells has balanced
arc counts in the basic digraph. Its footprint in each coarse
cluster is at most one cell. -/
theorem complete_exceptional_interval_arc_counts {n m : ℕ}
    (G : Digraph V) (Z : Finset V) (c : ↥Zᶜ → I) (s : Equiv.Perm I)
    (loc : Fin (n+2) → I) (X : Fin (n+2) → Finset ↥Zᶜ)
    (hLoc : Function.Injective loc)
    (hStep : ∀ j : Fin (n+1), loc j.succ = s (loc j.castSucc))
    (hC : ∀ j v, v ∈ X j → c v = loc j)
    (hSize : ∀ j, (X j).card = m)
    (Q : OriginalInterval G Z
      ((univ.biUnion X).map (Function.Embedding.subtype (· ∈ Zᶜ)))
      ((X 0).map (Function.Embedding.subtype (· ∈ Zᶜ)))
      ((X (Fin.last (n+1))).map (Function.Embedding.subtype (· ∈ Zᶜ)))) :
    let D := basicExceptionalPathSystem Q.digraph Z
    (∀ x, (∑ a : Arc D, if c a.val.1 = x then (1:ℕ) else 0) =
      ∑ a : Arc D, if c a.val.2 = s x then (1:ℕ) else 0) ∧
    ∀ x, (finiteSatisfying (fun v => c v = x ∧ IncidentTo D v)).card ≤ m := by
  intro D
  have hApart (j k : Fin (n+2)) (hne : j ≠ k) : Disjoint (X j) (X k) := by
    rw [disjoint_left]
    intro v hv hv'
    exact hne (hLoc ((hC _ _ hv).symm.trans (hC _ _ hv')))
  have hOut (v : ↥Zᶜ) : (∃ w, D.Adj v w) ↔ ∃ j : Fin (n+1), v ∈ X j.castSucc := by
    rw [(basic_exceptional_endpoint_slots Q.digraph Z Q.cover (fun _ _ => Q.no_internal) v).1,
      (Q.slots v.val (mem_compl.mp v.prop)).1]
    simp only [mem_sdiff,mem_physical_cell,mem_biUnion,mem_univ,true_and]
    constructor
    · rintro ⟨⟨j,hj⟩,hLast⟩
      revert hj
      exact Fin.lastCases (fun he => (hLast he).elim) (fun i he => ⟨i,he⟩) j
    · rintro ⟨j,hj⟩
      exact ⟨⟨_,hj⟩,fun he => disjoint_left.mp (hApart _ _ j.castSucc_lt_last.ne) hj he⟩
  have hIn (v : ↥Zᶜ) : (∃ w, D.Adj w v) ↔ ∃ j : Fin (n+1), v ∈ X j.succ := by
    rw [(basic_exceptional_endpoint_slots Q.digraph Z Q.cover (fun _ _ => Q.no_internal) v).2,
      (Q.slots v.val (mem_compl.mp v.prop)).2]
    simp only [mem_sdiff,mem_physical_cell,mem_biUnion,mem_univ,true_and]
    constructor
    · rintro ⟨⟨j,hj⟩,hFirst⟩
      revert hj
      exact Fin.cases (fun he => (hFirst he).elim) (fun i he => ⟨i,he⟩) j
    · rintro ⟨j,hj⟩
      exact ⟨⟨_,hj⟩,fun he => disjoint_left.mp (hApart _ _ j.succ_ne_zero) hj he⟩
  have hD : IsDirectedPathSystem D := basicExceptionalPathSystem.isDirectedPathSystem Q.path_system
  constructor
  · intro x
    let S := finiteSatisfying (fun j : Fin (n+1) => loc j.castSucc = x)
    have hOS : finiteSatisfying (fun v => c v = x ∧ ∃ w, D.Adj v w) = S.biUnion (fun j => X j.castSucc) := by
      ext v
      simp only [mem_finiteSatisfying,hOut,mem_biUnion,S]
      exact ⟨fun ⟨hx,j,hj⟩ => ⟨j,(hC _ _ hj).symm.trans hx,hj⟩,
        fun ⟨j,hj,hv⟩ => ⟨(hC _ _ hv).trans hj,j,hv⟩⟩
    have hIS : finiteSatisfying (fun v => c v = s x ∧ ∃ w, D.Adj w v) = S.biUnion (fun j => X j.succ) := by
      ext v
      simp only [mem_finiteSatisfying,hIn,mem_biUnion,S]
      exact ⟨fun ⟨hx,j,hj⟩ => ⟨j,s.injective ((hStep j).symm.trans ((hC _ _ hj).symm.trans hx)),hj⟩,
        fun ⟨j,hj,hv⟩ => ⟨(hC _ _ hv).trans ((hStep j).trans (congrArg s hj)),j,hv⟩⟩
    rw [(path_arc_endpoint_counts D hD (fun v => c v = x)).1,
      (path_arc_endpoint_counts D hD (fun v => c v = s x)).2,hOS,hIS]
    rw [card_biUnion (fun i _ j _ h => hApart _ _ (fun he => h (Fin.castSucc_injective _ he))),
      card_biUnion (fun i _ j _ h => hApart _ _ (fun he => h (Fin.succ_injective _ he)))]
    simp only [hSize]
  · intro x
    have hSupport (v : ↥Zᶜ) (hv : IncidentTo D v) : ∃ j, v ∈ X j := by
      rcases hv with hv | hv
      · obtain ⟨j,hj⟩ := (hOut v).mp hv
        exact ⟨_,hj⟩
      · obtain ⟨j,hj⟩ := (hIn v).mp hv
        exact ⟨_,hj⟩
    by_cases h : ∃ j, loc j = x
    · obtain ⟨j,hj⟩ := h
      have hSub : finiteSatisfying (fun v => c v = x ∧ IncidentTo D v) ⊆ X j := by
        intro v hv
        obtain ⟨hc,hd⟩ := (mem_finiteSatisfying (p := fun v => c v = x ∧ IncidentTo D v)).mp hv
        obtain ⟨k,hk⟩ := hSupport v hd
        exact (hLoc ((hC _ _ hk).symm.trans (hc.trans hj.symm))) ▸ hk
      exact (card_le_card hSub).trans_eq (hSize j)
    · have hEmpty : finiteSatisfying (fun v => c v = x ∧ IncidentTo D v) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨hc,hd⟩ := (mem_finiteSatisfying (p := fun v => c v = x ∧ IncidentTo D v)).mp hv
        obtain ⟨k,hk⟩ := hSupport v hd
        exact h ⟨k,(hC _ _ hk).symm.trans hc⟩
      simp [hEmpty]

end OverfullWork.DirectedRobustExpansion
