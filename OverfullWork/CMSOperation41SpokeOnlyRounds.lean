module

public import OverfullWork.CMSOperation41SmallPrescriptions
public import OverfullWork.CMSOperation41PhysicalLayerFamily
public import OverfullWork.CMSOperation41RetiredPool

@[expose] public section


/-! The branches whose prescriptions consist only of two-edge spokes.
Their expanded length is known before any paths in the core are packed. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2000000 in
theorem exists_spoke_only_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (U B omitted : Finset V) (hBU : B ⊆ U)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hDegree : ∀ v ∈ B,U.card+omitted.card+k+2*B.card ≤ G.degree v) :
    ∃ R : TrimmingReplacementWords G U (Fin B.card), R.gaps = ∅ ∧
      (∑ i,(R.body i).length) = B.card ∧
      (∀ i : Fin B.card × Bool,(R.endpoint i).val ∉ omitted) ∧
      (∀ i : Fin B.card × Bool,projectionLoad (range j) used (R.endpoint i).val < cap) ∧
      (∀ i,(R.body i).length = 1) ∧ (∀ v,(∃ i,v ∈ R.body i) ↔ v ∈ B) := by
  let empty := TrimmingReplacementWords.empty G U
  obtain ⟨T,hGap,_,_,hBody,hAvoid,hFresh⟩ := empty.exists_with_retired_spokes B omitted hBU
    (fun i => i.elim0) (fun i => i.1.elim0) used j cap k budget hCap hUsed hTotal
    (by simpa only [Fintype.card_fin,mul_zero,add_zero] using hDegree)
  let e : Fin B.card ≃ Fin 0 ⊕ ↥B := (Fintype.equivFinOfCardEq (by simp)).symm
  let R := T.reindex e
  have hLen (i : Fin B.card) : (R.body i).length = 1 := by
    change (T.body (e i)).length = 1
    cases h : e i with
    | inl a => exact a.elim0
    | inr z => rw [hBody]; rfl
  refine ⟨R,hGap,by simp [hLen],?_,?_,hLen,?_⟩
  · intro i
    exact hAvoid (e i.1,i.2)
  · rintro ⟨i,side⟩
    change projectionLoad (range j) used (T.endpoint (e i,side)).val < cap
    cases h : e i with
    | inl a => exact a.elim0
    | inr z => exact hFresh z side
  · intro v
    constructor
    · rintro ⟨i,hi⟩
      change v ∈ T.body (e i) at hi
      cases h : e i with
      | inl a => exact a.elim0
      | inr z =>
        rw [h,hBody,List.mem_singleton] at hi
        exact hi.symm ▸ z.property
    · intro h
      let z : ↥B := ⟨v,h⟩
      refine ⟨e.symm (Sum.inr z),?_⟩
      change v ∈ T.body (e (e.symm (Sum.inr z)))
      rw [Equiv.apply_symm_apply,hBody]
      exact List.mem_cons_self

/-- The even-core branch S2.3 adds a spoke at each surviving retired
vertex. It needs no additional parity gap. -/
theorem exists_even_core_spoke_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (initial current active : Finset V) (hCurrent : current ⊆ initial) (hCore : initialᶜ ⊆ active)
    (hEven : Even (active\current).card)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hDegree : ∀ v ∈ retiredTrimmingPool initial current active,
      initial.card+k+2*(retiredTrimmingPool initial current active).card ≤ G.degree v) :
    let B := retiredTrimmingPool initial current active
    ∃ R : TrimmingReplacementWords G initial (Fin B.card),R.gaps = ∅ ∧
      Even (initialᶜ.card+∑ i,(R.body i).length) ∧
      ∀ i : Fin B.card × Bool,projectionLoad (range j) used (R.endpoint i).val < cap := by
  intro B
  have hBU : B ⊆ initial := fun _ h => (mem_inter.mp (mem_sdiff.mp h).1).2
  obtain ⟨R,hGap,hLength,_,hFresh,_,_⟩ := exists_spoke_only_round G initial B ∅ hBU used j cap k budget
    hCap hUsed hTotal (by simpa using hDegree)
  have hParity := (trimming_parity_for_retired_spokes initial current active hCurrent hCore).1
  refine ⟨R,hGap,?_,hFresh⟩
  rw [hLength,hParity]
  exact hEven

end OverfullWork.CMSTrimmingRound
