module

public import OverfullWork.DirectedLayoutOneRound
public import OverfullWork.DirectedBatchResidual

@[expose] public section


/-! The payment for reserve arcs in one constructed round of GGKLO (7.2). -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveStitching InducedDigraphSampling
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

noncomputable def Realization.shortVertices {K : Digraph V} {L : Layout V I}
    (R : Realization K L) (long : I) : Finset V :=
  (univ \ insert long L.fixed).biUnion fun i => (R.interior i).toFinset

/-- A vertex pays nothing for reserve arcs unless it is a flexible
endpoint, a short interior, or belongs to the assigned block. -/
theorem Realization.reserve_cost {K D Γ : Digraph V} {L : Layout V I}
    (R : Realization K L) (long : I) (A : Finset V)
    (hDΓ : Disjoint D Γ)
    (hLong : wordGraph (R.word long) ≤ mixed D (induced Γ A) ⟨Subtype.val,Subtype.val_injective⟩)
    (v : V) :
    inDegree (R.used ⊓ Γ) v+outDegree (R.used ⊓ Γ) v ≤
      L.endpointLoad true v+L.endpointLoad false v+
        (if v ∈ R.shortVertices long then 2 else 0)+(if v ∈ A then 2 else 0) := by
  letI : DecidableRel (R.used ⊓ Γ).Adj := fun _ _ => Classical.propDecidable _
  have hIn : inDegree (R.used ⊓ Γ) v ≤ inDegree R.used v := by
    apply card_le_card
    exact fun x hx => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2.1⟩
  have hOut : outDegree (R.used ⊓ Γ) v ≤ outDegree R.used v := by
    apply card_le_card
    exact fun x hx => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2.1⟩
  obtain ⟨hi,ho⟩ := R.semidegrees_used v
  by_cases hv : v ∈ L.boundary
  · simp only [if_pos hv] at hi ho
    change inDegree R.used v = L.endpointLoad true v at hi
    change outDegree R.used v = L.endpointLoad false v at ho
    omega
  simp only [if_neg hv] at hi ho
  by_cases hA : v ∈ A
  · rw [if_pos hA]
    omega
  by_cases hS : v ∈ R.shortVertices long
  · rw [if_pos hS]
    omega
  have hVertex {x y : V} (hxy : (R.used ⊓ Γ).Adj x y) (hEnd : v = x ∨ v = y) : False := by
    obtain ⟨hUsed,hΓ⟩ := hxy
    obtain ⟨i,hi⟩ := Digraph.iSup_adj.mp hUsed
    by_cases he : i.val = long
    · have hh : (wordGraph (R.word long)).Adj x y := he ▸ hi
      rcases hLong hh with ⟨p,q,_,hp,hq⟩ | ⟨_,hD⟩
      · have hM : x ∈ A ∧ y ∈ A := ⟨hp ▸ p.prop,hq ▸ q.prop⟩
        exact hA (hEnd.elim (fun h => h.symm ▸ hM.1) (fun h => h.symm ▸ hM.2))
      · exact disjoint_iff_inf_le.mp hDΓ (show (D ⊓ Γ).Adj x y from ⟨hD,hΓ⟩)
    · have hMem : v ∈ R.word i.val := hEnd.elim (fun h => h.symm ▸ hi.mem (by simp))
        (fun h => h.symm ▸ hi.mem (by simp))
      have hI : v ∈ R.interior i.val := by
        change v ∈ L.source i.val :: R.interior i.val ++ [L.target i.val] at hMem
        rcases List.mem_cons.mp hMem with hs | ht
        · exact (hv (hs.symm ▸ (L.ends i.val).1)).elim
        · rcases List.mem_append.mp ht with hm | hb
          · exact hm
          · exact (hv ((List.mem_singleton.mp hb).symm ▸ (L.ends i.val).2.1)).elim
      exact hS (mem_biUnion.mpr ⟨i.val,by simp [he,i.prop],List.mem_toFinset.mpr hI⟩)
  have hZeroIn : inDegree (R.used ⊓ Γ) v = 0 := by
    apply card_eq_zero.mpr
    exact eq_empty_iff_forall_notMem.mpr fun w hw => hVertex (mem_filter.mp hw).2 (Or.inr rfl)
  have hZeroOut : outDegree (R.used ⊓ Γ) v = 0 := by
    apply card_eq_zero.mpr
    exact eq_empty_iff_forall_notMem.mpr fun w hw => hVertex (mem_filter.mp hw).2 (Or.inl rfl)
  simp [hZeroIn,hZeroOut]

/-- Sum the actual reserve costs of a family of completed rounds. The
three counters correspond to the three terms of GGKLO (7.2). -/
theorem reserve_loss_of_rounds {J : Type*} [Fintype J] {K D Γ : Digraph V}
    (L : J → Layout V I) (R : ∀ i, Realization K (L i))
    (long : J → I) (A : J → Finset V) (hDΓ : Disjoint D Γ)
    (hLong : ∀ i, wordGraph ((R i).word (long i)) ≤
      mixed D (induced Γ (A i)) ⟨Subtype.val,Subtype.val_injective⟩)
    (b s l : ℕ) (hEndpoint : ∀ v, (∑ i, ((L i).endpointLoad true v+
      (L i).endpointLoad false v)) ≤ b)
    (hInterior : ∀ v, DirectedReserveUsage.visits (fun i => (R i).shortVertices (long i)) v ≤ s)
    (hBlock : ∀ v, DirectedReserveUsage.visits A v ≤ l) :
    let U := (⨆ i, (R i).used) ⊓ Γ
    ∀ v, inDegree U v+outDegree U v ≤ b+2*s+2*l := by
  dsimp only
  have hEq : (⨆ i, (R i).used ⊓ Γ) = (⨆ i, (R i).used) ⊓ Γ := by
    ext x y
    simp only [Digraph.iSup_adj,Digraph.inf_adj]
    constructor
    · rintro ⟨i,hi,hΓ⟩
      exact ⟨⟨i,hi⟩,hΓ⟩
    · rintro ⟨⟨i,hi⟩,hΓ⟩
      exact ⟨i,hi,hΓ⟩
  rw [← hEq]
  exact DirectedReserveUsage.reserve_arc_cost _ _ A _ b s l hEndpoint hInterior hBlock
    (fun i v => (R i).reserve_cost (long i) (A i) hDΓ (hLong i) v)

end OverfullWork.DirectedSpanningConfiguration
