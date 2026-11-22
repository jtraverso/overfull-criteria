module

public import OverfullWork.OsthusStadenPhysicalRedHalves
public import OverfullWork.OsthusStadenBridgeCells
public import OverfullWork.KuhnOsthusWoundSetup

@[expose] public section


/-! Claim 5.1 on the actual reduced layers of §5.5. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

noncomputable def PrimaryRedSelection.allPCells {I : Type*} [Fintype I]
    {r s p : ℕ} [NeZero (2*s)]
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)} (D : PrimaryRedSelection (p := p) C)
    (q : Bool) (j : RefinedFactorIndex r (2*s) p) : Finset (RefinedVertex I (2*s) p) :=
  univ.biUnion (D.pCells q j)

theorem PrimaryRedSelection.mem_allPCells_iff {I : Type*} [Fintype I]
    {r s p : ℕ} [NeZero (2*s)]
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)} (D : PrimaryRedSelection (p := p) C)
    (q : Bool) (j : RefinedFactorIndex r (2*s) p) (a : RefinedVertex I (2*s) p) :
    a ∈ D.allPCells q j ↔ D.selectedPCell q j a := by
  constructor
  · intro h
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp h
    obtain ⟨z,hz,he⟩ := mem_map.mp hi
    exact ⟨i,z,hz,he.symm⟩
  · rintro ⟨i,z,hz,he⟩
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_map.mpr ⟨z,hz,he.symm⟩⟩

/-- Every refined layer realizes the bridge-cell ordering along a
Hamilton ordering of the primary reduced graph. The source and target
indices are all distinct, and the two ends of every bridge use the
prescribed red directions. -/
theorem PrimaryRedSelection.exists_bridge_order
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero (2*s)] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ η d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    {A : UnwoundPrimarySlices G thin E g σ τ η d R}
    (D : PrimaryRedSelection (p := p) A.coordinates)
    (j : RefinedFactorIndex r (2*s) p) (hs : 3 ≤ s)
    (Q : Digraph I) (C : Equiv.Perm I) (hC : ∀ i, Q.Adj i (C i))
    (hσ : ∀ i, Q.Adj i (σ j.1 i)) :
    ∃ src dst : I → RefinedVertex I (2*s) p,
      (∀ i, (src i).1.1 = i ∧ (dst i).1.1 = C i) ∧
      (∀ i, Q.Adj (src i).1.1 (dst i).1.1 ∧ Q.Adj (((A.factor j).symm (src i)).1.1) (src i).1.1) ∧
      (∀ i, D.selectedPCell false j ((A.factor j).symm (src i)) ∧ D.selectedPCell true j (dst i)) ∧
      Function.Injective src ∧ Function.Injective dst ∧ (∀ i k, src i ≠ dst k) := by
  have hProj (w : RefinedVertex I (2*s) p) : (A.factor j w).1.1 = σ j.1 w.1.1 := by
    rcases j with ⟨t,a,b⟩
    exact (congrArg Prod.fst (A.factor_proj t a b w)).trans (A.first_proj t a w.1)
  have hIn (i : I) : ∃ w ∈ D.allPCells true j,w.1.1 = i := by
    have hNE : (D.select true j i).Nonempty := card_pos.mp (by rw [D.size]; omega)
    obtain ⟨z,hz⟩ := hNE
    exact ⟨redPLabel j.1.val i z,(D.mem_allPCells_iff _ _ _).mpr ⟨i,z,hz,rfl⟩,rfl⟩
  have hOut (i : I) :
      1 < ((D.allPCells false j).filter (fun w => w.1.1 = i)).card := by
    have hSub : D.pCells false j i ⊆ (D.allPCells false j).filter (fun w => w.1.1 = i) := by
      intro w hw
      obtain ⟨z,hz,hzEq⟩ := mem_map.mp hw
      exact mem_filter.mpr ⟨(D.mem_allPCells_iff _ _ _).mpr ⟨i,z,hz,hzEq.symm⟩,
        congrArg (fun a => a.1.1) hzEq.symm⟩
    refine (show 1 < (D.pCells false j i).card from by rw [D.pCells_card]; omega).trans_le (card_le_card hSub)
  obtain ⟨src,dst,hTag,hEdge,hVotes,hSrc,hDst,hSeparate⟩ := exists_bridge_cells
    Q (fun w : RefinedVertex I (2*s) p => w.1.1) C (σ j.1) (A.factor j)
    (D.allPCells true j) (D.allPCells false j) hC hProj hIn hOut
  refine ⟨src,dst,hTag,fun i => ⟨hEdge i,?_⟩,fun i =>
    ⟨(D.mem_allPCells_iff _ _ _).mp (hVotes i).1,(D.mem_allPCells_iff _ _ _).mp (hVotes i).2⟩,
    hSrc,hDst,hSeparate⟩
  have he := hProj ((A.factor j).symm (src i))
  rw [Equiv.apply_symm_apply] at he
  rw [he]
  exact hσ _

/-- Every projected successor uses a positive copy of an arc of the
underlying reduced graph. -/
theorem primary_factor_successor_in_support {I : Type*} {r : ℕ}
    (Q : Digraph I) (d : I → I → ℝ) (β : ℝ) (σ : Fin r → Equiv.Perm I)
    (pick : Fin r → I → DirectedRegularPairs.ReducedCopy (DirectedRegularPairs.reducedMultiplicity Q d β))
    (hPick : ∀ t i, (pick t i).1 = (i,σ t i)) :
    ∀ t i, Q.Adj i (σ t i) := by
  intro t i
  by_contra h
  have hCount := (pick t i).2.isLt
  change (pick t i).2.val <
    DirectedRegularPairs.reducedMultiplicity Q d β (pick t i).1.1 (pick t i).1.2 at hCount
  have hZero : DirectedRegularPairs.reducedMultiplicity Q d β (pick t i).1.1 (pick t i).1.2 = 0 := by
    rw [hPick]
    exact if_neg h
  omega

universe u

/-- Use the Hamilton ordering of a robust spanning subgraph of the
primary reduced graph to prepare the bridge-cell ordering in all layers. -/
theorem exists_bridge_orders_from_robust_support (ν t₀ α : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ t₀) (hτα : 16*t₀ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {I : Type u} [Fintype I] {V : Type*} [Fintype V]
      {r s p m : ℕ} [NeZero (2*s)] [NeZero p]
      {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
      {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ η d : ℝ}
      {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
        (cluster (g t) i) (2*s) p m τ τ τ}
      {A : UnwoundPrimarySlices G thin E g σ τ η d R}
      (D : PrimaryRedSelection (p := p) A.coordinates) (Q S : Digraph I),
      N ≤ Fintype.card I → 3 ≤ s → S ≤ Q → IsRealRobust S ν t₀ →
      (∀ i, α*(Fintype.card I:ℝ) ≤ (inDegree S i:ℝ)) →
      (∀ i, α*(Fintype.card I:ℝ) ≤ (outDegree S i:ℝ)) →
      (∀ t i, Q.Adj i (σ t i)) →
      ∃ e : Fin (Fintype.card I) ≃ I,
        let C := e.permCongr (finRotate (Fintype.card I))
        (∀ i, Q.Adj i (C i)) ∧
        ∃ src dst : RefinedFactorIndex r (2*s) p → I → RefinedVertex I (2*s) p,
          (∀ j i, (src j i).1.1 = i ∧ (dst j i).1.1 = C i) ∧
          (∀ j i, Q.Adj (src j i).1.1 (dst j i).1.1 ∧
            Q.Adj (((A.factor j).symm (src j i)).1.1) (src j i).1.1) ∧
          (∀ j i, D.selectedPCell false j ((A.factor j).symm (src j i)) ∧
            D.selectedPCell true j (dst j i)) ∧
          (∀ j, Function.Injective (src j)) ∧ (∀ j, Function.Injective (dst j)) ∧
          ∀ j i k, src j i ≠ dst j k := by
  obtain ⟨N,hN⟩ := exists_kuhn_osthus_ordered_reduced_cycle.{u} ν t₀ α hν hντ hτα hα
  refine ⟨N,?_⟩
  intro I _ V _ r s p m _ _ G thin E g σ τ η d R A D Q S hSize hs hSub hRob hIn hOut hSucc
  obtain ⟨e,hCycle,_,_⟩ := hN S hSize hRob hIn hOut
  let C := e.permCongr (finRotate (Fintype.card I))
  have hC (i : I) : Q.Adj i (C i) := by
    have h := hCycle (e.symm i)
    change S.Adj (e (e.symm i)) (e (finRotate (Fintype.card I) (e.symm i))) at h
    rw [e.apply_symm_apply] at h
    exact hSub h
  choose src dst hTags hEdges hRed hSrc hDst hSeparate using fun j =>
    D.exists_bridge_order j hs Q C hC (hSucc j.1)
  exact ⟨e,hC,src,dst,hTags,hEdges,hRed,hSrc,hDst,hSeparate⟩

end OverfullWork.DirectedRobustExpansion
