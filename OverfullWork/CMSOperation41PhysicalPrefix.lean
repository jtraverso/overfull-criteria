module

public import OverfullWork.CMSOperation41Preprocessing
public import OverfullWork.CMSOperation41Invariants
public import OverfullWork.RobustExpansionDeletion

@[expose] public section


/-! The auxiliary and physical prefixes have identical incidences at
every exceptional vertex. The only difference consists of the ordinary
core edges already used by the simultaneous packing. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing RobustExpansion
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

def usedTrimmingPrefix (L : ℕ → SimpleGraph V) (j : ℕ) : SimpleGraph V :=
  ⨆ i : Fin j,L i.val

theorem usedTrimmingPrefix_succ (L : ℕ → SimpleGraph V) (j : ℕ) :
    usedTrimmingPrefix L (j+1) = usedTrimmingPrefix L j ⊔ L j := by
  ext u v
  simp only [usedTrimmingPrefix,iSup_adj,sup_adj]
  constructor
  · rintro ⟨i,hi⟩
    by_cases h : i.val < j
    · exact Or.inl ⟨⟨i.val,h⟩,hi⟩
    · have he : i.val = j := by have ho := i.isLt; omega
      exact Or.inr (he ▸ hi)
  · rintro (⟨i,hi⟩ | hj)
    · exact ⟨⟨i.val,by have h := i.isLt; omega⟩,hi⟩
    · exact ⟨⟨j,Nat.lt_succ_self _⟩,hj⟩

theorem DeletionRun.induce_away {W : Finset V} {G T : SimpleGraph V}
    (p : DeletionRun W G T) :
    T.induce ((W : Set V)ᶜ) = G.induce ((W : Set V)ᶜ) := by
  induction p with
  | refl => rfl
  | @step U _ _ w x hw _ _ ih =>
    exact (induce_compl_delete_bad_edge U W hw).trans ih

theorem exact_replay_away_from_core_removals {G T C : SimpleGraph V} {W Z : Finset V}
    (p : DeletionRun W G T) (hW : W ⊆ Z)
    [DecidableRel (sdiff G C).Adj]
    (hC : ∀ v ∈ Z,∀ u,¬C.Adj v u)
    (hSmall : ∀ w ∈ W,(sdiff G C).degree w < (sdiff G C).maxDegree)
    (hNC : ¬(sdiff G C).EdgeColorable (sdiff G C).maxDegree) :
    let H := sdiff G C
    let S := sdiff T C
    DeletionRun W H S ∧ S ≤ H ∧ S.maxDegree = H.maxDegree ∧ ¬S.EdgeColorable S.maxDegree := by
  intro H S
  have hInc (w : V) (hw : w ∈ Z) (x : V) : H.Adj w x ↔ G.Adj w x :=
    ⟨fun h => h.1,fun h => ⟨h,hC w hw x⟩⟩
  obtain ⟨R,hRun,hLe,hMax,hUncol,hSync,hCore⟩ :=
    replay_auxiliary_low_preprocessing_on p hW H hInc hSmall hNC
  have hEq : R = S := by
    ext u v
    by_cases hu : u ∈ Z
    · exact (hSync u hu v).trans ⟨fun h => ⟨h,hC u hu v⟩,fun h => h.1⟩
    by_cases hv : v ∈ Z
    · rw [R.adj_comm,S.adj_comm]
      exact (hSync v hv u).trans ⟨fun h => ⟨h,hC v hv u⟩,fun h => h.1⟩
    have hu' : u ∈ ((W : Set V)ᶜ) := fun h => hu (hW h)
    have hv' : v ∈ ((W : Set V)ᶜ) := fun h => hv (hW h)
    have hAdj₁ := congrArg (fun J : SimpleGraph ↥((W : Set V)ᶜ) => J.Adj ⟨u,hu'⟩ ⟨v,hv'⟩) hCore
    have hAdj₂ := congrArg (fun J : SimpleGraph ↥((W : Set V)ᶜ) => J.Adj ⟨u,hu'⟩ ⟨v,hv'⟩)
      (DeletionRun.induce_away p)
    change (R.Adj u v) = (H.Adj u v) at hAdj₁
    change (T.Adj u v) = (G.Adj u v) at hAdj₂
    change R.Adj u v ↔ T.Adj u v ∧ ¬C.Adj u v
    rw [hAdj₁,hAdj₂]
    rfl
  subst R
  exact ⟨hRun,hLe,hMax,hUncol⟩

theorem virtual_and_physical_prefix_step (G T P C : SimpleGraph V)
    (L : ℕ → SimpleGraph V) (j : ℕ)
    (hVirtual : G = sdiff T P) (hLayer : C = P ⊔ L j) :
    sdiff G (usedTrimmingPrefix L (j+1)) =
      sdiff (sdiff T (usedTrimmingPrefix L j)) C := by
  subst G C
  rw [usedTrimmingPrefix_succ]
  ext u v
  simp only [sdiff_adj,sup_adj]
  tauto

theorem realized_layer_available_at_prefix (T P : SimpleGraph V)
    (L : ℕ → SimpleGraph V) (j : ℕ)
    (hLeP : P ≤ T) (hLeL : L j ≤ T)
    (hOrd : ∀ i < j,Disjoint (L j) (L i))
    (hPrescribed : ∀ i < j,Disjoint P (L i)) :
    P ⊔ L j ≤ sdiff T (usedTrimmingPrefix L j) := by
  intro u v h
  refine ⟨sup_le hLeP hLeL h,?_⟩
  intro hUsed
  obtain ⟨i,hi⟩ := iSup_adj.mp hUsed
  change P.Adj u v ∨ (L j).Adj u v at h
  rcases h with h | h
  · exact (disjoint_iff_inf_le.mp (hPrescribed i.val i.isLt)) ⟨h,hi⟩
  · exact (disjoint_iff_inf_le.mp (hOrd i.val i.isLt)) ⟨h,hi⟩

end OverfullWork.CMSTrimmingRound
