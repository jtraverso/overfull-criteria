module

public import OverfullWork.CMSOperation41PhysicalPrefix

@[expose] public section


/-! Exact class-two and maximum-degree invariants of the physical
prefixes once the auxiliary prescriptions have been realized together.
Ordinary core edges from different rounds are disjoint. The virtual
graph keeps its full ordinary core for every round. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem max_degree_and_class_two_of_eq (G H : SimpleGraph V)
    [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj] (h : G = H) (d : ℕ)
    (hG : G.maxDegree = d ∧ ¬G.EdgeColorable G.maxDegree) :
    H.maxDegree = d ∧ ¬H.EdgeColorable H.maxDegree := by
  subst H
  cases Subsingleton.elim dH dG
  exact hG

theorem auxiliary_trimming_preserves_core (G : SimpleGraph V) (U : Finset V)
    (S T P : ℕ → SimpleGraph V) (W : ℕ → Finset V) (m : ℕ)
    (hFirst : S 0 = G) (hW : ∀ i < m,W i ⊆ U)
    (hClean : ∀ i < m,DeletionRun (W i) (S i) (T i))
    (hOuter : ∀ i < m,∀ x y,(P i).Adj x y → x ∈ U ∨ y ∈ U)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i)) :
    (∀ i ≤ m,∀ x y,x ∉ U → y ∉ U → ((S i).Adj x y ↔ G.Adj x y)) ∧
      (∀ i < m,∀ x y,x ∉ U → y ∉ U → ((T i).Adj x y ↔ G.Adj x y)) := by
  have hCleanCore (i : ℕ) (hi : i < m) (x y : V) (hx : x ∉ U) (hy : y ∉ U) :
      (T i).Adj x y ↔ (S i).Adj x y := by
    let Z := ((W i : Set V)ᶜ)
    let a : Z := ⟨x,fun h => hx (hW i hi h)⟩
    let b : Z := ⟨y,fun h => hy (hW i hi h)⟩
    have h := congrArg (fun R : SimpleGraph Z => R.Adj a b) (DeletionRun.induce_away (hClean i hi))
    exact Iff.of_eq h
  have hS (i : ℕ) (hi : i ≤ m) (x y : V) (hx : x ∉ U) (hy : y ∉ U) :
      (S i).Adj x y ↔ G.Adj x y := by
    induction i with
    | zero => rw [hFirst]
    | succ i ih =>
      rw [hNext i (by omega)]
      change (T i).Adj x y ∧ ¬(P i).Adj x y ↔ G.Adj x y
      have hP : ¬(P i).Adj x y := fun h => (hOuter i (by omega) x y h).elim hx hy
      exact (and_iff_left hP).trans ((hCleanCore i (by omega) x y hx hy).trans (ih (by omega)))
  exact ⟨hS,fun i hi x y hx hy => (hCleanCore i hi x y hx hy).trans (hS i hi.le x y hx hy)⟩

set_option maxHeartbeats 6000000 in
theorem realized_trimming_prefixes_class_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (S T P L : ℕ → SimpleGraph V) (W : ℕ → Finset V) (m : ℕ) :
    let d := G.maxDegree
    let H (i : ℕ) := sdiff (S i) (usedTrimmingPrefix L i)
    let C (i : ℕ) := sdiff (T i) (usedTrimmingPrefix L i)
    S 0 = G → 2*m ≤ d → ¬G.EdgeColorable d →
    (∀ i < m,W i ⊆ U) →
    (∀ i < m,DeletionRun (W i) (S i) (T i)) →
    (∀ i < m,∀ w ∈ W i,(S i).degree w < d-2*i) →
    (∀ i < m,P i ≤ T i) →
    (∀ i < m,∀ x y,(P i).Adj x y → x ∈ U ∨ y ∈ U) →
    (∀ i < m,L i ≤ G) →
    (∀ i,∀ x y,(L i).Adj x y → x ∉ U ∧ y ∉ U) →
    (∀ i < m,∀ j < i,Disjoint (L i) (L j)) →
    (∀ i < m,S (i+1) = sdiff (T i) (P i)) →
    (∀ i < m,(P i ⊔ L i).EdgeColorable 2) →
    (∀ i < m,∀ v,(P i ⊔ L i).degree v ≤ 2) →
    (∀ i < m,∀ v,(C i).degree v+2 ≤ d-2*i+(P i ⊔ L i).degree v) →
    ∀ i ≤ m,(H i).maxDegree = d-2*i ∧ ¬(H i).EdgeColorable (H i).maxDegree := by
  intro d H C hFirst hLength hNC hW hClean hLow hLeP hOuter hL hInner hDis hNext hColour hDegree hDemand i hi
  obtain ⟨_,hVirtualCore⟩ := auxiliary_trimming_preserves_core G U S T P W m hFirst hW hClean hOuter hNext
  induction i with
  | zero =>
    have h₀ : H 0 = G := by
      change sdiff (S 0) (usedTrimmingPrefix L 0) = G
      rw [hFirst]
      ext u v
      change (G.Adj u v ∧ ¬(usedTrimmingPrefix L 0).Adj u v) ↔ G.Adj u v
      refine ⟨And.left,fun h => ⟨h,?_⟩⟩
      intro hu
      obtain ⟨j,_⟩ := iSup_adj.mp hu
      exact Fin.elim0 j
    simpa only [Nat.mul_zero,Nat.sub_zero] using
      max_degree_and_class_two_of_eq G (H 0) h₀.symm d ⟨rfl,hNC⟩
  | succ i ih =>
    have hi' : i < m := by omega
    obtain ⟨hPrev,hObstruction⟩ := ih hi'.le
    have hNoOld (v : V) (hv : v ∈ U) (u : V) : ¬(usedTrimmingPrefix L i).Adj v u := by
      intro h
      obtain ⟨j,hj⟩ := iSup_adj.mp h
      exact (hInner j.val v u hj).1 hv
    have hLowH (v : V) (hv : v ∈ W i) : (H i).degree v < (H i).maxDegree := by
      have hEq : (H i).degree v = (S i).degree v := by
        rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
        congr 1
        ext u
        simp only [mem_neighborFinset]
        change (S i).Adj v u ∧ ¬(usedTrimmingPrefix L i).Adj v u ↔ (S i).Adj v u
        exact and_iff_left (hNoOld v (hW i hi' hv) u)
      rw [hEq,hPrev]
      exact hLow i hi' v hv
    obtain ⟨_,_,hCMax,hCNC⟩ := exact_replay_away_from_core_removals (hClean i hi')
      (hW i hi') hNoOld hLowH hObstruction
    have hOrdinary : L i ≤ T i := by
      intro u v huv
      have hInner' := hInner i u v huv
      exact (hVirtualCore i hi' u v hInner'.1 hInner'.2).mpr (hL i hi' huv)
    have hDisOuter (j : ℕ) (_ : j < i) : Disjoint (P i) (L j) := by
      rw [disjoint_iff_inf_le]
      intro u v hv
      have hIn := hInner j u v hv.2
      exact ((hOuter i hi' u v hv.1).elim hIn.1 hIn.2).elim
    have hAvailable : P i ⊔ L i ≤ C i :=
      realized_layer_available_at_prefix (T i) (P i) L i (hLeP i hi') hOrdinary
        (hDis i hi') hDisOuter
    have hMax : (C i).maxDegree = d-2*i := hCMax.trans hPrev
    have hTwo : 2 ≤ (C i).maxDegree := by omega
    have hReq (v : V) : (C i).degree v+2 ≤ (C i).maxDegree+(P i ⊔ L i).degree v := by
      rw [hMax]
      exact hDemand i hi' v
    obtain ⟨hAfter,hUncol⟩ := realized_layer_preserves_class_two (C i) (P i ⊔ L i) hTwo
      hCNC hAvailable (hColour i hi') (hDegree i hi') hReq
    have hEq : H (i+1) = sdiff (C i) (P i ⊔ L i) :=
      virtual_and_physical_prefix_step (S (i+1)) (T i) (P i) (P i ⊔ L i) L i (hNext i hi') rfl
    apply max_degree_and_class_two_of_eq _ _
      (dG := SimpleGraph.Sdiff.adjDecidable V (C i) (P i ⊔ L i)) hEq.symm
    refine ⟨?_,hUncol⟩
    rw [hAfter,hMax]
    omega

end OverfullWork.CMSTrimmingRound
