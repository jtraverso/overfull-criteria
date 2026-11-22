module

public import OverfullWork.KuhnOsthusCycleAbsorberRepairPair

@[expose] public section


/-! The open portion of S from V₄ to V₁₃, through the two ordered
switch pairs and the reserved final switch. All its arcs come
from the complement of the primary path bundle. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Build the open reserve in a residual graph, using the two
specified crossed matchings and a new repair switch in that graph. -/
theorem CycleAbsorberClaimOne.exists_open_reserve_in {G D : Digraph V}
    {A : ℕ → Finset V} {m n : ℕ} (C : CycleAbsorberClaimOne G A m n) (mark : Fin m)
    (hSize : ∀ i, 3 ≤ i → i ≤ 12 → (A i).card = 2*m)
    (hDis : ∀ i j, 3 ≤ i → i ≤ 12 → 3 ≤ j → j ≤ 12 → i ≠ j → Disjoint (A i) (A j))
    (hFirst : ∀ i b, D.Adj (C.first.source (cycleAbsorberSwitchSlot m (i,b)))
      (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 b))))
    (hSecond : ∀ i b, D.Adj (C.second.source (alternateCycleAbsorberSwitchSlot m (i,b)))
      (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 b))))
    (η d : ℝ) (hη : 0 ≤ η) (hGap : 2*η < d) (hd : d ≤ 1)
    (hPairs : ∀ i, 4 ≤ i → i < 12 → IsLowerSuperregularPair D η d (A i) (A (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRoute : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    ∃ S : OrderedClusterPaths D A (Fin m × Fin 2) 3 12,
      (∀ i b, S.vertex 3 (i,b) = (C.first.source (cycleAbsorberSwitchSlot m (i,b))).val) ∧
      (∀ i b, S.vertex 4 (i,b) = (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 b))).val) ∧
      (∀ i b, S.vertex 7 (i,b) = (C.second.source (alternateCycleAbsorberSwitchSlot m (i,b))).val) ∧
      (∀ i b, S.vertex 8 (i,b) = (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 b))).val) ∧
      ∀ a b : Fin 2, D.Adj (S.vertex 11 (mark,a)) (S.vertex 12 (mark,b)) := by
  obtain ⟨S,h₃,h₄,h₇,h₈⟩ := C.exists_reserve_middle_in
    (fun i hi hj => hSize i (by omega) (by omega))
    (fun i j hi hi' hj hj' h => hDis i j (by omega) (by omega) (by omega) (by omega) h)
    hFirst hSecond η d hη hGap hd (fun i hi hi' => hPairs i hi (by omega)) r hr hCut hRoute
  obtain ⟨T,hKeep,hRepair⟩ := exists_ordered_paths_through_repair_pair S (by decide) mark
    (fun i hi hi' => hSize i (by omega) hi')
    (fun i j hi hi' hj hj' he => hDis i j (by omega) hi' (by omega) hj' he)
    η d hη hGap hd (fun i hi hi' => hPairs i (by omega) hi') r hr hCut hRoute
  exact ⟨T,fun i b => (hKeep 3 (by decide) (i,b)).trans (h₃ i b),
    fun i b => (hKeep 4 (by decide) (i,b)).trans (h₄ i b),
    fun i b => (hKeep 7 (by decide) (i,b)).trans (h₇ i b),
    fun i b => (hKeep 8 (by decide) (i,b)).trans (h₈ i b),hRepair⟩

/-- The path bundle carries both rows of ordered switch marks. The
last marked copy is prescribed before linking it to the repair switch. -/
theorem CycleAbsorberClaimOne.exists_open_reserve {G : Digraph V} {A : ℕ → Finset V} {m n : ℕ}
    (C : CycleAbsorberClaimOne G A m n) (hn : 12 ≤ n) (mark : Fin m)
    (hSize : ∀ i ≤ n, (A i).card = 2*m)
    (hDis : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (A i) (A j))
    (ε η d a : ℝ) (hε : 0 ≤ ε) (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a)
    (hGap : 2*η < d) (hd : d ≤ 1) (hTol : 2*(ε+a) ≤ η)
    (hBudget : 1 ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPairs : ∀ i, 4 ≤ i → i < 12 → IsLowerSuperregularPair G ε d (A i) (A (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRoute : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    let D := G \ C.paths.unionPaths
    ∃ S : OrderedClusterPaths D A (Fin m × Fin 2) 3 12,
      (∀ i b, S.vertex 3 (i,b) = (C.first.source (cycleAbsorberSwitchSlot m (i,b))).val) ∧
      (∀ i b, S.vertex 4 (i,b) = (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 b))).val) ∧
      (∀ i b, S.vertex 7 (i,b) = (C.second.source (alternateCycleAbsorberSwitchSlot m (i,b))).val) ∧
      (∀ i b, S.vertex 8 (i,b) = (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 b))).val) ∧
      ∀ a b : Fin 2, D.Adj (S.vertex 11 (mark,a)) (S.vertex 12 (mark,b)) := by
  intro D
  have hDis' (i j : ℕ) (_ : 0 ≤ i) (hi : i ≤ n) (_ : 0 ≤ j) (hj : j ≤ n) (he : i ≠ j) :=
    hDis i j hi hj he
  obtain ⟨hFirst,hSecond⟩ := C.crossed_arcs_after_factor (by omega) (le_refl C.paths.unionPaths)
    (C.paths.unionPaths_out_unique hDis')
  have hRes (i : ℕ) (hi : 4 ≤ i) (hir : i < 12) : IsLowerSuperregularPair D η d (A i) (A (i+1)) := by
    have hm : 0 < m := Nat.zero_lt_of_lt mark.isLt
    exact IsLowerSuperregularPair.after_path_bundle C.paths (fun j k _ hj _ hk h => hDis j k hj hk h)
      (A i) (A (i+1)) (card_pos.mp (by rw [hSize i (by omega)]; omega))
      (card_pos.mp (by rw [hSize (i+1) (by omega)]; omega)) (2*m)
      (hSize i (by omega)) (hSize (i+1) (by omega)) ε η d a
      hε hη hη₁ ha (by linarith) hTol hBudget (hPairs i (by omega) hir)
  exact C.exists_open_reserve_in mark (fun i _ hi => hSize i (hi.trans hn))
    (fun i j _ hi _ hj h => hDis i j (hi.trans hn) (hj.trans hn) h)
    hFirst hSecond η d hη.le hGap hd hRes r hr hCut hRoute

end OverfullWork.DirectedRobustExpansion
