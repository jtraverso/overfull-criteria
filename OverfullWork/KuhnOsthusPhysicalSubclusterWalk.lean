module

public import OverfullWork.KuhnOsthusWalkCoordinates
public import OverfullWork.KuhnOsthusSharedStyleRefinement
public import OverfullWork.KuhnOsthusResidualExceptionalInterval

@[expose] public section


/-! Put the physical refinement in the order of the universal walk
and retain the successor pairs required by (ST3). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

set_option maxHeartbeats 500000 in
/-- Use one uniform refinement of each trimmed cluster and assign its
cells to the successive visits of the same universal walk. The cells
partition their original clusters and the traversed pairs remain
superregular, as in (ST1)–(ST3). -/
theorem exists_kuhn_osthus_physical_subcluster_walk
    (B ε η d : ℝ) (L : ℕ) (hL : 0 < L)
    (hB : 0 < B) (hε : 0 < ε) (hη : 0 < η) (hη₁ : η ≤ 1)
    (hFloor : 2*ε ≤ d) (hTol : 2*(max 2 (L:ℝ)*ε) ≤ η) :
    ∃ N : ℕ, ∀ {V : Type u} {I : Type*} [Fintype V] [Fintype I]
      (G : Digraph V) (X : I → Finset V) (F : Fin L → Equiv.Perm I) (m : ℕ),
      let q := L*Fintype.card I
      HasSpanningCycle (fun e f : (Σ _ : Fin L, I) => F e.1 e.2 = f.2) →
      0 < m → N ≤ L*m → (∀ i, (X i).card = L*m) →
      4*(Fintype.card V:ℝ) ≤ B*((L*m:ℕ):ℝ) →
      (∀ i j, i ≠ j → Disjoint (X i) (X j)) →
      (∀ a i, IsLowerSuperregularPair G ε d (X i) (X (F a i))) →
      ∃ (order : Fin q ≃ Fin L × I) (D : Fin q → Finset V),
        (∀ j, (order (finRotate q j)).2 = F (order j).1 (order j).2) ∧
        (∀ i, (univ : Finset (Fin L)).biUnion (fun a => D (order.symm (a,i))) = X i) ∧
        (∀ j, (D j).card = m ∧ D j ⊆ X (order j).2) ∧
        (∀ i j, i ≠ j → Disjoint (D i) (D j)) ∧
        (∀ v, (∃ i, v ∈ X i) → ∃ j, v ∈ D j) ∧
        ∀ j, IsLowerSuperregularPair G η d (D j) (D (finRotate q j)) := by
  obtain ⟨N,hN⟩ := exists_shared_exceptional_style_refinement.{u} B ε hB hε L hL
  refine ⟨N,?_⟩
  intro V I _ _ G X F m q hWalk hm hSizeN hSize hProfiles hDisG hPairs
  obtain ⟨order,hOrder,_⟩ := exists_indexed_universal_walk F hWalk
  obtain ⟨C,hC,hDis,hCover,hRef⟩ := hN G G X m hSizeN hSize hProfiles hDisG
  let D (j : Fin q) := C (order j)
  have hCover' (i : I) : (univ : Finset (Fin L)).biUnion (fun a => D (order.symm (a,i))) = X i := by
    simpa only [D,order.apply_symm_apply] using hCover i
  refine ⟨order,D,hOrder,hCover',fun j => hC (order j),
    (fun _ _ h => hDis _ _ (order.injective.ne h)),?_,?_⟩
  · intro v hv
    obtain ⟨i,hi⟩ := hv
    rw [←hCover' i] at hi
    obtain ⟨a,_,ha⟩ := mem_biUnion.mp hi
    exact ⟨order.symm (a,i),ha⟩
  · intro j
    let i := order j
    let k := order (finRotate q j)
    have hP : IsLowerSuperregularPair G ε d (X i.2) (X k.2) := by
      rw [show k.2 = F i.1 i.2 from hOrder j]
      exact hPairs i.1 i.2
    have hi : (C i).Nonempty := card_pos.mp (by rw [(hC i).1]; exact hm)
    have hEq : (C i).card = (C k).card := (hC i).1.trans (hC k).1.symm
    have hP' := IsLowerSuperregularPair.on_residual_style_cells G ⊥ bot_le
      (X i.2) (X k.2) (C i) (C k) (hC i).2 (hC k).2 hi hEq L 0 d ε η 0 hL hε.le hη hη₁
      le_rfl hFloor (by rw [hSize,(hC i).1]) (by rw [hSize,(hC k).1])
      (hRef i).1 (hRef k).2.1 (by simpa only [add_zero] using hTol)
      (by norm_num) (by simp [outDegree]) (by simp [inDegree,inNeighbours]) hP
    simpa only [sdiff_bot] using hP'

end OverfullWork.DirectedRobustExpansion
