module

public import OverfullWork.HeavyNeighbourCutRepair

@[expose] public section


/-! # Orient the free blocks while retaining fixed paired exceptions

This is the remainder-weight comparison in CMS (5.5), which is stronger
than balancing the total centre degree. Both pinned blocks remain fixed
while the two unpinned remainders may exchange sides.
-/
namespace OverfullWork.FrozenBlockOrientation
open Finset BalancedCutPerturbation
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem exists_orientation (A X Y : Finset V) (m : ℕ) (w : V → ℕ)
    (hA : A.card = m) (hAc : Aᶜ.card = m) (hX : X ⊆ A) (hY : Y ⊆ Aᶜ)
    (hXY : X.card = Y.card) (hWeight : (∑ x ∈ X, w x) ≤ ∑ y ∈ Y, w y) :
    ∃ B : Finset V, B.card = m ∧ Bᶜ.card = m ∧ X ⊆ B ∧ Y ⊆ Bᶜ ∧
      (∑ x ∈ B\X, w x) ≤ ∑ x ∈ Bᶜ\Y, w x ∧
      (∑ x ∈ B, w x) ≤ ∑ x ∈ Bᶜ, w x ∧
      (Close A B X.card ∨ Close Aᶜ B X.card) := by
  let U := A\X
  let V' := Aᶜ\Y
  have hUX := sum_sdiff (f := w) hX
  have hVY := sum_sdiff (f := w) hY
  change (∑ x ∈ U, w x)+(∑ x ∈ X, w x) = ∑ x ∈ A, w x at hUX
  change (∑ x ∈ V', w x)+(∑ x ∈ Y, w x) = ∑ x ∈ Aᶜ, w x at hVY
  by_cases hFree : (∑ x ∈ U, w x) ≤ ∑ x ∈ V', w x
  · refine ⟨A,hA,hAc,hX,hY,hFree,?_,Or.inl ?_⟩
    · omega
    · simp [Close]
  let B := V'∪X
  have hVX : Disjoint V' X := by
    apply disjoint_left.mpr
    intro x hv hx
    exact (mem_compl.mp (mem_sdiff.mp hv).1) (hX hx)
  have hUY : Disjoint U Y := by
    apply disjoint_left.mpr
    intro x hu hy
    exact (mem_compl.mp (hY hy)) (mem_sdiff.mp hu).1
  have hCompl : Bᶜ = U∪Y := by
    ext x
    have hx := fun hh : x ∈ X => hX hh
    have hy := fun hh : x ∈ Y => mem_compl.mp (hY hh)
    simp only [B,U,V',mem_compl,mem_union,mem_sdiff]
    tauto
  have hB : B.card = m := by
    dsimp only [B,V']
    rw [card_union_of_disjoint hVX,card_sdiff_of_subset hY,←hXY,hAc]
    have hc := card_le_card hY
    omega
  have hBc : Bᶜ.card = m := by
    have hc := card_add_card_compl A
    simp only [card_compl]
    omega
  have hXB : X ⊆ B := subset_union_right
  have hYBc : Y ⊆ Bᶜ := by rw [hCompl];exact subset_union_right
  have hFreeB : B\X = V' := by
    ext x
    have hnot : x ∈ V' → x ∉ X := fun hv hx => disjoint_left.mp hVX hv hx
    simp only [B,mem_sdiff,mem_union]
    tauto
  have hFreeBc : Bᶜ\Y = U := by
    rw [hCompl]
    ext x
    have hnot : x ∈ U → x ∉ Y := fun hu hy => disjoint_left.mp hUY hu hy
    simp only [mem_sdiff,mem_union]
    tauto
  have hDegree : (∑ x ∈ B, w x) ≤ ∑ x ∈ Bᶜ, w x := by
    rw [hCompl,sum_union hUY]
    change (∑ x ∈ V'∪X, w x) ≤ _
    rw [sum_union hVX]
    omega
  have hClose : Close Aᶜ B X.card := by
    have hsub : B\Aᶜ ⊆ X := by
      intro x hx
      rcases mem_union.mp (mem_sdiff.mp hx).1 with hv | hxX
      · exact False.elim ((mem_sdiff.mp hx).2 (mem_sdiff.mp hv).1)
      · exact hxX
    have hc := card_le_card hsub
    exact ⟨by rw [difference_card_eq Aᶜ B (hAc.trans hB.symm)];exact hc,hc⟩
  refine ⟨B,hB,hBc,hXB,hYBc,?_,hDegree,Or.inr hClose⟩
  rw [hFreeB,hFreeBc]
  omega

end OverfullWork.FrozenBlockOrientation
