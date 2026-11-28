module

public import OverfullWork.DirectedMultiplicityDemands
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {I : Type*} [Fintype I]

/-- On the two sides of a cluster cycle, the neighbors of a nonempty
proper set of left clusters strictly outnumber the set. -/
theorem clusterCycle_neighbour_card
    (next : Equiv.Perm I) (hCycle : ∀ i j, next.SameCycle i j)
    (S : Finset I) (hS : S.Nonempty) (hProper : S ≠ univ) :
    S.card + 1 ≤ (S ∪ S.image next).card := by
  by_contra! h
  have hEq : S ∪ S.image next = S :=
    (eq_of_subset_of_card_le subset_union_left (by omega)).symm
  have hClosed : ∀ i ∈ S, next i ∈ S := by
    intro i hi
    rw [← hEq]
    exact mem_union_right _ (mem_image_of_mem next hi)
  obtain ⟨i, hi⟩ := hS
  have hPow (n : ℕ) : (next ^ n) i ∈ S := by
    induction n with
    | zero => simpa using hi
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hClosed _ ih
  apply hProper
  apply eq_univ_of_forall
  intro j
  obtain ⟨n, hn⟩ := (hCycle i j).exists_nat_pow_eq
  rw [← hn]
  exact hPow n

/-- The integral Hall assignment in Chen–Shan §5.1.5. Each left
cluster meets the right cluster with the same index and the one with
the next index. The row and column sums are the required loads. -/
theorem exists_clusterCycle_demand_assignment
    (next : Equiv.Perm I) (hCycle : ∀ i j, next.SameCycle i j)
    (p q : I → ℕ) (b z : ℕ) (hz : z ≤ b) (hBudget : Fintype.card I*z ≤ b)
    (hp : ∀ i, p i ≤ b) (hq : ∀ i, b-z ≤ q i)
    (hBalance : (∑ i, p i) = ∑ i, q i) :
    ∃ H : I → I → ℕ,
      (∀ i j, j ≠ i → j ≠ next i → H i j = 0) ∧
      (∀ i, (∑ j, H i j) = p i) ∧ (∀ j, (∑ i, H i j) = q j) := by
  classical
  let capacity (i j : I) := if j = i ∨ j = next i then ∑ u, p u else 0
  have hCuts (S T : Finset I) : (∑ i ∈ S, p i) ≤ (∑ j ∈ T, q j) +
      ∑ i ∈ S, ∑ j ∈ Tᶜ, capacity i j := by
    by_cases hEdge : ∃ i ∈ S, ∃ j ∈ Tᶜ, j = i ∨ j = next i
    · obtain ⟨i, hi, j, hj, he⟩ := hEdge
      have hCap : (∑ u, p u) ≤ ∑ x ∈ S, ∑ y ∈ Tᶜ, capacity x y := by
        calc
          _ = capacity i j := by simp [capacity, he]
          _ ≤ ∑ y ∈ Tᶜ, capacity i y := single_le_sum (fun _ _ => Nat.zero_le _) hj
          _ ≤ _ := single_le_sum (f := fun x => ∑ y ∈ Tᶜ, capacity x y)
            (fun _ _ => Nat.zero_le _) hi
      exact (sum_le_sum_of_subset (subset_univ S)).trans (hCap.trans (Nat.le_add_left _ _))
    · have hN : S ∪ S.image next ⊆ T := by
        intro j hj
        by_contra hNot
        have hj' : j ∈ Tᶜ := mem_compl.mpr hNot
        rcases mem_union.mp hj with h | h
        · exact hEdge ⟨j, h, j, hj', Or.inl rfl⟩
        · obtain ⟨i, hi, rfl⟩ := mem_image.mp h
          exact hEdge ⟨i, hi, _, hj', Or.inr rfl⟩
      have hHall : (∑ i ∈ S, p i) ≤ ∑ j ∈ T, q j := by
        by_cases hFull : S = univ
        · have hT : T = univ := eq_univ_of_forall fun i => hN
            (mem_union_left _ (hFull ▸ mem_univ i))
          simpa [hFull, hT] using hBalance.le
        by_cases hEmpty : S = ∅
        · simp [hEmpty]
        have hNon : S.Nonempty := nonempty_iff_ne_empty.mpr hEmpty
        have hExpand := (clusterCycle_neighbour_card next hCycle S hNon hFull).trans (card_le_card hN)
        have hCost : (S.card+1)*z ≤ b :=
          (Nat.mul_le_mul_right z (hExpand.trans (card_le_univ T))).trans hBudget
        have hMargin : S.card*b ≤ (S.card+1)*(b-z) := by
          have hSub := Nat.sub_add_cancel hz
          have hMul := congrArg (fun x : ℕ => (S.card+1)*x) hSub
          simp only [mul_add, add_mul, one_mul] at hMul hCost ⊢
          omega
        calc
          _ ≤ ∑ _i ∈ S, b := sum_le_sum (fun i _ => hp i)
          _ = S.card*b := by simp
          _ ≤ (S.card+1)*(b-z) := hMargin
          _ ≤ T.card*(b-z) := Nat.mul_le_mul_right _ hExpand
          _ = ∑ _j ∈ T, (b-z) := by simp
          _ ≤ _ := sum_le_sum (fun j _ => hq j)
      exact hHall.trans (Nat.le_add_right _ _)
  obtain ⟨H, hH, hp', hq'⟩ :=
    DirectedMultigraphFactors.exists_matrix_of_capacity_cuts capacity p q hBalance hCuts
  refine ⟨H, fun i j hi hj => ?_, hp', hq'⟩
  exact Nat.eq_zero_of_le_zero (by simpa [capacity, hi, hj] using hH i j)

/-- For balanced counts of already covered vertices, the cycle
assignment brings every cluster up to exactly the common target. -/
theorem exists_clusterCycle_augmentation_loads
    (next : Equiv.Perm I) (hCycle : ∀ i j, next.SameCycle i j)
    (coveredA coveredB : I → ℕ) (b z : ℕ) (hz : z ≤ b)
    (hBudget : Fintype.card I*z ≤ b)
    (hA : ∀ i, coveredA i ≤ z) (hB : ∀ j, coveredB j ≤ z)
    (hBalance : (∑ i, coveredA i) = ∑ j, coveredB j) :
    ∃ H : I → I → ℕ,
      (∀ i j, j ≠ i → j ≠ next i → H i j = 0) ∧
      (∀ i, coveredA i + ∑ j, H i j = b) ∧
      (∀ j, coveredB j + ∑ i, H i j = b) := by
  have hSum (c : I → ℕ) (hc : ∀ i, c i ≤ z) :
      (∑ i, (b-c i)) + (∑ i, c i) = ∑ _i : I, b := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun i _ => Nat.sub_add_cancel ((hc i).trans hz))
  have hSA := hSum coveredA hA
  have hSB := hSum coveredB hB
  obtain ⟨H, hH, hRow, hCol⟩ := exists_clusterCycle_demand_assignment next hCycle
    (fun i => b-coveredA i) (fun i => b-coveredB i) b z hz hBudget
    (fun _ => Nat.sub_le _ _) (fun i => Nat.sub_le_sub_left (hB i) b) (by omega)
  refine ⟨H, hH, fun i => ?_, fun j => ?_⟩
  · rw [hRow, Nat.add_sub_of_le ((hA i).trans hz)]
  · rw [hCol, Nat.add_sub_of_le ((hB j).trans hz)]


/-- The cyclic order on the subclusters in §5.1.5 realizes the
augmentation loads with the same-index and successive-index pairs. -/
theorem exists_fin_clusterCycle_augmentation_loads
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (coveredA coveredB : Fin ℓ → ℕ) (b z : ℕ)
    (hBudget : ℓ*z ≤ b)
    (hA : ∀ i, coveredA i ≤ z) (hB : ∀ j, coveredB j ≤ z)
    (hBalance : (∑ i, coveredA i) = ∑ j, coveredB j) :
    ∃ H : Fin ℓ → Fin ℓ → ℕ,
      (∀ i j, j ≠ i → j ≠ finRotate ℓ i → H i j = 0) ∧
      (∀ i, coveredA i + ∑ j, H i j = b) ∧
      (∀ j, coveredB j + ∑ i, H i j = b) := by
  have hMoved (i : Fin ℓ) : finRotate ℓ i ≠ i := by
    apply Equiv.Perm.mem_support.mp
    rw [support_finRotate_of_le hℓ]
    exact mem_univ i
  have hz : z ≤ b := (by
    simpa using Nat.mul_le_mul_right z (show 1 ≤ ℓ by omega) : z ≤ ℓ*z).trans hBudget
  exact exists_clusterCycle_augmentation_loads (finRotate ℓ)
    (fun i j => (isCycle_finRotate_of_le hℓ).sameCycle (hMoved i) (hMoved j))
    coveredA coveredB b z hz (by simpa using hBudget) hA hB hBalance

/-- One greedy step in the physical augmentation. The adjacency
relation can already exclude the reserve edges used in an earlier round. -/
theorem exists_cluster_augmentation_edge
    {V : Type*} [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]
    (L R used : Finset V)
    (hLeft : (L ∩ used).card < L.card)
    (hRight : ∀ u ∈ L, u ∉ used →
      (R ∩ used).card < (R.filter (adj u)).card) :
    ∃ u ∈ L, ∃ v ∈ R, u ∉ used ∧ v ∉ used ∧ adj u v := by
  have hFree : (L \ used).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff, inter_comm used]
    omega
  obtain ⟨u, hu⟩ := hFree
  obtain ⟨huL, huFree⟩ := mem_sdiff.mp hu
  have hSub : R.filter (adj u) ∩ used ⊆ R ∩ used := by
    intro v hv
    obtain ⟨hRv, hvUsed⟩ := mem_inter.mp hv
    exact mem_inter.mpr ⟨(mem_filter.mp hRv).1, hvUsed⟩
  have hOther : ((R.filter (adj u)) \ used).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff, inter_comm used]
    exact Nat.sub_pos_of_lt ((card_le_card hSub).trans_lt (hRight u huL huFree))
  obtain ⟨v, hv⟩ := hOther
  obtain ⟨hvAdj, hvFree⟩ := mem_sdiff.mp hv
  exact ⟨u, huL, v, (mem_filter.mp hvAdj).1, huFree, hvFree, (mem_filter.mp hvAdj).2⟩

end OverfullWork.ChenShan
