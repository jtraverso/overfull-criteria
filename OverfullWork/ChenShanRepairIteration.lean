module

public import OverfullWork.ChenShanRepairNeighborhoods
public import OverfullWork.ChenShanRepairPathCounts

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*} [Fintype V]

/-- Iterative imbalance repair with an explicit allowance for previously
deleted edges and for vertices at their internal-use limit. -/
theorem exists_balanced_leave_of_repair_budgets
    (part : V → ZMod 3) (G : Finset (V × V)) (K T B : ℕ)
    (hT : 0 < T) (hTotal : 3*positiveImbalance G ≤ T*B)
    (hArc : ∀ a b, (a,b) ∈ G → part b = part a + 1)
    (hDivergence : ∀ v, (arcDivergence G v).natAbs ≤ K)
    (hOut : ∀ a, (repairClass part (part a + 1)).card + (B+2) + 2*(K+2*T) <
      2*(arcOutNeighbors G a).card)
    (hIn : ∀ b, (repairClass part (part b - 1)).card + (B+2) + 2*(K+2*T) <
      2*(arcInNeighbors G b).card) :
    ∃ D ⊆ G, ArcBalanced (G \ D) ∧ ∀ v, incidentDegree D v ≤ K+2*T := by
  have finish (p : ℕ) : ∀ (D : Finset (V × V)) (used : V → ℕ),
      D ⊆ G → (∀ v, used v ≤ T) → (∑ v, used v) + 3*p ≤ 3*positiveImbalance G →
      (∀ v, incidentDegree D v + (arcDivergence (G \ D) v).natAbs ≤ 2*used v + K) →
      positiveImbalance (G \ D) = p →
      ∃ D' ⊆ G, ArcBalanced (G \ D') ∧ ∀ v, incidentDegree D' v ≤ K+2*T := by
    induction p using Nat.strong_induction_on with
    | h p ih =>
      intro D used hD hUse hUses hDegree hP
      have hDeleted (v : V) : incidentDegree D v ≤ K+2*T := by
        have h := hUse v
        have h' := hDegree v
        omega
      by_cases hp : p = 0
      · exact ⟨D,hD,(arcBalanced_iff_positiveImbalance_eq_zero _).2 (hP.trans hp),hDeleted⟩
      have hPos : 0 < positiveImbalance (G \ D) := by omega
      obtain ⟨u,v,hu,hv⟩ := exists_opposite_arcDivergence _ hPos
      have huv : u ≠ v := by
        rintro rfl
        omega
      let F := univ.filter (fun v => T ≤ used v)
      have hF : F.card ≤ B := by
        have hBudget : T*F.card ≤ ∑ v, used v := by
          calc
            _ = ∑ _v ∈ F, T := by simp [mul_comm]
            _ ≤ ∑ v ∈ F, used v := sum_le_sum (fun v hv => (mem_filter.mp hv).2)
            _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
        apply Nat.le_of_not_gt
        intro hLt
        have h' := Nat.mul_lt_mul_of_pos_left hLt hT
        omega
      obtain ⟨l,hl,f,hStart,hEnd,hPath,hAvoid⟩ :=
        exists_short_repair_path_of_budgets part G D F (K+2*T) (B+2)
          hArc hDeleted (Nat.add_le_add_right hF _) hOut hIn u v huv
      have hPathStart : 0 < arcDivergence (G \ D) (f 0) := hStart.symm ▸ hu
      have hPathEnd : arcDivergence (G \ D) (f (Fin.last l)) < 0 := hEnd.symm ▸ hv
      have hNe : f 0 ≠ f (Fin.last l) := by simpa only [hStart,hEnd] using huv
      let C := directedPathArcs l f
      let D' := D ∪ C
      let I := pathInternalVertices f
      let used' := fun v => used v + if v ∈ I then 1 else 0
      have hD' : D' ⊆ G := union_subset hD (hPath.trans sdiff_subset)
      have hDisjoint : Disjoint D C := by
        refine disjoint_left.mpr (fun e hd hc => ?_)
        exact (mem_sdiff.mp (hPath hc)).2 hd
      have hSdiff : G \ D' = (G \ D) \ C := by
        ext e
        simp only [D',mem_sdiff,mem_union]
        tauto
      have hP' : positiveImbalance (G \ D') + 1 = p := by
        rw [hSdiff,← hP]
        exact positiveImbalance_delete_directedPath _ f hPath hPathStart hPathEnd
      have hUse' (w : V) : used' w ≤ T := by
        dsimp only [used']
        split_ifs with hI
        · obtain ⟨i,hi,hj,heq⟩ := (mem_pathInternalVertices f _).mp hI
          have hn := hAvoid i hi hj
          rw [heq] at hn
          have hn' : ¬ T ≤ used w := by simpa [F] using hn
          omega
        · simpa using hUse w
      have hUses' : (∑ w, used' w) + 3*positiveImbalance (G \ D') ≤ 3*positiveImbalance G := by
        have hCount : I.card ≤ 3 := card_pathInternalVertices_le_three f hl hNe
        have hSum : (∑ w, used' w) = (∑ w, used w) + I.card := by
          simp only [used',sum_add_distrib,← card_filter]
          simp
        rw [hSum]
        omega
      have hDegree' (w : V) :
          incidentDegree D' w + (arcDivergence (G \ D') w).natAbs ≤ 2*used' w+K := by
        have hIncidence := incidentDegree_path_eq f hNe w
        have hAbs := natAbs_arcDivergence_delete_path f hPath hPathStart hPathEnd w
        have hp := hDegree w
        rw [hSdiff,incidentDegree_union_disjoint hDisjoint]
        dsimp only [C] at *
        dsimp only [used',I]
        omega
      exact ih _ (by omega) D' used' hD' hUse' hUses' hDegree' rfl
  apply finish (positiveImbalance G) ∅ (fun _ => 0) (empty_subset _)
  · simp
  · simp
  · intro v
    simpa [incidentDegree] using hDivergence v
  · simp

end OverfullWork.ChenShan
