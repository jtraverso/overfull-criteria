module

public import OverfullWork.OsthusStadenSliceRegularity
public import OverfullWork.PurePairPreservation

@[expose] public section


/-! A deletion in each p-cell preserves superregularity, as needed after
the bridge stars of Osthus–Staden §5.5 have been installed. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

variable {V : Type*} [Fintype V]

theorem IsSuperregularPair.congr_on {D H : Digraph V} {A B : Finset V} {ε d : ℝ}
    (hD : IsSuperregularPair D ε d A B)
    (h : ∀ x ∈ A, ∀ y ∈ B, D.Adj x y ↔ H.Adj x y) :
    IsSuperregularPair H ε d A B := by
  refine ⟨(uniform_congr_on D H A B ε h).mp hD.1,?_,?_,?_⟩
  · rw [←density_congr_on D H A B h]
    exact hD.2.1
  · intro x hx
    have he : B ∩ outProfile H x = B ∩ outProfile D x := by
      ext y
      simp only [mem_inter,outProfile,mem_filter,mem_univ,true_and]
      by_cases hy : y ∈ B
      · simpa only [hy,true_and] using (h x hx y hy).symm
      · simp only [hy,false_and]
    simpa only [profileCount,he] using hD.2.2.1 x hx
  · intro y hy
    have he : A ∩ inProfile H y = A ∩ inProfile D y := by
      ext x
      simp only [mem_inter,inProfile,mem_filter,mem_univ,true_and]
      by_cases hx : x ∈ A
      · simpa only [hx,true_and] using (h x hx y hy).symm
      · simp only [hx,false_and]
    simpa only [profileCount,he] using hD.2.2.2 y hy

omit [Fintype V] in
private theorem profile_error_erase {P Q : Finset V} {x : V} {ε δ d : ℝ}
    (hx : x ∈ P) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    (hOld : |profileCount P Q-d*(P.card:ℝ)| ≤ ε*(P.card:ℝ))
    (hSize : ε*(P.card:ℝ)+1 ≤ δ*((P.erase x).card:ℝ)) :
    |profileCount (P.erase x) Q-d*((P.erase x).card:ℝ)| ≤ δ*((P.erase x).card:ℝ) := by
  have hCard : ((P.erase x).card:ℝ) = (P.card:ℝ)-1 := by
    rw [card_erase_of_mem hx,Nat.cast_sub (card_pos.mpr ⟨x,hx⟩),Nat.cast_one]
  have hMono : profileCount (P.erase x) Q ≤ profileCount P Q := by
    unfold profileCount
    exact_mod_cast card_le_card (inter_subset_inter (erase_subset x P) Subset.rfl)
  have hDiff : (P \ P.erase x).card = 1 := by
    rw [card_sdiff_of_subset (erase_subset x P),card_erase_of_mem hx]
    have h := card_pos.mpr (show P.Nonempty from ⟨x,hx⟩)
    omega
  have hGap := profile_count_dist_le P (P.erase x) Q
  rw [hDiff,sdiff_eq_empty_iff_subset.mpr (erase_subset x P),card_empty] at hGap
  rw [max_eq_left (by decide : (0:ℕ) ≤ 1),Nat.cast_one] at hGap
  change |profileCount P Q-profileCount (P.erase x) Q| ≤ 1 at hGap
  have hErr : |(profileCount (P.erase x) Q-profileCount P Q)+d| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith only [(abs_le.mp hGap).2,hd],by linarith only [hMono,hd₁]⟩
  calc
    _ = |(profileCount P Q-d*(P.card:ℝ))+((profileCount (P.erase x) Q-profileCount P Q)+d)| := by
      rw [hCard]; congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hOld hErr).trans hSize)

/-- One removal on each side costs at most one neighbour. The density
and regularity estimates are transferred by slicing. -/
theorem IsSuperregularPair.erase_one {D : Digraph V} {A B : Finset V} {x y : V} {ε δ d : ℝ}
    (hD : IsSuperregularPair D ε d A B) (hx : x ∈ A) (hy : y ∈ B)
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (hδ : 2*ε ≤ δ) (hδ₁ : δ ≤ 1)
    (hA : ε*(A.card:ℝ)+1 ≤ δ*((A.erase x).card:ℝ))
    (hB : ε*(B.card:ℝ)+1 ≤ δ*((B.erase y).card:ℝ)) :
    IsSuperregularPair D δ d (A.erase x) (B.erase y) := by
  have hAScale : (A.card:ℝ)*ε ≤ ((A.erase x).card:ℝ)*δ := by linarith only [hA]
  have hBScale : (B.card:ℝ)*ε ≤ ((B.erase y).card:ℝ)*δ := by linarith only [hB]
  have hABig := hAScale.trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hδ₁)
  have hBBig := hBScale.trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hδ₁)
  refine ⟨uniform_on_subcells D hD.1 (erase_subset x A) (erase_subset y B) hABig hBBig
    hAScale hBScale hδ,?_,?_,?_⟩
  · rw [show density D (A.erase x) (B.erase y)-d =
      (density D (A.erase x) (B.erase y)-density D A B)+(density D A B-d) by ring]
    exact (abs_add_le _ _).trans ((add_le_add
      (hD.1 _ (erase_subset x A) _ (erase_subset y B) hABig hBBig).le hD.2.1).trans
      (by linarith only [hδ]))
  · exact fun u hu => profile_error_erase hy hd hd₁ (hD.2.2.1 u (erase_subset x A hu)) hB
  · exact fun v hv => profile_error_erase hx hd hd₁ (hD.2.2.2 v (erase_subset y B hv)) hA

end OverfullWork.DirectedRobustExpansion
