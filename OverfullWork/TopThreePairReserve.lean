module

public import OverfullWork.ThreeLargestVertices

@[expose] public section


/-! Pair reserve after removing one copy at each of the three largest weights. -/
namespace OverfullWork.TopThreePairReserve
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem pair_bound (Y U : Finset V) (w r : V → ℕ) (D : ℕ) (hD : 4 ≤ D)
    (hU : U ⊆ Y) (hThree : U.card=3) (hPositive : ∀ u ∈ U, 2 ≤ w u)
    (hTop : ∀ u ∈ U, ∀ v ∈ Y, v ∉ U → w v ≤ w u)
    (hNonmax : ∀ v ∈ Y, w v < D)
    (hLight : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → w y+w z < D+2)
    (hPoint : ∀ v ∈ Y, r v+(if v ∈ U then 1 else 0)=w v)
    (hTotal : (∑ v ∈ Y, r v)+3=∑ v ∈ Y, w v)
    (hLarge : D+2 ≤ ∑ v ∈ Y, w v) :
    ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 2*(r y+r z) ≤ (∑ v ∈ Y, r v)+(D-1) := by
  have hRest : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z →
      (∑ v ∈ (Y.erase y).erase z, w v)+w y+w z=∑ v ∈ Y, w v := by
    intro y hy z hz hyz
    have h₁ := sum_erase_add Y w hy
    have h₂ := sum_erase_add (Y.erase y) w (mem_erase.mpr ⟨hyz.symm,hz⟩)
    omega
  have hOne : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → y ∈ U → z ∉ U →
      2*(r y+r z) ≤ (∑ v ∈ Y, r v)+(D-1) := by
    intro y hy z hz hyz hyU hzU
    have hSub : U.erase y ⊆ (Y.erase y).erase z := by
      intro v hv
      exact mem_erase.mpr ⟨by intro he;exact hzU (he ▸ (mem_erase.mp hv).2),
        mem_erase.mpr ⟨(mem_erase.mp hv).1,hU (mem_erase.mp hv).2⟩⟩
    have hSum := sum_le_sum_of_subset_of_nonneg hSub (f := w) (fun _ _ _ => Nat.zero_le _)
    have hLower := sum_le_sum (s := U.erase y) (fun v hv => hTop v (mem_erase.mp hv).2 z hz hzU)
    have hTwo := sum_le_sum (s := U.erase y) (fun v hv => hPositive v (mem_erase.mp hv).2)
    simp only [sum_const,smul_eq_mul,card_erase_of_mem hyU,hThree] at hLower hTwo
    have hyPoint := hPoint y hy
    have hzPoint := hPoint z hz
    rw [if_pos hyU] at hyPoint
    rw [if_neg hzU] at hzPoint
    have hN := hNonmax y hy
    have hR := hRest y hy z hz hyz
    omega
  intro y hy z hz hyz
  by_cases hyU : y ∈ U
  · by_cases hzU : z ∈ U
    · have hL := hLight y hy z hz hyz
      have hY := hPoint y hy
      have hZ := hPoint z hz
      rw [if_pos hyU] at hY
      rw [if_pos hzU] at hZ
      omega
    · exact hOne y hy z hz hyz hyU hzU
  · by_cases hzU : z ∈ U
    · have hh := hOne z hz y hy hyz.symm hzU hyU
      omega
    · have hSub : U ⊆ (Y.erase y).erase z := by
        intro v hv
        exact mem_erase.mpr ⟨by intro he;exact hzU (he ▸ hv),
          mem_erase.mpr ⟨by intro he;exact hyU (he ▸ hv),hU hv⟩⟩
      have hSum := sum_le_sum_of_subset_of_nonneg hSub (f := w) (fun _ _ _ => Nat.zero_le _)
      have hYBound := sum_le_sum (s := U) (fun v hv => hTop v hv y hy hyU)
      have hZBound := sum_le_sum (s := U) (fun v hv => hTop v hv z hz hzU)
      simp only [sum_const,smul_eq_mul,hThree] at hYBound hZBound
      have hY := hPoint y hy
      have hZ := hPoint z hz
      rw [if_neg hyU] at hY
      rw [if_neg hzU] at hZ
      have hR := hRest y hy z hz hyz
      omega

end OverfullWork.TopThreePairReserve
