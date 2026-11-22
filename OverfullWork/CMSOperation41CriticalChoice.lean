module

public import OverfullWork.OddCutDeficit

@[expose] public section


/-! The critical-case choice in Operation 4.1 uses auxiliary degrees
rather than the degrees of the graph that still contains unchosen core
edges. The almost-overfull test forces at least two exceptional vertices. -/
namespace OverfullWork.CMSTrimmingRound

open Finset
open scoped Classical

variable {V : Type*} [DecidableEq V]

def HasAlmostOverfullRecord (active : Finset V) (d budget : ℕ) (degree : V → ℕ) : Prop :=
  ∃ X ⊆ active,Odd X.card ∧
    (∑ v ∈ X,(d-degree v))+(∑ v ∈ active \ X,degree v) ≤ d+budget

theorem critical_choice_two_exceptional (active U : Finset V) (hU : U ⊆ active)
    (d budget : ℕ) (degree : V → ℕ) (hBudget : 1 ≤ budget)
    (hBound : ∀ v ∈ active,degree v ≤ d) (hOdd : Odd (active \ U).card)
    (hMass : (∑ v ∈ active \ U,(d-degree v)) ≤ 1)
    (hNo : ¬HasAlmostOverfullRecord active d budget degree) : 2 ≤ U.card := by
  by_contra! hSmall
  have hCompl : active \ (active \ U) = U := by
    ext v
    simp only [mem_sdiff,not_and,not_not]
    exact ⟨fun ⟨_,h⟩ => h (by assumption),fun h => ⟨hU h,fun _ => h⟩⟩
  have hSum : (∑ v ∈ U,degree v) ≤ d := by
    have h₁ : (∑ v ∈ U,degree v) ≤ U.card*d := by
      calc
        _ ≤ ∑ _v ∈ U,d := sum_le_sum (fun v hv => hBound v (hU hv))
        _ = _ := by simp
    have h₂ := Nat.mul_le_mul_right d (show U.card ≤ 1 by omega)
    omega
  apply hNo
  refine ⟨active \ U,sdiff_subset,hOdd,?_⟩
  rw [hCompl]
  omega

theorem exists_critical_active_vertices (active U : Finset V) (hU : U ⊆ active)
    (d budget : ℕ) (degree : V → ℕ) (hBudget : 1 ≤ budget)
    (hBound : ∀ v ∈ active,degree v ≤ d) (hOdd : Odd (active \ U).card)
    (hMass : (∑ v ∈ active \ U,(d-degree v)) ≤ 1)
    (hNo : ¬HasAlmostOverfullRecord active d budget degree) :
    ∃ T ⊆ U,(Even active.card ↔ T.card = 2) ∧
      ((Even U.card ∧ ∃ a ∈ U,T = {a} ∧ ∀ v ∈ U,degree a ≤ degree v) ∨
        (Odd U.card ∧ ∃ a ∈ U,∃ b ∈ U,a ≠ b ∧ T = {a,b} ∧
          (∀ v ∈ U,degree a ≤ degree v) ∧ ∀ v ∈ U,v ≠ a → degree b ≤ degree v)) := by
  have hTwo := critical_choice_two_exceptional active U hU d budget degree hBudget hBound hOdd hMass hNo
  obtain ⟨a,ha,hMin⟩ := U.exists_min_image degree (card_pos.mp (by omega))
  have hCard : (active \ U).card+U.card = active.card := card_sdiff_add_card_eq_card hU
  by_cases he : Even U.card
  · have hActive : Odd active.card := by
      obtain ⟨k,hk⟩ := hOdd
      obtain ⟨j,hj⟩ := he
      exact ⟨k+j,by omega⟩
    refine ⟨{a},singleton_subset_iff.mpr ha,?_,Or.inl ⟨he,a,ha,rfl,hMin⟩⟩
    simp [(Nat.not_even_iff_odd.mpr hActive)]
  · have ho := Nat.not_even_iff_odd.mp he
    have hActive : Even active.card := by
      obtain ⟨k,hk⟩ := hOdd
      obtain ⟨j,hj⟩ := ho
      exact ⟨k+j+1,by omega⟩
    have hErase : 0 < (U.erase a).card := by rw [card_erase_of_mem ha]; omega
    obtain ⟨b,hb,hSecond⟩ := (U.erase a).exists_min_image degree (card_pos.mp hErase)
    have hbU := (mem_erase.mp hb).2
    have hba := (mem_erase.mp hb).1
    refine ⟨{a,b},insert_subset_iff.mpr ⟨ha,singleton_subset_iff.mpr hbU⟩,
      by simp [hActive,card_pair hba.symm],Or.inr ⟨ho,a,ha,b,hbU,hba.symm,rfl,hMin,?_⟩⟩
    exact fun v hv hva => hSecond v (mem_erase.mpr ⟨hva,hv⟩)

end OverfullWork.CMSTrimmingRound
