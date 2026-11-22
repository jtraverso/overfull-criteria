module

public import OverfullWork.ReducedTerminalGeometry

@[expose] public section


/-! The balanced partition used in CMS §4, Subcase 2.4.
The finite construction inserts each weight into the lighter part.
It needs no positivity of individual weights. -/
namespace OverfullWork.BoundedWeightBipartition
open Finset
open scoped Classical
variable {V : Type*} [DecidableEq V]

theorem exists_balanced (Z : Finset V) (w : V → ℕ) (r : ℕ)
    (hBound : ∀ z ∈ Z, w z ≤ r) :
    ∃ A ⊆ Z, (∑ z ∈ A, w z) ≤ (∑ z ∈ Z\A, w z) ∧
      (∑ z ∈ Z\A, w z) ≤ (∑ z ∈ A, w z)+r := by
  induction Z using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simp⟩
  | @insert v S hv ih =>
    obtain ⟨A,hA,hAB,hBA⟩ := ih (fun z hz => hBound z (mem_insert_of_mem hz))
    have hvA : v ∉ A := fun h => hv (hA h)
    have hvB : v ∉ S\A := fun h => hv (mem_sdiff.mp h).1
    have hvw := hBound v (mem_insert_self v S)
    have hComp : insert v S\insert v A=S\A := by
      ext z
      by_cases hz : z=v
      · subst z; simp [hv,hvA]
      · simp [hz]
    have hComp' : insert v S\(S\A)=insert v A := by
      ext z
      have hh : z ∈ A → z ∈ S := fun h => hA h
      have hvz : z=v → z ∉ S := fun h => h ▸ hv
      simp only [mem_sdiff,mem_insert]
      tauto
    by_cases hOrder : (∑ z ∈ A, w z)+w v ≤ (∑ z ∈ S\A, w z)
    · refine ⟨insert v A,insert_subset_insert _ hA,?_,?_⟩
      · rw [hComp,sum_insert hvA];omega
      · rw [hComp,sum_insert hvA];omega
    · refine ⟨S\A,(sdiff_subset).trans (subset_insert v S),?_,?_⟩
      · rw [hComp',sum_insert hvA];omega
      · rw [hComp',sum_insert hvA];omega

theorem exists_nonempty_balanced (Z : Finset V) (w : V → ℕ) (r : ℕ)
    (hBound : ∀ z ∈ Z, w z ≤ r) (hTotal : 2*r < ∑ z ∈ Z, w z) :
    ∃ A ⊆ Z, A.Nonempty ∧ (Z\A).Nonempty ∧
      0 < (∑ z ∈ A, w z) ∧
      (∑ z ∈ A, w z) ≤ (∑ z ∈ Z\A, w z) ∧
      (∑ z ∈ Z\A, w z) ≤ (∑ z ∈ A, w z)+r := by
  obtain ⟨A,hA,hAB,hBA⟩ := exists_balanced Z w r hBound
  have hSum := sum_sdiff hA (f:=w)
  have hPosA : 0 < ∑ z ∈ A, w z := by omega
  have hPosB : 0 < ∑ z ∈ Z\A, w z := by omega
  refine ⟨A,hA,?_,?_,hPosA,hAB,hBA⟩
  · by_contra h
    have he := not_nonempty_iff_eq_empty.mp h
    simp only [he,sum_empty] at hPosA
    omega
  · by_contra h
    have he := not_nonempty_iff_eq_empty.mp h
    simp only [he,sum_empty] at hPosB
    omega

end OverfullWork.BoundedWeightBipartition
