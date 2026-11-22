module

public import OverfullWork.FreshCentreBundleReserves

@[expose] public section


/-! Weighted first-anchor reserve after excluding the two Stage I vertices. -/
namespace SimpleGraph.MultiGraph.PartialColouring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 24000000

theorem first_anchor_mass_of_two_light_blockers (S : M.PartialColouring k)
    (A : Finset V) (a b : V) (D : ℕ) (i : Fin k) (L U : ℝ)
    (ha : a ∈ A) (hRegular : M.IsRegularOfDegree D) (hCover : S.CoversInternal A)
    (hCard : (Aᶜ\S.colouring.missingSet Aᶜ i).card ≤ 2)
    (hL : 0 ≤ L) (hU : (S.available.mult s(a,b):ℝ) ≤ U)
    (hLight : ∀ v ∈ Aᶜ, v ≠ b → (M.mult s(a,v):ℝ) ≤ L)
    (hReserve : (k:ℝ)+U+2*L < D) :
    0 < S.available.degreeInto (S.colouring.missingSet Aᶜ i) a := by
  let Z := Aᶜ\S.colouring.missingSet Aᶜ i
  have hInside : S.available.degreeInto A a=0 := by
    apply sum_eq_zero
    intro v hv
    change M.mult s(a,v)-S.graph.mult s(a,v)=0
    rw [hCover a v (by tauto),Nat.sub_self]
  have hSplit := S.available.degreeInto_add_compl A a
  have hDegree := S.available_degree a
  have hPalette := S.colouring.degree_le_palette a
  rw [hRegular a] at hDegree
  have hOutside : D ≤ S.available.degreeInto Aᶜ a+k := by omega
  have hBlocked : (S.available.degreeInto Z a:ℝ) ≤ U+2*L := by
    have hPoint : ∀ v ∈ Z, (S.available.mult s(a,v):ℝ) ≤
        (if v=b then (S.available.mult s(a,b):ℝ) else 0)+L := by
      intro v hv
      by_cases hvb : v=b
      · simp only [hvb,ite_true];linarith
      · have hm : (S.available.mult s(a,v):ℝ) ≤ M.mult s(a,v) := by exact_mod_cast Nat.sub_le (M.mult s(a,v)) (S.graph.mult s(a,v))
        have hl := hLight v (mem_sdiff.mp hv).1 hvb
        simp only [if_neg hvb];linarith
    have hSum := sum_le_sum hPoint
    rw [sum_add_distrib] at hSum
    have hOne : (∑ v ∈ Z, if v=b then (S.available.mult s(a,b):ℝ) else 0) ≤ U := by
      simp only [sum_ite_eq',sum_const_zero]
      split_ifs <;> linarith [show (0:ℝ) ≤ S.available.mult s(a,b) from Nat.cast_nonneg _]
    have hCount : (Z.card:ℝ) ≤ 2 := by exact_mod_cast hCard
    have hConst : (∑ _v ∈ Z, L) ≤ 2*L := by simpa using mul_le_mul_of_nonneg_right hCount hL
    have hCast : (S.available.degreeInto Z a:ℝ)=(∑ v ∈ Z, (S.available.mult s(a,v):ℝ)) := by simp only [MultiGraph.degreeInto,Nat.cast_sum]
    linarith
  have hMissingSubset : S.colouring.missingSet Aᶜ i ⊆ Aᶜ := filter_subset _ _
  have hSum := sum_sdiff (f := fun v => S.available.mult s(a,v)) hMissingSubset
  change S.available.degreeInto Z a+S.available.degreeInto (S.colouring.missingSet Aᶜ i) a=
    S.available.degreeInto Aᶜ a at hSum
  have hOutsideR : (D:ℝ) ≤ (S.available.degreeInto Aᶜ a:ℝ)+(k:ℝ) := by exact_mod_cast hOutside
  have hSumR : (S.available.degreeInto Z a:ℝ)+(S.available.degreeInto (S.colouring.missingSet Aᶜ i) a:ℝ)=
    S.available.degreeInto Aᶜ a := by exact_mod_cast hSum
  exact_mod_cast (show (0:ℝ) < S.available.degreeInto (S.colouring.missingSet Aᶜ i) a by linarith)

theorem first_anchor_mass_of_missing_candidate (S : M.PartialColouring k)
    (A : Finset V) (a v : V) (i : Fin k)
    (hv : v ∈ S.colouring.missingSet Aᶜ i) (hCopy : 0 < S.available.mult s(a,v)) :
    0 < S.available.degreeInto (S.colouring.missingSet Aᶜ i) a :=
  sum_pos_iff.mpr ⟨v,hv,hCopy⟩

end SimpleGraph.MultiGraph.PartialColouring
