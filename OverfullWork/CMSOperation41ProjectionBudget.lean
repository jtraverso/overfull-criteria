module

public import OverfullWork.LowSkeletonProjection

@[expose] public section


/-! Claim 4.1(7) limits freely selected core representatives.
The previously used representatives are counted by their incidence
with the earlier rounds, and saturated vertices are forbidden in
the next actual projection. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V J : Type*} [Fintype V] [DecidableEq V]

def projectionLoad (history : Finset J) (used : J → Finset V) (v : V) : ℕ :=
  (history.filter fun i => v ∈ used i).card

theorem sum_projection_load (history : Finset J) (used : J → Finset V) :
    (∑ v : V,projectionLoad history used v) = ∑ i ∈ history,(used i).card := by
  calc
    _ = ∑ v : V,∑ i ∈ history,if v ∈ used i then 1 else 0 := by
      apply sum_congr rfl
      intro v _
      rw [projectionLoad,card_eq_sum_ones,sum_filter]
    _ = ∑ i ∈ history,∑ v : V,if v ∈ used i then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      rw [card_eq_sum_ones,←sum_filter]
      simp

theorem saturated_projection_card_le (history : Finset J) (used : J → Finset V)
    (cap k b : ℕ) (hCap : 0 < cap) (hUsed : ∀ i ∈ history,(used i).card ≤ b)
    (hTotal : history.card*b ≤ k*cap) :
    (univ.filter fun v : V => cap ≤ projectionLoad history used v).card ≤ k := by
  let S : Finset V := univ.filter fun v => cap ≤ projectionLoad history used v
  have hLoad : S.card*cap ≤ ∑ v : V,projectionLoad history used v := by
    calc
      _ = ∑ _v ∈ S,cap := by simp
      _ ≤ ∑ v ∈ S,projectionLoad history used v :=
        sum_le_sum (fun v hv => (mem_filter.mp hv).2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have hBound : (∑ i ∈ history,(used i).card) ≤ history.card*b := by
    calc
      _ ≤ ∑ _i ∈ history,b := sum_le_sum hUsed
      _ = _ := by simp
  rw [sum_projection_load] at hLoad
  exact (Nat.le_of_mul_le_mul_right (hLoad.trans (hBound.trans hTotal)) hCap)

theorem exists_projection_with_free_load_cap (G : SimpleGraph V) [DecidableRel G.Adj]
    (A U Z : Finset V) (history : Finset J) (used : J → Finset V)
    (cap k b : ℕ) (hCap : 0 < cap) (hUsed : ∀ i ∈ history,(used i).card ≤ b)
    (hTotal : history.card*b ≤ k*cap)
    (hDegree : ∀ v ∈ A ∩ U,U.card + A.card + Z.card + k ≤ G.degree v) :
    let S := univ.filter fun v : V => cap ≤ projectionLoad history used v
    ∃ P : LowSkeletonProjection.Projection G A U (Z ∪ S),
      ∀ a : A,a.val ∈ U → projectionLoad history used (P.representative a).val < cap := by
  intro S
  have hCard : S.card ≤ k := saturated_projection_card_le history used cap k b hCap hUsed hTotal
  obtain ⟨P⟩ := LowSkeletonProjection.exists_projection G A U (Z ∪ S) (by
    intro v hv
    have h := card_union_le Z S
    have hh := hDegree v hv
    omega)
  refine ⟨P,?_⟩
  intro a ha
  by_contra! h
  have hRep : (P.representative a).val ∈ S := mem_filter.mpr ⟨mem_univ _,h⟩
  exact P.fresh a ha (mem_union_right A (mem_union_right Z hRep))

end OverfullWork.CMSTrimmingRound
