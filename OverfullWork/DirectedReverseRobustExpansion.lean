module

public import OverfullWork.DirectedRobustExpansion

@[expose] public section


/-! The finite incidence-count argument for Lo–Patel, Proposition 3.2. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

def reverse (D : Digraph V) : Digraph V := ⟨fun x y => D.Adj y x⟩

omit [Fintype V] in
private theorem incidences_reverse (D : Digraph V) (S T : Finset V) :
    incidences D S T = incidences (reverse D) T S := by
  change (∑ v ∈ T, (S.filter fun u => D.Adj u v).card) =
    ∑ u ∈ S, (T.filter fun v => D.Adj u v).card
  simp only [card_filter]
  rw [sum_comm]

omit [Fintype V] in
private theorem incidences_ge (D : Digraph V) (S T : Finset V) (k : ℕ)
    (h : ∀ v ∈ T, k ≤ inNeighbours D S v) :
    T.card*k ≤ incidences D S T := by
  simpa [incidences] using (sum_le_sum h :
    (∑ _v ∈ T, k) ≤ ∑ v ∈ T, inNeighbours D S v)

omit [Fintype V] in
private theorem incidences_le (D : Digraph V) (S T : Finset V) (k : ℕ)
    (h : ∀ v ∈ T, inNeighbours D S v ≤ k) :
    incidences D S T ≤ T.card*k := by
  simpa [incidences] using (sum_le_sum h :
    (∑ v ∈ T, inNeighbours D S v) ≤ ∑ _v ∈ T, k)

/-- Robust out-expansion gives robust in-expansion with an explicit
integer loss. The upper budget on `s` is quadratic in `r` at fixed order. -/
theorem reverse_robust_of_robust (D : Digraph V) {r s t : ℕ}
    (hs : 0 < s) (hsr : s ≤ r) (hrt : r ≤ t)
    (hBudget : s*Fintype.card V ≤ r*(r-s))
    (hIn : ∀ v, 2*t ≤ inDegree D v)
    (hD : IsRobustAt D r t) : IsRobustAt (reverse D) s (2*t) := by
  intro S hSlo hShi
  by_contra hFail
  let B := neighbourhood (reverse D) s S
  let T := univ \ B
  let C := neighbourhood D r T ∩ S
  change ¬ S.card+s ≤ B.card at hFail
  have hBC : B.card+T.card = Fintype.card V := by
    rw [add_comm]
    exact (card_sdiff_add_card_eq_card (subset_univ B)).trans card_univ
  have hBad : B.card < S.card+s := Nat.lt_of_not_ge hFail
  have hTlo : t ≤ T.card := by omega
  have hSmall : ∀ v ∈ T, inNeighbours (reverse D) S v ≤ s := by
    intro v hv
    have h := (mem_sdiff.mp hv).2
    simp only [B, neighbourhood, mem_filter, mem_univ, true_and, not_le] at h
    omega
  have hEdgeBound := incidences_le (reverse D) S T s hSmall
  rw [← incidences_reverse] at hEdgeBound
  have hBound := hEdgeBound.trans (Nat.mul_le_mul_right s (card_le_univ T))
  rw [Nat.mul_comm _ s] at hBound
  have hBlo : t ≤ B.card := by
    by_contra h
    have hDeg : ∀ v ∈ S, t+1 ≤ inNeighbours D T v := by
      intro v _
      have hTotal := hIn v
      have hDisj := card_le_card_sdiff_add_card
        (s := univ.filter (fun u => D.Adj u v)) (t := B)
      have hEq : (univ.filter (fun u => D.Adj u v) \ B).card = inNeighbours D T v := by
        congr 1
        ext u
        simp [T, and_comm]
      change 2*t ≤ (univ.filter (fun u => D.Adj u v)).card at hTotal
      omega
    have hLower := incidences_ge D T S (t+1) hDeg
    have hStrict : r*(r-s) < S.card*(t+1) := by
      apply Nat.mul_lt_mul_of_le_of_lt (by omega) (by omega)
      omega
    omega
  have hGrow := hD T hTlo (by omega)
  have hClo : r-s+1 ≤ C.card := by
    have hPart := card_union_add_card_inter (neighbourhood D r T) S
    have hUniv := card_le_univ (neighbourhood D r T ∪ S)
    change r-s+1 ≤ (neighbourhood D r T ∩ S).card
    omega
  have hCdeg : ∀ v ∈ C, r ≤ inNeighbours D T v := by
    intro v hv
    exact (mem_filter.mp (mem_inter.mp hv).1).2
  have hLower := incidences_ge D T C r hCdeg
  have hSub : incidences D T C ≤ incidences D T S := sum_le_sum_of_subset inter_subset_right
  have hStrict : r*(r-s) < C.card*r := by
    rw [Nat.mul_comm r (r-s)]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  omega

end OverfullWork.DirectedRobustExpansion
