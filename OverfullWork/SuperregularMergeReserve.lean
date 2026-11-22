module

public import OverfullWork.DirectedArcSelection
public import OverfullWork.RealDirectedRobustHamilton

@[expose] public section


/-! The expansion estimate for the auxiliary digraph in Kühn–Osthus
Lemma 6.5, used as Osthus–Staden Lemma 4.5. Lower bounds on rectangles
are retained through a bounded loss at each endpoint. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

theorem incidences_le_card_mul_indegree (D : Digraph V) (S T : Finset V) (k : ℕ)
    (hIn : ∀ v, inDegree D v ≤ k) : incidences D S T ≤ T.card*k := by
  unfold incidences
  calc
    _ ≤ ∑ _v ∈ T,k := by
      apply sum_le_sum
      intro v _
      exact (card_le_card (filter_subset_filter _ (subset_univ S))).trans (hIn v)
    _ = _ := by simp [Nat.mul_comm]

/-- Every medium source set reaches all but fewer than an ε-fraction of
the targets. The reserve can lose at most k arcs per target. -/
theorem real_robust_of_rectangles_after_deletion (D H : Digraph V) (k : ℕ)
    (hHD : H ≤ D) (d ε ν τ : ℝ)
    (hd : 0 < d) (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (hWidths : ε+ν ≤ τ) (hCost : (k:ℝ)+ν*(Fintype.card V:ℝ) ≤ d*τ*(Fintype.card V:ℝ))
    (hn : 0 < Fintype.card V)
    (hRect : ∀ S T : Finset V, ε*(Fintype.card V:ℝ) ≤ (S.card:ℝ) →
      ε*(Fintype.card V:ℝ) ≤ (T.card:ℝ) →
      d*(S.card:ℝ)*(T.card:ℝ) ≤ (incidences D S T:ℝ))
    (hLoss : ∀ v, inDegree H v ≤ k) : IsRealRobust (D \ H) ν τ := by
  intro S hS hS'
  let B := (realNeighbourhood (D \ H) ν S)ᶜ
  have hB : (B.card:ℝ) ≤ ε*(Fintype.card V:ℝ) := by
    by_contra! hBig
    have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
    have hPos : 0 < B.card := by exact_mod_cast (lt_of_le_of_lt (mul_nonneg hε hnR.le) hBig)
    have hWeak (v : V) (hv : v ∈ B) :
        (inNeighbours (D \ H) S v:ℝ) < ν*(Fintype.card V:ℝ) := by
      have h := mem_compl.mp hv
      simp only [realNeighbourhood,mem_filter,mem_univ,true_and,not_le] at h
      exact h
    have hFew : (incidences (D \ H) S B:ℝ) < (B.card:ℝ)*(ν*(Fintype.card V:ℝ)) := by
      simp only [incidences,Nat.cast_sum]
      calc
        _ < ∑ _v ∈ B,ν*(Fintype.card V:ℝ) :=
          sum_lt_sum_of_nonempty (card_pos.mp hPos) hWeak
        _ = _ := by simp
    have hLost : (incidences H S B:ℝ) ≤ (B.card:ℝ)*(k:ℝ) := by
      exact_mod_cast incidences_le_card_mul_indegree H S B k hLoss
    have hOld := hRect S B ((mul_le_mul_of_nonneg_right
      (by linarith only [hν,hWidths] : ε ≤ τ) hnR.le).trans hS) hBig.le
    have hPay : (incidences (D \ H) S B:ℝ)+(incidences H S B:ℝ) = (incidences D S B:ℝ) := by
      exact_mod_cast DirectedArcSelection.incidence_partition D H hHD S B
    have hUp : (k:ℝ)+ν*(Fintype.card V:ℝ) ≤ d*(S.card:ℝ) := by
      exact hCost.trans (by nlinarith only [mul_le_mul_of_nonneg_left hS hd.le])
    have hMult := mul_le_mul_of_nonneg_right hUp (Nat.cast_nonneg B.card)
    nlinarith only [hOld,hPay,hLost,hFew,hMult]
  have hSplit : (B.card:ℝ)+((realNeighbourhood (D \ H) ν S).card:ℝ) = (Fintype.card V:ℝ) := by
    exact_mod_cast (card_compl_add_card (realNeighbourhood (D \ H) ν S))
  have hWidth := mul_le_mul_of_nonneg_right hWidths (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  nlinarith only [hSplit,hWidth,hB,hS']

theorem residual_semidegrees (D H : Digraph V) (hHD : H ≤ D) (v : V) :
    inDegree (D \ H) v + inDegree H v = inDegree D v ∧
    outDegree (D \ H) v + outDegree H v = outDegree D v := by
  constructor
  · simpa only [incidences_degree] using DirectedArcSelection.incidence_partition D H hHD univ {v}
  · simpa only [DirectedArcSelection.incidences_outDegree] using
      DirectedArcSelection.incidence_partition D H hHD {v} univ

end OverfullWork.DirectedRobustExpansion
