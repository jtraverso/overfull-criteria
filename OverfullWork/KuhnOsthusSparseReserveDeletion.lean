module

public import OverfullWork.KuhnOsthusSparseSuccessorPairs

@[expose] public section


/-! Keep the sparse reserve hypotheses after bounded-degree deletion,
as needed by repeated applications of the path extender in Lemma 8.4. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

theorem commonInNeighbours_mono {D H : Digraph V} (h : H ≤ D) (x y : V) :
    commonInNeighbours H x y ≤ commonInNeighbours D x y := by
  apply card_le_card
  rintro u hu
  obtain ⟨_,h₁,h₂⟩ := mem_filter.mp hu
  exact mem_filter.mpr ⟨mem_univ _,h h₁,h h₂⟩

private theorem incidence_reserve_split {D H : Digraph V} (hHD : H ≤ D) (S T : Finset V) :
    (incidences (D \ H) S T:ℝ) + incidences H S T = incidences D S T := by
  simp only [incidences_eq_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  by_cases hh : H.Adj x y
  · have hd : D.Adj x y := hHD hh
    simp [Digraph.sdiff_adj,hh,hd]
  · simp [Digraph.sdiff_adj,hh]

private theorem rectangle_deletion_cost (H : Digraph V) (k : ℕ)
    (hLoss : ∀ x, inDegree H x ≤ k) (S T : Finset V) :
    (incidences H S T : ℝ) ≤ (T.card : ℝ)*k := by
  simp only [incidences,Nat.cast_sum]
  rw [←nsmul_eq_mul,←sum_const]
  apply sum_le_sum
  intro v _
  have hSub : inNeighbours H S v ≤ inDegree H v :=
    card_le_card (filter_subset_filter _ (subset_univ _))
  exact_mod_cast hSub.trans (hLoss v)

private theorem pay_rectangle_loss (H : Digraph V) (k : ℕ) (d ε ε' : ℝ)
    (hd : 0 ≤ d) (hε : ε ≤ ε') (hLoss : ∀ x, inDegree H x ≤ k)
    (hPay : (k : ℝ) ≤ (ε'-ε)*d*(ε'*Fintype.card V))
    (S T : Finset V) (hS : ε'*(Fintype.card V : ℝ) ≤ (S.card : ℝ)) :
    (incidences H S T : ℝ) ≤ (ε'-ε)*d*(S.card : ℝ)*(T.card : ℝ) := by
  have hK := hPay.trans (mul_le_mul_of_nonneg_left hS (mul_nonneg (sub_nonneg.mpr hε) hd))
  have hSpend := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg T.card : (0 : ℝ) ≤ T.card)
  exact (rectangle_deletion_cost H k hLoss S T).trans (by simpa only [mul_comm] using hSpend)

/-- Both directions of relative regularity survive the same degree
deletion budget. The nominal density is preserved. -/
theorem relative_regularity_after_bounded_deletion (D H : Digraph V) (d ε ε' : ℝ)
    (k : ℕ) (hHD : H ≤ D) (hd : 0 ≤ d) (hε : ε ≤ ε')
    (hLoss : ∀ x, inDegree H x ≤ k)
    (hPay : (k : ℝ) ≤ (ε'-ε)*d*(ε'*Fintype.card V))
    (hReg : ∀ S T : Finset V, ε*(Fintype.card V : ℝ) ≤ (S.card : ℝ) →
      ε*(Fintype.card V : ℝ) ≤ (T.card : ℝ) →
      |(incidences D S T : ℝ)-d*(S.card : ℝ)*(T.card : ℝ)| ≤ ε*d*(S.card : ℝ)*(T.card : ℝ)) :
    ∀ S T : Finset V, ε'*(Fintype.card V : ℝ) ≤ (S.card : ℝ) →
      ε'*(Fintype.card V : ℝ) ≤ (T.card : ℝ) →
      |(incidences (D \ H) S T : ℝ)-d*(S.card : ℝ)*(T.card : ℝ)| ≤
        ε'*d*(S.card : ℝ)*(T.card : ℝ) := by
  intro S T hS hT
  have hWidth := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  obtain ⟨hLo,hHi⟩ := abs_le.mp (hReg S T (hWidth.trans hS) (hWidth.trans hT))
  have hSplit := incidence_reserve_split hHD S T
  have hLoss' := pay_rectangle_loss H k d ε ε' hd hε hLoss hPay S T hS
  have hNonneg : (0 : ℝ) ≤ incidences H S T := Nat.cast_nonneg _
  have hMargin := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε hd) (Nat.cast_nonneg S.card))
    (Nat.cast_nonneg T.card)
  exact abs_le.mpr ⟨by linarith only [hSplit,hLo,hLoss'],by linarith only [hSplit,hHi,hNonneg,hMargin]⟩

/-- Proposition 4.8 in normalized coordinates for the two kinds
of extender pair. A zero semidegree floor applies to the chord pairs. -/
theorem SparseSuccessorPairBounds.after_bounded_deletion
    {D H : Digraph V} {d ε ε' μ ζ ζ' : ℝ} (h : SparseSuccessorPairBounds D d ε μ ζ)
    (k : ℕ) (hHD : H ≤ D) (hd : 0 ≤ d) (hε : ε ≤ ε')
    (hLoss : ∀ x, inDegree H x ≤ k ∧ outDegree H x ≤ k)
    (hPayDegree : ζ' ≤ 0 ∨ (k : ℝ) ≤ (ζ-ζ')*d*Fintype.card V)
    (hPayDensity : (k : ℝ) ≤ (ε'-ε)*d*(ε'*Fintype.card V)) :
    SparseSuccessorPairBounds (D \ H) d ε' μ ζ' := by
  have hDegree {a b c : ℕ} (he : a+b = c) (hb : b ≤ k)
      (hc : ζ*d*(Fintype.card V : ℝ) ≤ (c : ℝ)) :
      ζ'*d*(Fintype.card V : ℝ) ≤ (a : ℝ) := by
    rcases hPayDegree with hz | hPay
    · exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hz hd)
        (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)
    · have he' : (a : ℝ)+b = c := by exact_mod_cast he
      have hb' : (b : ℝ) ≤ k := by exact_mod_cast hb
      linarith only [he',hb',hc,hPay]
  constructor
  · intro x
    exact hDegree (residual_semidegrees D H hHD x).1 (hLoss x).1 (h.in_degree x)
  · intro x
    exact hDegree (residual_semidegrees D H hHD x).2 (hLoss x).2 (h.out_degree x)
  · intro x y hxy
    have hLe : D \ H ≤ D := fun _ _ he => he.1
    have hlo : (commonInNeighbours (D \ H) x y : ℝ) ≤ commonInNeighbours D x y := by
      exact_mod_cast commonInNeighbours_mono hLe x y
    exact hlo.trans (h.in_codegree x y hxy)
  · intro x y hxy
    have hLe : reverseArcs (D \ H) ≤ reverseArcs D := fun _ _ he => he.1
    have hlo : (commonInNeighbours (reverseArcs (D \ H)) x y : ℝ) ≤
        commonInNeighbours (reverseArcs D) x y := by
      exact_mod_cast commonInNeighbours_mono hLe x y
    exact hlo.trans (h.out_codegree x y hxy)
  · intro S T hS hT
    have hWidth := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
    have hReg := h.rectangle S T (hWidth.trans hS) (hWidth.trans hT)
    have hLoss' := pay_rectangle_loss H k d ε ε' hd hε (fun x => (hLoss x).1) hPayDensity S T hS
    linarith only [incidence_reserve_split hHD S T,hReg,hLoss']

/-- A per-vertex deletion budget pays for the semidegree losses and for
all large rectangles. The absolute bounds on codegrees are preserved. -/
theorem sparse_pair_robust_after_bounded_deletion (D H : Digraph V)
    (d ε ε' μ ζ ζ' ν τ : ℝ) (k : ℕ) (hV : 0 < Fintype.card V)
    (hHD : H ≤ D)
    (hLoss : ∀ x, inDegree H x ≤ k ∧ outDegree H x ≤ k)
    (hd : 0 < d) (hε : 0 < ε) (hε' : ε ≤ ε') (hε1 : ε' < 1)
    (hμ : 0 < μ) (hζ' : 0 < ζ') (hν : 0 < ν) (hτ : 2*ν ≤ τ)
    (hScale : 160*ε' ≤ (ζ'*μ)^2)
    (hDiagonal : 16*(Fintype.card V:ℝ) ≤ (ζ'*d*Fintype.card V)^2)
    (hDiscard : 8*ν ≤ τ*(ζ'*d)^2)
    (hνDensity : ν < (1-ε')*d*ε')
    (hPayDegree : (k:ℝ) ≤ (ζ-ζ')*d*Fintype.card V)
    (hPayDensity : (k:ℝ) ≤ (ε'-ε)*d*(ε'*Fintype.card V))
    (hIn : ∀ x, ζ*d*(Fintype.card V:ℝ) ≤ (inDegree D x:ℝ))
    (hOut : ∀ x, ζ*d*(Fintype.card V:ℝ) ≤ (outDegree D x:ℝ))
    (hCodegIn : ∀ x y, x ≠ y →
      (commonInNeighbours D x y:ℝ) ≤ (d/μ)^2*Fintype.card V)
    (hCodegOut : ∀ x y, x ≠ y →
      (commonInNeighbours (reverseArcs D) x y:ℝ) ≤ (d/μ)^2*Fintype.card V)
    (hReg : ∀ S T : Finset V, ε*(Fintype.card V:ℝ) ≤ (S.card:ℝ) →
      ε*(Fintype.card V:ℝ) ≤ (T.card:ℝ) →
      (1-ε)*d*(S.card:ℝ)*(T.card:ℝ) ≤ (incidences D S T:ℝ)) :
    IsRealRobust (D \ H) ν τ := by
  have hPair : SparseSuccessorPairBounds D d ε μ ζ :=
    ⟨hIn,hOut,hCodegIn,hCodegOut,hReg⟩
  have hRest := hPair.after_bounded_deletion k hHD hd.le hε' hLoss (Or.inr hPayDegree) hPayDensity
  exact kuhn_osthus_sparse_pair_expansion (D \ H) d ε' μ ζ' ν τ hV hd (hε.trans_le hε')
    hε1 hμ hζ' hν hτ hScale hDiagonal hDiscard hνDensity
    hRest.in_degree hRest.out_degree hRest.in_codegree hRest.out_codegree hRest.rectangle

end OverfullWork.DirectedRobustExpansion
