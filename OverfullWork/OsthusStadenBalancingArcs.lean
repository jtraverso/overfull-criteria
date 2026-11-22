module

public import OverfullWork.OsthusStadenShadowBalance
public import OverfullWork.DirectedArcSelection
public import OverfullWork.DirectedRegularPairs

@[expose] public section


/-! Sparse exact-size choices for Osthus–Staden Lemma 3.9 and §5.9.
The greedy choice uses the actual remaining ordered arcs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

noncomputable def arcRectangle {V : Type*} (D : Digraph V) (A B : Finset V) : Finset (V × V) :=
  (A ×ˢ B).filter (fun uv => D.Adj uv.1 uv.2)

theorem mem_arcRectangle {V : Type*} (D : Digraph V) (A B : Finset V) (e : V × V) :
    e ∈ arcRectangle D A B ↔ e.1 ∈ A ∧ e.2 ∈ B ∧ D.Adj e.1 e.2 := by
  simp [arcRectangle,and_assoc]

theorem card_arcRectangle {V : Type*} (D : Digraph V) (A B : Finset V) :
    (arcRectangle D A B).card = incidences D A B := by
  unfold arcRectangle
  rw [card_filter,sum_product,sum_comm]
  simp only [incidences,inNeighbours,card_filter]

/-- A greedy exact-size arc set with separate outgoing and incoming
caps. Any large rectangle must contain at least the requested number
of arcs, after earlier batches have been removed. -/
theorem exists_sparse_arc_selection {V : Type*} [Fintype V]
    (D : Digraph V) (A B : Finset V) (q cap loss : ℕ)
    (hcap : 0 < cap) (hLoss : q ≤ cap*loss)
    (hDense : ∀ X ⊆ A, ∀ Y ⊆ B, A.card ≤ X.card+loss → B.card ≤ Y.card+loss →
      q ≤ incidences D X Y) :
    ∃ C ⊆ arcRectangle D A B, C.card = q ∧
      (∀ x, (C.filter (fun e => e.1 = x)).card ≤ cap) ∧
      ∀ y, (C.filter (fun e => e.2 = y)).card ≤ cap := by
  suffices h : ∀ n ≤ q, ∃ C ⊆ arcRectangle D A B, C.card = n ∧
      (∀ x, (C.filter (fun e => e.1 = x)).card ≤ cap) ∧
      ∀ y, (C.filter (fun e => e.2 = y)).card ≤ cap from h q le_rfl
  intro n hn
  induction n with
  | zero => exact ⟨∅,empty_subset _,rfl,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨C,hC,hCard,hOut,hIn⟩ := ih (Nat.le_of_succ_le hn)
    let bad (S : Finset V) (f : V × V → V) :=
      S.filter (fun x => cap ≤ (C.filter (fun e => f e = x)).card)
    have hBad (S : Finset V) (f : V × V → V) : (bad S f).card ≤ loss := by
      have h := sum_le_sum (s := bad S f) (fun x hx => (mem_filter.mp hx).2)
      simp only [sum_const,Nat.nsmul_eq_mul] at h
      have hSum := sum_card_fiberwise_eq_card_filter C (bad S f) f
      have hBound := card_le_card (filter_subset (fun e => f e ∈ bad S f) C)
      have hMul : cap*(bad S f).card ≤ cap*loss := by
        rw [Nat.mul_comm cap]
        exact h.trans (hSum.le.trans (hBound.trans (by omega)))
      exact Nat.le_of_mul_le_mul_left hMul hcap
    let X := A \ bad A Prod.fst
    let Y := B \ bad B Prod.snd
    have hX : A.card ≤ X.card+loss := by
      have h := card_sdiff_add_card_eq_card (filter_subset _ A :
        bad A Prod.fst ⊆ A)
      change X.card + (bad A Prod.fst).card = A.card at h
      have h' := hBad A Prod.fst
      omega
    have hY : B.card ≤ Y.card+loss := by
      have h := card_sdiff_add_card_eq_card (filter_subset _ B :
        bad B Prod.snd ⊆ B)
      change Y.card + (bad B Prod.snd).card = B.card at h
      have h' := hBad B Prod.snd
      omega
    have hCount : C.card < (arcRectangle D X Y).card := by
      rw [hCard,card_arcRectangle]
      exact hn.trans (hDense X sdiff_subset Y sdiff_subset hX hY)
    obtain ⟨e,he,hNo⟩ := exists_mem_notMem_of_card_lt_card hCount
    have hXY := mem_product.mp (mem_filter.mp he).1
    have hFrom : (C.filter (fun z => z.1 = e.1)).card < cap := by
      by_contra! hf
      exact (mem_sdiff.mp hXY.1).2 (mem_filter.mpr ⟨(mem_sdiff.mp hXY.1).1,hf⟩)
    have hTo : (C.filter (fun z => z.2 = e.2)).card < cap := by
      by_contra! hf
      exact (mem_sdiff.mp hXY.2).2 (mem_filter.mpr ⟨(mem_sdiff.mp hXY.2).1,hf⟩)
    have hEdge : e ∈ arcRectangle D A B := mem_filter.mpr
      ⟨mem_product.mpr ⟨(mem_sdiff.mp hXY.1).1,(mem_sdiff.mp hXY.2).1⟩,(mem_filter.mp he).2⟩
    refine ⟨insert e C,insert_subset hEdge hC,by rw [card_insert_of_notMem hNo,hCard],?_,?_⟩
    · intro x
      by_cases hx : e.1 = x
      · subst x
        rw [filter_insert,if_pos rfl,card_insert_of_notMem (fun h => hNo (mem_filter.mp h).1)]
        exact hFrom
      · rw [filter_insert,if_neg hx]
        exact hOut x
    · intro y
      by_cases hy : e.2 = y
      · subst y
        rw [filter_insert,if_pos rfl,card_insert_of_notMem (fun h => hNo (mem_filter.mp h).1)]
        exact hTo
      · rw [filter_insert,if_neg hy]
        exact hIn y

/-- A reserve remains usable after restricting to the aligned cells and
deleting the arcs already assigned to previous layers. It suffices to
keep the lower density on the rectangles examined by the greedy proof. -/
theorem exists_sparse_balancing_arcs {V : Type*} [Fintype V]
    (D used : Digraph V) (A B A' B' : Finset V) (ε d : ℝ)
    (q cap loss a b L : ℕ)
    (hR : DirectedRegularPairs.IsUniform D ε A B)
    (hD : d ≤ DirectedRegularPairs.density D A B)
    (hA : A' ⊆ A) (hB : B' ⊆ B)
    (ha : 0 < a) (hb : 0 < b) (hcap : 0 < cap) (hLoss : q ≤ cap*loss)
    (hSizeA : a+loss ≤ A'.card) (hSizeB : b+loss ≤ B'.card)
    (hLargeA : (A.card:ℝ)*ε ≤ a) (hLargeB : (B.card:ℝ)*ε ≤ b)
    (hUsed : ∀ v, inDegree used v ≤ L)
    (hCoeff : 0 ≤ d-ε) (hSlack : 0 ≤ (d-ε)*(a:ℝ)-(L:ℝ))
    (hNeed : (q:ℝ) ≤ ((d-ε)*(a:ℝ)-(L:ℝ))*(b:ℝ)) :
    ∃ C ⊆ arcRectangle (D \ used) A' B', C.card = q ∧
      (∀ x, (C.filter (fun e => e.1 = x)).card ≤ cap) ∧
      ∀ y, (C.filter (fun e => e.2 = y)).card ≤ cap := by
  apply exists_sparse_arc_selection (D \ used) A' B' q cap loss hcap hLoss
  intro X hX Y hY hXL hYL
  have hx : a ≤ X.card := by omega
  have hy : b ≤ Y.card := by omega
  have hDx := DirectedRegularPairs.uniform_incidences_lower D hR hD (hX.trans hA) (hY.trans hB)
    (hLargeA.trans (by exact_mod_cast hx)) (hLargeB.trans (by exact_mod_cast hy))
    (card_pos.mp (ha.trans_le hx)) (card_pos.mp (hb.trans_le hy))
  have hConsume : incidences used X Y ≤ L*Y.card :=
    DirectedRegularPairs.incidences_le_of_neighbour_bound used X Y L (fun v _ =>
      (card_le_card (filter_subset_filter _ (subset_univ X))).trans (hUsed v))
  have hDiff : arcRectangle D X Y \ arcRectangle used X Y = arcRectangle (D \ used) X Y := by
    ext e
    simp only [arcRectangle,mem_sdiff,mem_filter,Digraph.sdiff_adj]
    tauto
  have hKeep : incidences D X Y ≤ incidences (D \ used) X Y + incidences used X Y := by
    have h := card_le_card_sdiff_add_card (s := arcRectangle D X Y) (t := arcRectangle used X Y)
    simpa only [hDiff,card_arcRectangle] using h
  have hConsume' : (incidences used X Y:ℝ) ≤ (L:ℝ)*(Y.card:ℝ) := by exact_mod_cast hConsume
  have hKeep' : (incidences D X Y:ℝ) ≤ (incidences (D \ used) X Y:ℝ)+(incidences used X Y:ℝ) :=
    by exact_mod_cast hKeep
  have hX' := mul_le_mul_of_nonneg_left (by exact_mod_cast hx : (a:ℝ) ≤ X.card) hCoeff
  have hX'' := mul_le_mul_of_nonneg_right hX' (Nat.cast_nonneg Y.card : (0:ℝ) ≤ _)
  have hY' := mul_le_mul_of_nonneg_left (by exact_mod_cast hy : (b:ℝ) ≤ Y.card) hSlack
  have h : (q:ℝ) ≤ (incidences (D \ used) X Y:ℝ) := by
    nlinarith only [hNeed,hDx,hConsume',hKeep',hX'',hY']
  exact_mod_cast h

end OverfullWork.DirectedRobustExpansion
