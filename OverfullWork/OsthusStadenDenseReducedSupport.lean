module

public import OverfullWork.OsthusStadenReducedBudgets
public import OverfullWork.RobustClusterQuotient
public import OverfullWork.DirectedPairEnergy
public import OverfullWork.DirectedPurePairGraph

@[expose] public section


/-! The dense support of the reduced multidigraph in §5.1.
The density threshold is applied on the same cells as the sparse
quotient. -/
namespace OverfullWork.DirectedClusterQuotient

open Finset DirectedRobustExpansion DirectedRegularPairs DirectedPairEnergy
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

/-- Reduce a physical graph at the larger density threshold. -/
def denseReduced (H : Digraph V) (f : V → Option I) (d : ℝ) : Digraph I :=
  ⟨fun i j => d ≤ density H (cluster f i) (cluster f j)⟩

theorem denseReduced_le_quotient (H : Digraph V) (f : V → Option I) (d : ℝ) (hd : 0 < d) :
    denseReduced H f d ≤ quotient H f := by
  intro i j h
  obtain ⟨u,hu,v,hv,hArc⟩ := arc_of_positive_density H _ _ (hd.trans_le h)
  exact ⟨u,v,(mem_cluster f i u).mp hu,(mem_cluster f j v).mp hv,hArc⟩

private theorem inNeighbours_lift_sum (H : Digraph V) (f : V → Option I)
    (S : Finset I) (v : V) :
    inNeighbours H (lift f S) v = ∑ i ∈ S, inNeighbours H (cluster f i) v := by
  have hDis : (↑S : Set I).PairwiseDisjoint (cluster f) := fun _ _ _ _ hij => clusters_disjoint f hij
  simp only [inNeighbours,lift,filter_biUnion]
  exact card_biUnion (fun i hi j hj hij => (hDis hi hj hij).mono (filter_subset _ _) (filter_subset _ _))

private theorem incidences_lift_left (H : Digraph V) (f : V → Option I)
    (S : Finset I) (B : Finset V) :
    incidences H (lift f S) B = ∑ i ∈ S, incidences H (cluster f i) B := by
  simp only [incidences,inNeighbours_lift_sum]
  exact sum_comm

private theorem inNeighbours_le_after_pure_loss (G H : Digraph V) (hLe : H ≤ G) (S : Finset V) (v : V) :
    inNeighbours G S v ≤ inNeighbours H S v+inDegree (G \ H) v := by
  have hPart := DirectedArcSelection.incidence_partition G H hLe S {v}
  simp only [incidences,sum_singleton] at hPart
  have hLoss : inNeighbours (G \ H) S v ≤ inDegree (G \ H) v :=
    RobustClusterQuotient.inNeighbours_mono _ (subset_univ _) _
  omega

set_option maxHeartbeats 1550000 in
/-- A second density cutoff on the original cells preserves robust
expansion at a smaller radius. Counting physical incoming arcs into
a whole target cell bounds its contribution to the robust
neighbourhood when it has too few dense incoming pairs. -/
theorem real_robust_dense_reduced_of_pure_loss
    (G H : Digraph V) (hLe : H ≤ G) (f : V → Option I) (m : ℕ)
    (hm : 0 < m) (hSize : ∀ i, (cluster f i).card = m) (ν τ μ d : ℝ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hτ : 0 ≤ τ) (hτHalf : 2*τ ≤ 1)
    (hμ : 0 ≤ μ) (hμν : μ ≤ ν/2) (hd : 0 ≤ d) (hMargin : 8*(μ+d) ≤ ν^2)
    (hN : 0 < Fintype.card V)
    (hRob : IsRealRobust G ν τ)
    (hExc : ((exceptional f).card:ℝ) ≤ (ν/4)*(Fintype.card V:ℝ))
    (hLoss : ∀ v, f v ≠ none → (inDegree (G \ H) v:ℝ) ≤ (ν/2)*(Fintype.card V:ℝ)) :
    IsRealRobust (denseReduced H f d) μ (2*τ) := by
  let N := (Fintype.card V:ℝ)
  let K := (Fintype.card I:ℝ)
  have hNR : 0 < N := by dsimp only [N]; exact_mod_cast hN
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hOrder : N = ((exceptional f).card:ℝ)+(m:ℝ)*K := by
    dsimp only [N,K]
    exact_mod_cast order_eq f m hSize
  have hOrd : (m:ℝ)*K ≤ N := by linarith only [hOrder,Nat.cast_nonneg (α := ℝ) (exceptional f).card]
  have hHalf : N ≤ 2*((m:ℝ)*K) := by
    have h := mul_le_mul_of_nonneg_right hν₁ hNR.le
    linarith only [h,hExc,hOrder]
  intro S hLow hHigh
  let U := lift f S
  let E := exceptional f
  let W := realNeighbourhood G ν U
  let R := denseReduced H f d
  let W' := realNeighbourhood R μ S
  have hU : (U.card:ℝ) = (m:ℝ)*(S.card:ℝ) := by exact_mod_cast lift_card f m hSize S
  have hLower : τ*N ≤ (U.card:ℝ) := by
    have ha := mul_le_mul_of_nonneg_left hLow hmR.le
    have hb := mul_le_mul_of_nonneg_left hHalf hτ
    linarith only [hU,ha,hb]
  have hUpper : (U.card:ℝ) ≤ (1-τ)*N := by
    have ha := mul_le_mul_of_nonneg_left hHigh hmR.le
    have hb := mul_le_mul_of_nonneg_left hOrd (sub_nonneg.mpr hτHalf)
    have hc := mul_le_mul_of_nonneg_right (show 1-2*τ ≤ 1-τ by linarith only [hτ]) hNR.le
    linarith only [hU,ha,hb,hc]
  have hW : (U.card:ℝ)+ν*N ≤ (W.card:ℝ) := hRob U hLower hUpper
  have hPhysical (j : I) (v : V) (hv : v ∈ W ∩ cluster f j) :
      (ν/2)*N ≤ (inNeighbours H U v:ℝ) := by
    have hRaw : ν*N ≤ (inNeighbours G U v:ℝ) := (mem_filter.mp (mem_inter.mp hv).1).2
    have hf : f v ≠ none := by rw [(mem_cluster f j v).mp (mem_inter.mp hv).2]; simp
    have hDrop := hLoss v hf
    have hArc : (inNeighbours G U v:ℝ) ≤ (inNeighbours H U v:ℝ)+inDegree (G \ H) v := by
      exact_mod_cast inNeighbours_le_after_pure_loss G H hLe U v
    linarith only [hRaw,hDrop,hArc]
  have hFew (j : I) (hj : j ∉ W') : ((W ∩ cluster f j).card:ℝ) ≤ (ν/4)*(m:ℝ) := by
    let B := S.filter (fun i => R.Adj i j)
    have hB : (B.card:ℝ) ≤ μ*K := by
      have h : ¬ μ*K ≤ (B.card:ℝ) := fun h => hj (mem_filter.mpr ⟨mem_univ _,h⟩)
      exact (lt_of_not_ge h).le
    have hPair (i : I) (hi : i ∈ S) :
        (incidences H (cluster f i) (cluster f j):ℝ) ≤
          (if i ∈ B then (1:ℝ) else 0)*((m:ℝ)^2)+d*((m:ℝ)^2) := by
      have hh := density_mass H (cluster f i) (cluster f j)
      simp only [mass,hSize,←pow_two] at hh
      rw [←hh]
      by_cases hb : i ∈ B
      · simpa only [if_pos hb,one_mul,mul_one] using
          (mul_le_mul_of_nonneg_left (density_le_one H (cluster f i) (cluster f j))
            (sq_nonneg (m:ℝ))).trans (le_add_of_nonneg_right (mul_nonneg hd (sq_nonneg (m:ℝ))))
      · have hD : density H (cluster f i) (cluster f j) ≤ d :=
          (lt_of_not_ge (fun h => hb (mem_filter.mpr ⟨hi,h⟩))).le
        simp only [if_neg hb,zero_mul,zero_add]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hD (sq_nonneg (m:ℝ))
    have hSum := sum_le_sum (s := S) hPair
    have hInd : (∑ i ∈ S, if i ∈ B then (1:ℝ) else 0) = B.card := by
      rw [←sum_filter]
      have hEq : S.filter (· ∈ B) = B := by
        ext i
        simp only [mem_filter,B,←and_assoc,and_self]
      rw [hEq,sum_const,nsmul_eq_mul,mul_one]
    simp only [sum_add_distrib,←sum_mul,sum_const,nsmul_eq_mul,hInd,←Nat.cast_sum,
      ←incidences_lift_left] at hSum
    have hSc : (S.card:ℝ) ≤ K := by dsimp only [K]; exact_mod_cast card_le_univ S
    have hTotal : (incidences H U (cluster f j):ℝ) ≤ (μ+d)*(m:ℝ)*N := by
      have h := mul_le_mul_of_nonneg_right hB (sq_nonneg (m:ℝ))
      have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSc hd) (sq_nonneg (m:ℝ))
      have h'' := mul_le_mul_of_nonneg_left hOrd (show 0 ≤ (μ+d)*(m:ℝ) by positivity)
      linarith only [hSum,h,h',h'']
    have hLow := sum_le_sum (s := W ∩ cluster f j) (hPhysical j)
    have hBound : (incidences H U (W ∩ cluster f j):ℝ) ≤ (incidences H U (cluster f j):ℝ) := by
      exact_mod_cast (sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => Nat.zero_le _) :
        incidences H U (W ∩ cluster f j) ≤ incidences H U (cluster f j))
    simp only [sum_const,nsmul_eq_mul,←Nat.cast_sum] at hLow
    change ((W ∩ cluster f j).card:ℝ)*((ν/2)*N) ≤ (incidences H U (W ∩ cluster f j):ℝ) at hLow
    have hCost := mul_le_mul_of_nonneg_right hMargin (mul_nonneg hmR.le hNR.le)
    have hResult : ((W ∩ cluster f j).card:ℝ)*((ν/2)*N) ≤ ((ν/4)*(m:ℝ))*((ν/2)*N) := by
      nlinarith only [hLow,hBound,hTotal,hCost]
    exact (mul_le_mul_iff_of_pos_right (by positivity : 0 < (ν/2)*N)).mp hResult
  have hAll (j : I) :
      ((W ∩ cluster f j).card:ℝ) ≤ (if j ∈ W' then (m:ℝ) else 0)+(ν/4)*(m:ℝ) := by
    by_cases hj : j ∈ W'
    · have h : (W ∩ cluster f j).card ≤ m := (card_le_card inter_subset_right).trans_eq (hSize j)
      simpa only [if_pos hj] using (by exact_mod_cast h : ((W ∩ cluster f j).card:ℝ) ≤ m).trans
        (le_add_of_nonneg_right (by positivity))
    · simpa only [if_neg hj,zero_add] using hFew j hj
  have hParts : ((W ∩ E).card+∑ j, (W ∩ cluster f j).card) = W.card := by
    have hEq : (W ∩ E) ∪ univ.biUnion (fun j => W ∩ cluster f j) = W := by
      ext v
      simp only [mem_union,mem_inter,mem_biUnion,mem_univ,true_and]
      constructor
      · rintro (⟨hv,_⟩ | ⟨j,hv,_⟩) <;> exact hv
      · intro hv
        cases he : f v with
        | none => exact Or.inl ⟨hv,(mem_exceptional f v).mpr he⟩
        | some j => exact Or.inr ⟨j,hv,(mem_cluster f j v).mpr he⟩
    have hApart : Disjoint (W ∩ E) (univ.biUnion (fun j => W ∩ cluster f j)) := by
      refine disjoint_left.mpr (fun v hv hv' => ?_)
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp hv'
      have hE := (mem_exceptional f v).mp (mem_inter.mp hv).2
      have hJ := (mem_cluster f j v).mp (mem_inter.mp hj).2
      rw [hE] at hJ
      cases hJ
    have hCount := card_biUnion (s := (univ : Finset I)) (t := fun j => W ∩ cluster f j)
      (fun i _ j _ hij => (clusters_disjoint f hij).mono inter_subset_right inter_subset_right)
    calc
      (W ∩ E).card+∑ j, (W ∩ cluster f j).card = ((W ∩ E) ∪ univ.biUnion (fun j => W ∩ cluster f j)).card := by
        rw [card_union_of_disjoint hApart,hCount]
      _ = W.card := congrArg card hEq
  have hSum := sum_le_sum (s := (univ : Finset I)) (fun j _ => hAll j)
  have hInd : (∑ j : I, if j ∈ W' then (m:ℝ) else 0) = (W'.card:ℝ)*(m:ℝ) := by
    rw [←sum_filter,filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul]
  simp only [sum_add_distrib,hInd,sum_const,card_univ,nsmul_eq_mul,←Nat.cast_sum] at hSum
  have hOther : ((W ∩ E).card:ℝ) ≤ (ν/4)*N :=
    (by exact_mod_cast card_le_card (show W ∩ E ⊆ E from inter_subset_right) :
      ((W ∩ E).card:ℝ) ≤ E.card).trans hExc
  have hParts' : ((W ∩ E).card:ℝ)+(↑(∑ j, (W ∩ cluster f j).card):ℝ) = W.card := by exact_mod_cast hParts
  have hExtra := mul_le_mul_of_nonneg_left hOrd (by positivity : 0 ≤ ν/4)
  have hM := mul_le_mul_of_nonneg_right hμν (mul_nonneg hmR.le hK)
  have hExtra' := mul_le_mul_of_nonneg_left hOrd (by positivity : 0 ≤ ν/2)
  have hResult : ((S.card:ℝ)+μ*K)*(m:ℝ) ≤ (W'.card:ℝ)*(m:ℝ) := by
    linarith only [hU,hW,hParts',hOther,hSum,hExtra,hM,hExtra']
  exact (mul_le_mul_iff_of_pos_right hmR).mp hResult

end OverfullWork.DirectedClusterQuotient
