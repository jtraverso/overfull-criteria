module

public import OverfullWork.DirectedPurePairGraph
public import OverfullWork.DirectedPairEnergy
public import OverfullWork.KuhnOsthusCodegreeCount
public import OverfullWork.PureGraphDeletionBudget

@[expose] public section


/-! Separate low-density deletions with bounded degrees from the
small total loss used to measure the exceptional set. -/
namespace OverfullWork.DirectedClusterQuotient

open Finset DirectedRobustExpansion DirectedRegularPairs DirectedPairEnergy
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

private theorem few_high_out_profiles (G : Digraph V) (A B : Finset V) (ε d : ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hReg : IsUniform G ε A B) (hLow : density G A B < d) :
    ((A.filter (fun x => (d+ε)*(B.card:ℝ) < (outTo G B x:ℝ))).card:ℝ) ≤ ε*(A.card:ℝ) := by
  let S := A.filter (fun x => (d+ε)*(B.card:ℝ) < (outTo G B x:ℝ))
  change (S.card:ℝ) ≤ ε*(A.card:ℝ)
  by_contra! hS
  have hSB : 0 < (S.card:ℝ)*(B.card:ℝ) := by
    have hAR : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hBR : (0:ℝ) < B.card := by exact_mod_cast hB.card_pos
    exact mul_pos ((mul_pos hε hAR).trans hS) hBR
  have hDensity := (abs_lt.mp (hReg S (filter_subset _ _) B Subset.rfl (by linarith only [hS])
    (mul_le_of_le_one_right (Nat.cast_nonneg _) hε₁))).2
  have hUp : (incidences G S B:ℝ) < (d+ε)*((S.card:ℝ)*(B.card:ℝ)) := by
    apply (div_lt_iff₀ hSB).mp
    change density G S B < d+ε
    linarith only [hDensity,hLow]
  rw [incidences_eq_sum_outTo] at hUp
  have hLo := sum_le_sum (s := S) (fun x hx => (mem_filter.mp hx).2.le)
  simp only [sum_const,nsmul_eq_mul] at hLo
  linarith only [hUp,hLo]

theorem few_high_low_density_pair_profiles (G : Digraph V) (A B : Finset V) (ε d : ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hReg : IsUniform G ε A B) (hLow : density G A B < d) :
    ((A.filter (fun x => (d+ε)*(B.card:ℝ) < (outTo G B x:ℝ))).card:ℝ) ≤ ε*(A.card:ℝ) ∧
    ((B.filter (fun y => (d+ε)*(A.card:ℝ) < (inNeighbours G A y:ℝ))).card:ℝ) ≤ ε*(B.card:ℝ) := by
  have hRev (S T : Finset V) : density (reverseArcs G) T S = density G S T := by
    unfold density
    rw [incidences_reverseArcs,mul_comm (T.card:ℝ)]
  have hReg' : IsUniform (reverseArcs G) ε B A := by
    intro T hT S hS hTL hSL
    rw [hRev,hRev]
    exact hReg S hS T hT hSL hTL
  refine ⟨few_high_out_profiles G A B ε d hA hB hε hε₁ hReg hLow,?_⟩
  have hEq : B.filter (fun y => (d+ε)*(A.card:ℝ) < (inNeighbours G A y:ℝ)) =
      B.filter (fun y => (d+ε)*(A.card:ℝ) < (outTo (reverseArcs G) A y:ℝ)) := by
    ext y
    simp only [mem_filter]
    rw [reverseArcs_outTo]
  rw [hEq]
  exact few_high_out_profiles (reverseArcs G) B A ε d hB hA hε hε₁ hReg' (by rwa [hRev])

/-- Remove the typical arcs of the low-density regular pairs.
Each such arc has both endpoint degrees below the pair caps. -/
def typicalLowArcs (G : Digraph V) (label : V → Option I) (ε d : ℝ) : Digraph V where
  Adj x y := G.Adj x y ∧ ∃ i j, label x = some i ∧ label y = some j ∧
    i ≠ j ∧ IsUniform G ε (cluster label i) (cluster label j) ∧
    density G (cluster label i) (cluster label j) < d ∧
    (outTo G (cluster label j) x:ℝ) ≤ (d+ε)*((cluster label j).card:ℝ) ∧
    (inNeighbours G (cluster label i) y:ℝ) ≤ (d+ε)*((cluster label i).card:ℝ)

omit [Fintype I] in
theorem typicalLowArcs_le (G : Digraph V) (label : V → Option I) (ε d : ℝ) :
    typicalLowArcs G label ε d ≤ G := fun _ _ h => h.1

omit [Fintype I] in
theorem regularPure_le_after_typicalLowArcs (G : Digraph V) (label : V → Option I) (ε d : ℝ) :
    restrictPairs G label (regularReduced G label ε d) ≤ G \ typicalLowArcs G label ε d := by
  rintro x y ⟨hG,i,j,hx,hy,hDense⟩
  refine ⟨hG,?_⟩
  rintro ⟨_,a,b,ha,hb,_,_,hLow,_,_⟩
  have ea : a = i := Option.some.inj (ha.symm.trans hx)
  have eb : b = j := Option.some.inj (hb.symm.trans hy)
  subst a
  subst b
  exact (not_lt_of_ge hDense.2.2) hLow

set_option maxHeartbeats 850000 in
/-- Low-density deletion costs at most (d+ε)n at each vertex in
each direction. It does not use the exceptional-set budget. -/
theorem typicalLowArcs_semidegrees (G : Digraph V) (label : V → Option I) (ε d : ℝ)
    (hn : 0 ≤ d+ε) :
    ∀ v, (inDegree (typicalLowArcs G label ε d) v:ℝ) ≤ (d+ε)*(Fintype.card V:ℝ) ∧
      (outDegree (typicalLowArcs G label ε d) v:ℝ) ≤ (d+ε)*(Fintype.card V:ℝ) := by
  let H := typicalLowArcs G label ε d
  have hIn (j : I) (v : V) :
      (((cluster label j).filter (fun x => H.Adj x v)).card:ℝ) ≤ (d+ε)*((cluster label j).card:ℝ) := by
    by_cases h : ((cluster label j).filter (fun x => H.Adj x v)).Nonempty
    · obtain ⟨x,hx⟩ := h
      obtain ⟨hx,hArc⟩ := mem_filter.mp hx
      obtain ⟨_,i,k,hi,_,_,_,_,_,hDegree⟩ := hArc
      have e : i = j := Option.some.inj (hi.symm.trans ((mem_cluster label j x).mp hx))
      subst i
      apply le_trans _ hDegree
      unfold inNeighbours
      have hSub : ((cluster label j).filter (fun x => H.Adj x v)) ⊆
          ((cluster label j).filter (fun x => G.Adj x v)) := by
        intro z hz
        simp only [mem_filter] at hz ⊢
        exact ⟨hz.1,hz.2.1⟩
      exact_mod_cast card_le_card hSub
    · rw [not_nonempty_iff_eq_empty.mp h,card_empty,Nat.cast_zero]
      exact mul_nonneg hn (Nat.cast_nonneg _)
  have hOut (j : I) (v : V) :
      (((cluster label j).filter (fun x => H.Adj v x)).card:ℝ) ≤ (d+ε)*((cluster label j).card:ℝ) := by
    by_cases h : ((cluster label j).filter (fun x => H.Adj v x)).Nonempty
    · obtain ⟨x,hx⟩ := h
      obtain ⟨hx,hArc⟩ := mem_filter.mp hx
      obtain ⟨_,i,k,_,hk,_,_,_,hDegree,_⟩ := hArc
      have e : k = j := Option.some.inj (hk.symm.trans ((mem_cluster label j x).mp hx))
      subst k
      apply le_trans _ hDegree
      unfold outTo
      have hSub : ((cluster label j).filter (fun x => H.Adj v x)) ⊆
          ((cluster label j).filter (fun x => G.Adj v x)) := by
        intro z hz
        simp only [mem_filter] at hz ⊢
        exact ⟨hz.1,hz.2.1⟩
      exact_mod_cast card_le_card hSub
    · rw [not_nonempty_iff_eq_empty.mp h,card_empty,Nat.cast_zero]
      exact mul_nonneg hn (Nat.cast_nonneg _)
  have hCount (p : V → Prop) (hCover : ∀ x, p x → ∃ i, label x = some i)
      (hBound : ∀ i, (((cluster label i).filter p).card:ℝ) ≤ (d+ε)*((cluster label i).card:ℝ)) :
      (((univ : Finset V).filter p).card:ℝ) ≤ (d+ε)*(Fintype.card V:ℝ) := by
    let C (i : I) := (cluster label i).filter p
    have hUnion : (univ : Finset V).filter p ⊆ (univ : Finset I).biUnion C := by
      intro x hx
      obtain ⟨i,hi⟩ := hCover x (mem_filter.mp hx).2
      exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨(mem_cluster label i x).mpr hi,(mem_filter.mp hx).2⟩⟩
    have hSize : (∑ i : I, ((cluster label i).card:ℝ)) ≤ Fintype.card V := by
      rw [←Nat.cast_sum,←card_biUnion (fun i _ j _ h => clusters_disjoint label h)]
      exact_mod_cast card_le_univ _
    calc
      _ ≤ ∑ i : I,((C i).card:ℝ) := by exact_mod_cast (card_le_card hUnion).trans card_biUnion_le
      _ ≤ ∑ i : I,(d+ε)*((cluster label i).card:ℝ) := sum_le_sum (fun i _ => hBound i)
      _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left hSize hn
  intro v
  constructor
  · apply hCount (fun x => H.Adj x v) _ (fun j => hIn j v)
    rintro x ⟨_,i,_,hi,_⟩
    exact ⟨i,hi⟩
  · apply hCount (fun x => H.Adj v x) _ (fun j => hOut j v)
    rintro x ⟨_,_,j,_,hj,_⟩
    exact ⟨j,hj⟩

set_option maxHeartbeats 850000 in
/-- The untreated arcs of a low regular pair must meet an atypical
endpoint. Their total cost has coefficient 2ε, independent of the
density floor. -/
theorem typicalLowArcs_remaining_pair (G : Digraph V) (label : V → Option I) (ε d : ℝ)
    (i j : I) (hij : i ≠ j) (hA : (cluster label i).Nonempty) (hB : (cluster label j).Nonempty)
    (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hReg : IsUniform G ε (cluster label i) (cluster label j))
    (hLow : density G (cluster label i) (cluster label j) < d) :
    (incidences (G \ typicalLowArcs G label ε d) (cluster label i) (cluster label j):ℝ) ≤
      2*ε*mass (cluster label i) (cluster label j) := by
  let A := cluster label i
  let B := cluster label j
  let D := G \ typicalLowArcs G label ε d
  let X := A.filter (fun x => (d+ε)*(B.card:ℝ) < (outTo G B x:ℝ))
  let Y := B.filter (fun y => (d+ε)*(A.card:ℝ) < (inNeighbours G A y:ℝ))
  obtain ⟨hX,hY⟩ := few_high_low_density_pair_profiles G A B ε d hA hB hε hε₁ hReg hLow
  have hBad (x y : V) (hx : x ∈ A) (hy : y ∈ B) (h : D.Adj x y) : x ∈ X ∨ y ∈ Y := by
    by_contra! hh
    have h₁ : (outTo G B x:ℝ) ≤ (d+ε)*(B.card:ℝ) := le_of_not_gt (fun ht =>
      hh.1 (mem_filter.mpr ⟨hx,ht⟩))
    have h₂ : (inNeighbours G A y:ℝ) ≤ (d+ε)*(A.card:ℝ) := le_of_not_gt (fun ht =>
      hh.2 (mem_filter.mpr ⟨hy,ht⟩))
    exact h.2 ⟨h.1,i,j,(mem_cluster label i x).mp hx,(mem_cluster label j y).mp hy,hij,hReg,hLow,h₁,h₂⟩
  have hBound : (arcCell D A B).card ≤ X.card*B.card+A.card*Y.card := by
    have hCover : arcCell D A B ⊆ (X ×ˢ B) ∪ (A ×ˢ Y) := by
      rintro ⟨x,y⟩ h
      simp only [arcCell,mem_filter,mem_product] at h
      obtain ⟨⟨hx,hy⟩,harc⟩ := h
      rcases hBad x y hx hy harc with hX | hY
      · exact mem_union_left _ (mem_product.mpr ⟨hX,hy⟩)
      · exact mem_union_right _ (mem_product.mpr ⟨hx,hY⟩)
    exact (card_le_card hCover).trans (by simpa only [card_product] using card_union_le (X ×ˢ B) (A ×ˢ Y))
  rw [arcCell_card] at hBound
  have hBound' : (incidences D A B:ℝ) ≤ (X.card:ℝ)*(B.card:ℝ)+(A.card:ℝ)*(Y.card:ℝ) := by
    exact_mod_cast hBound
  change (incidences D A B:ℝ) ≤ 2*ε*mass A B
  unfold mass
  linarith only [hBound',mul_le_mul_of_nonneg_right hX (Nat.cast_nonneg B.card),
    mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg A.card)]

end OverfullWork.DirectedClusterQuotient
