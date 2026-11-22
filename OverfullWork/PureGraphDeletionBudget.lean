module

public import OverfullWork.DirectedPurePairGraph
public import OverfullWork.DirectedDegreeTrimming

@[expose] public section


/-! Global deleted-arc accounting for the actual pair-restricted graph.
Exceptional endpoints and rejected cluster pairs cover every deletion. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRobustExpansion DirectedRegularPairs DirectedDegreeTrimming
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

noncomputable def arcCell (D : Digraph V) (A B : Finset V) : Finset (V × V) :=
  (A ×ˢ B).filter fun e => D.Adj e.1 e.2

theorem arcCell_card (D : Digraph V) (A B : Finset V) : (arcCell D A B).card=incidences D A B := by
  simp only [arcCell,card_filter,sum_product,incidences,inNeighbours]
  rw [sum_comm]

theorem arcCell_univ_card (D : Digraph V) : (arcCell D univ univ).card=total D := by
  rw [arcCell_card]
  rfl

noncomputable def rejectedCell (D : Digraph V) (f : V → Option I) (R : Digraph I)
    (ij : I × I) : Finset (V × V) :=
  if R.Adj ij.1 ij.2 then ∅ else arcCell D (cluster f ij.1) (cluster f ij.2)

theorem deleted_arcs_cover (D : Digraph V) (f : V → Option I) (R : Digraph I) :
    arcCell (D\restrictPairs D f R) univ univ ⊆
      ((exceptional f ×ˢ univ) ∪ (univ ×ˢ exceptional f)) ∪
        univ.biUnion (rejectedCell D f R) := by
  letI : DecidableRel (D\restrictPairs D f R).Adj := fun _ _ => Classical.propDecidable _
  intro e he
  obtain ⟨_,hD,hNot⟩ := mem_filter.mp he
  rcases e with ⟨u,v⟩
  cases hu : f u with
  | none =>
    exact mem_union_left _ (mem_union_left _ (mem_product.mpr ⟨(mem_exceptional f u).mpr hu,mem_univ _⟩))
  | some i =>
    cases hv : f v with
    | none =>
      exact mem_union_left _ (mem_union_right _ (mem_product.mpr ⟨mem_univ _,(mem_exceptional f v).mpr hv⟩))
    | some j =>
      have hR : ¬R.Adj i j := fun hh => hNot ⟨hD,i,j,hu,hv,hh⟩
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨(i,j),mem_univ _,?_⟩
      simp only [rejectedCell,if_neg hR]
      exact mem_filter.mpr ⟨mem_product.mpr ⟨(mem_cluster f i u).mpr hu,(mem_cluster f j v).mpr hv⟩,hD⟩

theorem total_deleted_le_rejected_pairs (D : Digraph V) (f : V → Option I) (R : Digraph I) :
    total (D\restrictPairs D f R) ≤ 2*(exceptional f).card*Fintype.card V+
      ∑ ij : I × I,if R.Adj ij.1 ij.2 then 0 else incidences D (cluster f ij.1) (cluster f ij.2) := by
  have hSub := card_le_card (deleted_arcs_cover D f R)
  have hUnion := card_union_le ((exceptional f ×ˢ univ) ∪ (univ ×ˢ exceptional f))
    (univ.biUnion (rejectedCell D f R))
  have hExc := card_union_le (exceptional f ×ˢ univ) (univ ×ˢ exceptional f)
  have hCells := card_biUnion_le (s:=univ) (t:=rejectedCell D f R)
  rw [arcCell_univ_card] at hSub
  simp only [card_product,card_univ] at hExc
  have hSum : (∑ ij : I × I,(rejectedCell D f R ij).card)=
      ∑ ij : I × I,if R.Adj ij.1 ij.2 then 0 else incidences D (cluster f ij.1) (cluster f ij.2) := by
    apply sum_congr rfl
    intro ij _
    by_cases hh : R.Adj ij.1 ij.2 <;> simp only [rejectedCell,hh,if_true,if_false,card_empty,arcCell_card]
  rw [hSum] at hCells
  nlinarith only [hSub,hUnion,hExc,hCells]

theorem incidences_le_density_cap (D : Digraph V) (A B : Finset V) (d : ℝ)
    (hDensity : density D A B ≤ d) :
    (incidences D A B:ℝ) ≤ d*(A.card:ℝ)*(B.card:ℝ) := by
  by_cases ha : A.card=0
  · have hA : A=∅ := card_eq_zero.mp ha
    simp [hA,incidences,inNeighbours]
  by_cases hb : B.card=0
  · have hB : B=∅ := card_eq_zero.mp hb
    simp [hB,incidences]
  have hPos : (0:ℝ) < (A.card:ℝ)*(B.card:ℝ) := by
    have hA : (0:ℝ) < A.card := by exact_mod_cast Nat.pos_of_ne_zero ha
    have hB : (0:ℝ) < B.card := by exact_mod_cast Nat.pos_of_ne_zero hb
    positivity
  have hh := (div_le_iff₀ hPos).mp hDensity
  nlinarith only [hh]

theorem total_deleted_density_budget (D : Digraph V) (f : V → Option I) (R : Digraph I)
    (J : Finset (I × I)) (M : ℕ) (d : ℝ) (hd : 0 ≤ d)
    (hSize : ∀ i,(cluster f i).card ≤ M)
    (hSparse : ∀ ij,ij ∉ J → ¬R.Adj ij.1 ij.2 →
      density D (cluster f ij.1) (cluster f ij.2) ≤ d) :
    (total (D\restrictPairs D f R):ℝ) ≤
      2*((exceptional f).card:ℝ)*(Fintype.card V:ℝ)+
      (J.card:ℝ)*(M:ℝ)^2+d*(M:ℝ)^2*(Fintype.card I:ℝ)^2 := by
  have hPoint : ∀ ij : I × I,
      (if R.Adj ij.1 ij.2 then (0:ℝ) else (incidences D (cluster f ij.1) (cluster f ij.2):ℝ)) ≤
      (if ij ∈ J then (M:ℝ)^2 else 0)+d*(M:ℝ)^2 := by
    intro ij
    have hCapN := (DirectedArcSelection.incidences_le D (cluster f ij.1) (cluster f ij.2)).trans
      (Nat.mul_le_mul (hSize ij.1) (hSize ij.2))
    have hCap : (incidences D (cluster f ij.1) (cluster f ij.2):ℝ) ≤ (M:ℝ)^2 := by
      exact_mod_cast (by simpa only [pow_two] using hCapN : incidences D (cluster f ij.1) (cluster f ij.2) ≤ M^2)
    by_cases hr : R.Adj ij.1 ij.2
    · simp only [if_pos hr];positivity
    by_cases hj : ij ∈ J
    · simp only [if_neg hr,if_pos hj]
      exact hCap.trans (le_add_of_nonneg_right (by positivity))
    · simp only [if_neg hr,if_neg hj,zero_add]
      have hDensity := incidences_le_density_cap D _ _ d (hSparse ij hj hr)
      have hProd : ((cluster f ij.1).card:ℝ)*((cluster f ij.2).card:ℝ) ≤ (M:ℝ)^2 := by
        exact_mod_cast (by simpa only [pow_two] using Nat.mul_le_mul (hSize ij.1) (hSize ij.2) :
          (cluster f ij.1).card*(cluster f ij.2).card ≤ M^2)
      have hh := mul_le_mul_of_nonneg_left hProd hd
      nlinarith only [hDensity,hh]
  have hSum := sum_le_sum (s:=univ) (fun ij _ => hPoint ij)
  have hIndicator : (∑ ij : I × I,if ij ∈ J then (M:ℝ)^2 else 0)=(J.card:ℝ)*(M:ℝ)^2 := by
    rw [←sum_filter]
    simp
  rw [sum_add_distrib,hIndicator] at hSum
  simp only [sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul] at hSum
  have hTotal : (total (D\restrictPairs D f R):ℝ) ≤
      2*((exceptional f).card:ℝ)*(Fintype.card V:ℝ)+
      ∑ ij : I × I,if R.Adj ij.1 ij.2 then (0:ℝ) else (incidences D (cluster f ij.1) (cluster f ij.2):ℝ) := by
    exact_mod_cast total_deleted_le_rejected_pairs D f R
  nlinarith only [hSum,hTotal]

noncomputable def defectivePairs (D : Digraph V) (f : V → Option I) (ε : ℝ) : Finset (I × I) :=
  univ.filter fun ij => ij.1=ij.2 ∨ ¬IsUniform D ε (cluster f ij.1) (cluster f ij.2)

theorem regular_pure_deletion_budget (D : Digraph V) (f : V → Option I) (ε d : ℝ)
    (M : ℕ) (hd : 0 ≤ d) (hSize : ∀ i,(cluster f i).card ≤ M) :
    (total (D\restrictPairs D f (regularReduced D f ε d)):ℝ) ≤
      2*((exceptional f).card:ℝ)*(Fintype.card V:ℝ)+
      ((defectivePairs D f ε).card:ℝ)*(M:ℝ)^2+d*(M:ℝ)^2*(Fintype.card I:ℝ)^2 := by
  apply total_deleted_density_budget D f _ (defectivePairs D f ε) M d hd hSize
  intro ij hGood hNot
  have hDef : ¬(ij.1=ij.2 ∨ ¬IsUniform D ε (cluster f ij.1) (cluster f ij.2)) :=
    fun hh => hGood (mem_filter.mpr ⟨mem_univ _,hh⟩)
  have hNe : ij.1 ≠ ij.2 := fun hh => hDef (Or.inl hh)
  have hUniform : IsUniform D ε (cluster f ij.1) (cluster f ij.2) := by
    by_contra hh;exact hDef (Or.inr hh)
  by_contra hDense
  exact hNot ⟨hNe,hUniform,(lt_of_not_ge hDense).le⟩

theorem regular_pure_bad_vertex_budget (D : Digraph V) (f : V → Option I) (ε d : ℝ)
    (M L : ℕ) (hd : 0 ≤ d) (hSize : ∀ i,(cluster f i).card ≤ M) :
    ((bad (D\restrictPairs D f (regularReduced D f ε d)) L).card:ℝ)*((L:ℝ)+1) ≤
      2*(2*((exceptional f).card:ℝ)*(Fintype.card V:ℝ)+
      ((defectivePairs D f ε).card:ℝ)*(M:ℝ)^2+d*(M:ℝ)^2*(Fintype.card I:ℝ)^2) := by
  have hLoss := regular_pure_deletion_budget D f ε d M hd hSize
  have hBad : ((bad (D\restrictPairs D f (regularReduced D f ε d)) L).card:ℝ)*((L:ℝ)+1) ≤
      2*(total (D\restrictPairs D f (regularReduced D f ε d)):ℝ) := by
    exact_mod_cast bad_budget (D\restrictPairs D f (regularReduced D f ε d)) L
  linarith only [hLoss,hBad]

end OverfullWork.DirectedClusterQuotient
