module

public import OverfullWork.OsthusStadenTrimmedCopies

@[expose] public section


/-! Sum the local reserve degrees over the actual incident copies,
using the reduced multidigraph bounds (6) of Osthus–Staden. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion
open scoped Classical
variable {V W I U : Type*} [Fintype V] [Fintype W] [Fintype I]

theorem lift_pair_semidegree (a b : W ↪ V) (D : Digraph W) (s : Bool) (x : W) :
    pairSemidegree s (liftDirectedPair a b D) (if s then a x else b x) =
      pairSemidegree s D x := by
  cases s
  · change ((univ : Finset V).filter (fun v => (liftDirectedPair a b D).Adj v (b x))).card =
      ((univ : Finset W).filter (fun w => D.Adj w x)).card
    have hMap : ((univ : Finset V).filter (fun v => (liftDirectedPair a b D).Adj v (b x))) =
        ((univ : Finset W).filter (fun w => D.Adj w x)).map a := by
      ext v
      simp only [mem_filter,mem_univ,true_and,mem_map]
      constructor
      · rintro ⟨w,y,rfl,hy,h⟩
        obtain rfl := b.injective hy
        exact ⟨w,h,rfl⟩
      · rintro ⟨w,h,rfl⟩
        exact (liftDirectedPair_adj a b D w x).mpr h
    rw [hMap,card_map]
  · change ((univ : Finset V).filter ((liftDirectedPair a b D).Adj (a x))).card =
      ((univ : Finset W).filter (D.Adj x)).card
    have hMap : ((univ : Finset V).filter ((liftDirectedPair a b D).Adj (a x))) =
        ((univ : Finset W).filter (D.Adj x)).map b := by
      ext v
      simp only [mem_filter,mem_univ,true_and,mem_map]
      constructor
      · rintro ⟨y,w,hy,rfl,h⟩
        obtain rfl := a.injective hy
        exact ⟨w,h,rfl⟩
      · rintro ⟨w,h,rfl⟩
        exact (liftDirectedPair_adj a b D x w).mpr h
    rw [hMap,card_map]

variable (source target : I → U)

def copyEndpoint (s : Bool) (i : I) : U := if s then source i else target i

noncomputable def incidentCopySet (s : Bool) (u : U) : Finset I :=
  univ.filter (fun i => copyEndpoint source target s i = u)

/-- Atypical incidences of a vertex at one endpoint of the parallel copies. -/
noncomputable def atypicalIncidentCopies (D : I → Digraph W) (ε d : ℝ)
    (s : Bool) (u : U) (x : W) : Finset I :=
  (incidentCopySet source target s u).filter (fun e =>
    2*ε*(Fintype.card W:ℝ) < |(pairSemidegree s (D e) x:ℝ)-d*(Fintype.card W:ℝ)|)

theorem pair_union_semidegree_at_cluster (a : U → W ↪ V) (D : I → Digraph W)
    (hSeparate : ∀ u v x y, a u x = a v y → u = v)
    (hDis : ∀ i j, i ≠ j → Disjoint (liftDirectedPair (a (source i)) (a (target i)) (D i))
      (liftDirectedPair (a (source j)) (a (target j)) (D j)))
    (s : Bool) (u : U) (x : W) :
    pairSemidegree s (directedPairUnion (a ∘ source) (a ∘ target) D) (a u x) =
      ∑ i ∈ incidentCopySet source target s u, pairSemidegree s (D i) x := by
  let L (i : I) := liftDirectedPair (a (source i)) (a (target i)) (D i)
  have hUn : directedPairUnion (a ∘ source) (a ∘ target) D = indexedArcUnion univ L := by
    ext v w
    simp [directedPairUnion,indexedArcUnion,L]
  have hSum := indexedArcUnion_semidegrees (univ : Finset I) L
    (fun i _ j _ hij => hDis i j hij) (a u x)
  have hEq : pairSemidegree s (indexedArcUnion univ L) (a u x) =
      ∑ i : I, pairSemidegree s (L i) (a u x) := by
    cases s
    · exact hSum.2
    · exact hSum.1
  rw [hUn,hEq,incidentCopySet,sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hi : copyEndpoint source target s i = u
  · rw [if_pos hi,← hi]
    cases s
    · exact lift_pair_semidegree _ _ _ false x
    · exact lift_pair_semidegree _ _ _ true x
  · rw [if_neg hi]
    cases s
    · change ((univ : Finset V).filter (fun v => (L i).Adj v (a u x))).card = 0
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      rintro v _ ⟨y,z,_,hz,_⟩
      exact hi (hSeparate _ _ _ _ hz)
    · change ((univ : Finset V).filter ((L i).Adj (a u x))).card = 0
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      rintro v _ ⟨y,z,hy,_,_⟩
      exact hi (hSeparate _ _ _ _ hy)

/-- Use the lower and upper reduced semidegree bounds, together with
the bound for bad incidences, to obtain the three inputs of the reserve
sum. The coefficient `a` accounts for vertices outside the clusters. -/
theorem h1_budget_from_reduced_counts {α L β γ e d ξ a J good : ℝ}
    (hβ : 0 < β) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hγ : 0 ≤ γ)
    (hLeft : (α-4*d)*L ≤ β*J) (hRight : β*J ≤ (α+2*e)*L)
    (hGood : J-good ≤ ξ*J)
    (hA : α*L ≤ a) (hALarge : 8*a ≤ 9*α*L)
    (hLow : 3*α*L/4 ≤ (1-ξ)*((α-4*d)*L))
    (hHigh : 6*((α+2*e)*L) ≤ 7*α*L)
    (hBad : 4*ξ*((α+2*e)*L) ≤ γ*β*(α*L)) :
    2*a ≤ 3*β*good ∧ 6*β*J ≤ 7*a ∧ 4*(J-good) ≤ γ*a := by
  have hg : (1-ξ)*J ≤ good := by linarith only [hGood]
  have hl := mul_le_mul_of_nonneg_left hLeft (sub_nonneg.mpr hξ1)
  have hgl := mul_le_mul_of_nonneg_left hg hβ.le
  have hbad := mul_le_mul_of_nonneg_left hGood (show 0 ≤ 4*β by positivity)
  have hright := mul_le_mul_of_nonneg_left hRight (show 0 ≤ 4*ξ by positivity)
  have ha := mul_le_mul_of_nonneg_left hA (mul_nonneg hγ hβ.le)
  refine ⟨by nlinarith only [hl,hgl,hLow,hALarge],by linarith only [hRight,hHigh,hA],?_⟩
  apply (mul_le_mul_iff_of_pos_left hβ).mp
  nlinarith only [hbad,hright,ha,hBad]

/-- The actual union of a reserve has the (H1) semidegrees on the
retained clusters. The usual normalization is `a*m = α*n`. -/
theorem h1_profile_of_reserve_copies (a : U → W ↪ V) (D : I → Digraph W)
    (β γ αnorm : ℝ) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (typical : Bool → U → W → Finset I)
    (hSeparate : ∀ u v x y, a u x = a v y → u = v)
    (hDis : ∀ i j, i ≠ j → Disjoint (liftDirectedPair (a (source i)) (a (target i)) (D i))
      (liftDirectedPair (a (source j)) (a (target j)) (D j)))
    (hBudget : ∀ s u x,
      let J := incidentCopySet source target s u
      let K := typical s u x
      K ⊆ J ∧ 2*αnorm ≤ 3*β*(K.card:ℝ) ∧
        6*β*(J.card:ℝ) ≤ 7*αnorm ∧ 4*((J \ K).card:ℝ) ≤ γ*αnorm)
    (hTypical : ∀ s u x i, i ∈ typical s u x →
      γ*β*(Fintype.card W:ℝ)/2 ≤ (pairSemidegree s (D i) x:ℝ) ∧
      (pairSemidegree s (D i) x:ℝ) ≤ 3*γ*β*(Fintype.card W:ℝ)/2) :
    ∀ s u x,
      γ*αnorm*(Fintype.card W:ℝ)/3 ≤
        (pairSemidegree s (directedPairUnion (a ∘ source) (a ∘ target) D) (a u x):ℝ) ∧
      (pairSemidegree s (directedPairUnion (a ∘ source) (a ∘ target) D) (a u x):ℝ)
        ≤ 2*γ*αnorm*(Fintype.card W:ℝ) := by
  intro s u x
  obtain ⟨hSub,hLow,hHigh,hBad⟩ := hBudget s u x
  rw [pair_union_semidegree_at_cluster source target a D hSeparate hDis,Nat.cast_sum]
  apply thin_reserve_profile_sum _ _ _ β γ αnorm (Fintype.card W:ℝ) hSub hβ hγ
    (Nat.cast_nonneg _) hLow hHigh hBad (hTypical s u x)
  intro i _
  have h := card_le_univ ((univ : Finset W).filter (fun y =>
    if s then (D i).Adj x y else (D i).Adj y x))
  cases s
  · exact_mod_cast (show inDegree (D i) x ≤ Fintype.card W from h)
  · exact_mod_cast (show outDegree (D i) x ≤ Fintype.card W from h)

end OverfullWork.DirectedRegularPairs
