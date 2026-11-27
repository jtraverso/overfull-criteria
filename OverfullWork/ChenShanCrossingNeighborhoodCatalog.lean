module

public import OverfullWork.ChenShanCrossingNeighborhoodCounts
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

theorem inner_prefixPart_card_le (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (hi : i+1 ≤ l) (hρ : ρ ≤ 1)
    (hn : 2 ≤ (nestedCoreSize ρ m i : ℝ)) (hk : (k:ℝ)/m ≤ 3/2)
    (c : Fin 3) :
    (prefixPartVertices S (i+1) c).card ≤ 2*nestedCoreSize ρ m i := by
  have hL := crossingPart_card_le S i hi hρ hn hk 0
  have hR := crossingPart_card_le S i hi hρ hn hk 4
  have hW := crossingPart_card_le S i hi hρ hn hk 2
  change (Fintype.card ↥(S.left (i+1)) : ℝ) ≤ _ at hL
  change (Fintype.card ↥(S.right (i+1)) : ℝ) ≤ _ at hR
  change (Fintype.card ↥(S.colors (i+1)) : ℝ) ≤ _ at hW
  simp only [Fintype.card_coe] at hL hR hW
  fin_cases c
  · have h := card_prefixPart_filter_left S (i+1) (fun _ => True) (fun _ => True) (by simp)
    simp only [filter_true] at h
    change (prefixPartVertices S (i+1) 0).card ≤ _
    rw [h]
    exact_mod_cast hL
  · have h := card_prefixPart_filter_right S (i+1) (fun _ => True) (fun _ => True) (by simp)
    simp only [filter_true] at h
    change (prefixPartVertices S (i+1) 1).card ≤ _
    rw [h]
    exact_mod_cast hR
  · have h := card_prefixPart_filter_color S (i+1) (fun _ => True) (fun _ => True) (by simp)
    simp only [filter_true] at h
    change (prefixPartVertices S (i+1) 2).card ≤ _
    rw [h]
    exact_mod_cast hW

/-- The protected set is empty when there is no later stage. -/
noncomputable def protectedCrossingPart (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (c : Fin 3) : Finset (TripartiteVertex A B W) :=
  if i+2 ≤ l then prefixPartVertices S (i+2) c else ∅

theorem protectedCrossingPart_subset (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (c : Fin 3) :
    protectedCrossingPart S i c ⊆ prefixPartVertices S (i+1) c := by
  unfold protectedCrossingPart
  split
  · exact prefixPartVertices_antitone S c (by omega)
  · exact empty_subset _

def crossingNeighborhoodTestVertex (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) : CrossingNeighborhoodTests S i → ↥(S.vertices i \ S.vertices (i+1))
  | .inl (x,_) => x
  | .inr (.inl (_,x,_)) => x
  | .inr (.inr (x,_)) => x

noncomputable def crossingNeighborhoodTestTarget (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) : CrossingNeighborhoodTests S i → Finset (TripartiteVertex A B W)
  | .inl (_,c) => prefixPartVertices S (i+1) c
  | .inr (.inl (_,x,y)) =>
    prefixPartVertices S (i+1) (remainingCrossingPart (crossingPartTag x.val) (crossingPartTag y.val))
  | .inr (.inr (_,c)) => protectedCrossingPart S i c

def crossingNeighborhoodTestFilter (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop) :
    CrossingNeighborhoodTests S i → TripartiteVertex A B W → Prop
  | .inr (.inl (true,_,y)) => tripartiteAdjacent F P Q y.val
  | _ => fun _ => True

theorem crossingNeighborhoodTestTarget_subset (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (j : CrossingNeighborhoodTests S i) :
    crossingNeighborhoodTestTarget S i j ⊆ S.vertices (i+1) := by
  rcases j with ⟨x,c⟩ | (⟨b,x,y⟩ | ⟨x,c⟩)
  · exact prefixPartVertices_subset S _ _
  · exact prefixPartVertices_subset S _ _
  · exact (protectedCrossingPart_subset S i c).trans (prefixPartVertices_subset S _ _)

theorem crossingNeighborhoodTestTarget_card_le (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (hi : i+1 ≤ l) (hρ : ρ ≤ 1)
    (hn : 2 ≤ (nestedCoreSize ρ m i : ℝ)) (hk : (k:ℝ)/m ≤ 3/2)
    (j : CrossingNeighborhoodTests S i) :
    (crossingNeighborhoodTestTarget S i j).card ≤ 2*nestedCoreSize ρ m i := by
  rcases j with ⟨x,c⟩ | (⟨b,x,y⟩ | ⟨x,c⟩)
  · exact inner_prefixPart_card_le S i hi hρ hn hk _
  · exact inner_prefixPart_card_le S i hi hρ hn hk _
  · exact (card_le_card (protectedCrossingPart_subset S i c)).trans
      (inner_prefixPart_card_le S i hi hρ hn hk c)

/-- The three families of single-neighborhood deviations hold in the
same sampled crossing graph as (R1) and (R3). -/
theorem exists_crossing_reserve_with_concrete_neighborhood_deviations
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (p : (j : Fin 6) → CrossingPart S i j → CrossingPart S i (crossingNext j) → ℝ)
    {μ ξ δ : ℝ} (hμ : 0 < μ) (hξ : 0 < ξ) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hi : i+1 ≤ l) (hm : 0 < m) (hK : (k:ℝ)/m ≤ 3/2) (hHalf : 1/2 ≤ (k:ℝ)/m)
    (hn : 2 ≤ (nestedCoreSize ρ m i : ℝ)) (hInit : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hδ : 0 ≤ δ) (hSmall : 18*δ ≤ ρ) (hRound : 1/2 ≤ δ*nestedCoreSize ρ m i)
    (hBounds : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hLarge : 5184/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 < (nestedCoreSize ρ m i : ℝ))
    (hZero : ∀ j a b, ¬crossingArc S i F P Q j (crossingNext j) a b → p j a b=0)
    (hp : ∀ j a b, crossingArc S i F P Q j (crossingNext j) a b →
      p j a b ∈ Set.Ioo (0:ℝ) 1 ∧ μ/2 ≤ p j a b ∧ p j a b ≤ 2*μ)
    (hMean : ∀ j (a : CrossingPart S i (crossingNext j)),
      (∑ b, p (crossingNext j) a b) = ∑ b, p j b a) :
    let n : ℝ := nestedCoreSize ρ m i
    let X := S.vertices i \ S.vertices (i+1)
    let I := CyclicEdgeSlot (V := CrossingPart S i) crossingNext
    let prob := fun e : I => p e.1 e.2.1 e.2.2
    let H := CrossingNeighborhoodTests S i
    ∃ tests : H → Finset I, ∃ sample : I → Bool,
      (∀ v, let R := sampledCrossingArcs S i F P Q sample
        |(arcDivergence R v : ℝ)| ≤ ξ*n ∧ (incidentDegree R v : ℝ) ≤ 10*μ*n) ∧
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y →
        let c : ℝ := (sampledCrossingCommonNeighbors S i F P Q sample x y).card
        c ≤ 50*μ^2*ρ*n ∧ (tripartiteAdjacent F P Q x y → μ^2*ρ*n/20 ≤ c)) ∧
      (∀ j, (tests j).card ≤ (crossingNeighborhoodTestTarget S i j).card ∧
        (∀ e ∈ tests j, let arc := crossingArcSlotEmbedding S i e
          tripartiteArc F P Q arc.1 arc.2) ∧
        (tests j).card = ((crossingNeighborhoodTestTarget S i j).filter
          (fun z => tripartiteAdjacent F P Q (crossingNeighborhoodTestVertex S i j).val z ∧
            crossingNeighborhoodTestFilter S i F P Q j z)).card ∧
        |((crossingNeighborhoodTestTarget S i j).filter (fun z => sampledCrossingAdjacent S i F P Q sample (crossingNeighborhoodTestVertex S i j).val z ∧ crossingNeighborhoodTestFilter S i F P Q j z)).card
          - mean prob (tests j)| ≤ min (ξ*n/2) (μ*n)) ∧
      ∀ x ∈ X, ∀ c, let V := protectedCrossingPart S i c
        ((V.filter (sampledCrossingAdjacent S i F P Q sample x)).card : ℝ)
          ≤ 3*μ*(V.card : ℝ)+ξ*n := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hK' := (div_le_iff₀ hmR).mp hK
  have hρ' : ρ ≤ 1 := by linarith only [hρsmall]
  obtain ⟨hInner,_,_⟩ := nested_crossing_core_window hρ hρsmall hInit
  have hInnerNat : 1 ≤ nestedCoreSize ρ m (i+1) := by
    have h : (1:ℝ) ≤ nestedCoreSize ρ m (i+1) := hInit.trans hInner
    exact_mod_cast h
  obtain ⟨tests,sample,hR1,hR3,hCounts⟩ := exists_crossing_reserve_with_neighborhood_counts S i F P Q p
    (fun j => (crossingNeighborhoodTestVertex S i j).val) (crossingNeighborhoodTestTarget S i)
    (crossingNeighborhoodTestFilter S i F P Q) (fun j => (crossingNeighborhoodTestVertex S i j).property)
    (crossingNeighborhoodTestTarget_subset S i) (crossingNeighborhoodTestTarget_card_le S i hi hρ' hn hK)
    hμ hξ hρ hρsmall hi hm hK hHalf hn hInit hδ hSmall hRound hBounds
    (crossing_neighborhood_test_budget S i hi hm hK' hρ' hInnerNat)
    (by norm_num only [show (54:ℝ)*(40+56)=5184 by norm_num]; exact hLarge)
    hZero hp hMean
  refine ⟨tests,sample,hR1,hR3,hCounts,?_⟩
  intro x hx c
  let j : CrossingNeighborhoodTests S i := .inr (.inr (⟨x,hx⟩,c))
  let V := protectedCrossingPart S i c
  let pSlot := fun e : CyclicEdgeSlot (V := CrossingPart S i) crossingNext => p e.1 e.2.1 e.2.2
  let actual : ℝ := (V.filter (sampledCrossingAdjacent S i F P Q sample x)).card
  have hCard : (tests j).card ≤ V.card := (hCounts j).1
  have hProb : ∀ e ∈ tests j, pSlot e ≤ 2*μ := fun e he =>
    (hp e.1 e.2.1 e.2.2 ((hCounts j).2.1 e he)).2.2
  have hDeviation := (hCounts j).2.2.2
  simp only [j,crossingNeighborhoodTestTarget,crossingNeighborhoodTestVertex,
    crossingNeighborhoodTestFilter,and_true] at hDeviation
  have hMeanUpper : mean pSlot (tests j) ≤ 2*μ*((tests j).card : ℝ) := by
    unfold mean
    rw [mul_comm (2*μ), ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hProb
  have hc : ((tests j).card : ℝ) ≤ V.card := by exact_mod_cast hCard
  have hMul := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*μ by positivity)
  have hξn : 0 ≤ ξ*(nestedCoreSize ρ m i : ℝ) := by positivity
  change actual ≤ _
  have hUpper := (abs_le.mp hDeviation).2.trans (min_le_left _ _)
  linarith only [hMeanUpper,hMul,hUpper,hξn,mul_nonneg hμ.le (Nat.cast_nonneg V.card)]

end OverfullWork.ChenShan
