module

public import OverfullWork.ChenShanCrossingNeighborhoodCatalog
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- The part containing the exterior vertex contributes no sampled neighbors. -/
theorem sampled_crossing_same_part_neighbors_empty
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    (x : TripartiteVertex A B W) :
    (prefixPartVertices S (i+1) (crossingPartTag x)).filter
      (sampledCrossingAdjacent S i F P Q sample x) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hc,ha⟩ := mem_filter.mp hz
  have he := (mem_filter.mp hc).2
  have ha' : tripartiteAdjacent F P Q x z :=
    ha.imp (sampledCrossingArcs_supported S i F P Q sample)
      (sampledCrossingArcs_supported S i F P Q sample)
  rcases x with a | (b | w) <;> rcases z with a' | (b' | w') <;>
    simp [crossingPartTag,tripartiteAdjacent,tripartiteArc] at he ha'

/-- The concrete reserve satisfies (R2) in each eligible inner class
in the same sample as (R1), (R3), (R5), and the filtered count deviations. -/
theorem exists_crossing_reserve_with_r2
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (p : (j : Fin 6) → CrossingPart S i j → CrossingPart S i (crossingNext j) → ℝ)
    {μ ξ δ η₀ : ℝ} (hμ : 0 < μ) (hξ : 0 < ξ) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hi : i+1 ≤ l) (hm : 0 < m) (hK : (k:ℝ)/m ≤ 3/2) (hHalf : 1/2 ≤ (k:ℝ)/m)
    (hn : 2 ≤ (nestedCoreSize ρ m i : ℝ)) (hInit : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hδ : 0 ≤ δ) (hSmall : 32*δ ≤ ρ) (hRound : 1/2 ≤ δ*nestedCoreSize ρ m i)
    (hη₀small : η₀ ≤ 1/80) (hξsmall : ξ ≤ μ*ρ/4)
    (hBounds : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hLarge : 5184/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 < (nestedCoreSize ρ m i : ℝ))
    (hZero : ∀ j a b, ¬crossingArc S i F P Q j (crossingNext j) a b → p j a b=0)
    (hp : ∀ j a b, crossingArc S i F P Q j (crossingNext j) a b →
      p j a b ∈ Set.Ioo (0:ℝ) 1 ∧ μ/2 ≤ p j a b ∧ p j a b ≤ 2*μ)
    (hNear : ∀ j a b, crossingArc S i F P Q j (crossingNext j) a b →
      |p j a b-μ| ≤ μ*η₀/100)
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
      (∀ x ∈ X, ∀ c, let V := protectedCrossingPart S i c
        ((V.filter (sampledCrossingAdjacent S i F P Q sample x)).card : ℝ)
          ≤ 3*μ*(V.card : ℝ)+ξ*n) ∧
      ∀ x ∈ X, ∀ c, c ≠ crossingPartTag x →
        let a : ℝ := ((prefixPartVertices S (i+1) c).filter
          (sampledCrossingAdjacent S i F P Q sample x)).card
        μ*(ρ*n)/4 ≤ a ∧ a ≤ 4*μ*(ρ*n) := by
  have hSmall' : 18*δ ≤ ρ := by linarith only [hSmall,hδ]
  obtain ⟨tests,sample,hR1,hR3,hCounts,hR5⟩ :=
    exists_crossing_reserve_with_concrete_neighborhood_deviations S i F P Q p
      hμ hξ hρ hρsmall hi hm hK hHalf hn hInit hδ hSmall' hRound hBounds hLarge hZero hp hMean
  refine ⟨tests,sample,hR1,hR3,hCounts,hR5,?_⟩
  intro x hx c hc
  let j : CrossingNeighborhoodTests S i := .inl (⟨x,hx⟩,c)
  let n : ℝ := nestedCoreSize ρ m i
  let prob := fun e : CyclicEdgeSlot (V := CrossingPart S i) crossingNext => p e.1 e.2.1 e.2.2
  have hCard := (hCounts j).2.2.1
  have hDeviation := (hCounts j).2.2.2
  simp only [j,crossingNeighborhoodTestTarget,crossingNeighborhoodTestVertex,
    crossingNeighborhoodTestFilter,and_true] at hCard hDeviation
  have hBefore := reserve_part_neighbor_card_bounds hBounds hi hm hρ hρsmall hInit hSmall
    hHalf hK x (mem_sdiff.mp hx).1 c hc
  dsimp only at hBefore
  have hLo : 15*(ρ*n)/32 ≤ ((tests j).card : ℝ) := by rw [hCard]; exact hBefore.1
  have hHi : ((tests j).card : ℝ) ≤ 97*(ρ*n)/32 := by rw [hCard]; exact hBefore.2
  have hProb (e) (he : e ∈ tests j) : (15/16)*μ ≤ prob e ∧ prob e ≤ (17/16)*μ :=
    reserve_probability_window hμ hη₀small (hNear e.1 e.2.1 e.2.2 ((hCounts j).2.1 e he))
  have ht : 0 ≤ ρ*n := by positivity
  obtain ⟨hMeanLo,hMeanHi⟩ := reserve_inner_count_mean prob (tests j) hμ hLo hHi hProb ht
  have hScale : min (ξ*n/2) (μ*n) ≤ μ*(ρ*n)/8 := by
    have hb := mul_le_mul_of_nonneg_right hξsmall (show 0 ≤ n by positivity)
    exact (min_le_left _ _).trans (by linarith only [hb])
  exact reserve_inner_count_bounds (mul_nonneg hμ.le ht)
    hMeanLo hMeanHi hScale hDeviation

end OverfullWork.ChenShan
