module

public import OverfullWork.ChenShanCrossingNeighborhoodParts
public import OverfullWork.ChenShanReserveNeighborhoodMean
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}
variable {S : NestedTripartitePrefixes A B W ρ m k l} {i : ℕ}
variable {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}

/-- A neighborhood can be tested by counting a fixed subset of the crossing
slots. Its size is bounded by the size of the target set. -/
theorem exists_crossing_neighborhood_test
    (x : TripartiteVertex A B W) (hx : x ∈ S.vertices i \ S.vertices (i+1))
    (Z : Finset (TripartiteVertex A B W)) (hZ : Z ⊆ S.vertices (i+1))
    (Good : TripartiteVertex A B W → Prop) :
    ∃ T : Finset (CyclicEdgeSlot (V := CrossingPart S i) crossingNext),
      T.card ≤ Z.card ∧
      (∀ e ∈ T, let arc := crossingArcSlotEmbedding S i e
        tripartiteArc F P Q arc.1 arc.2) ∧
      ∀ sample, count T sample =
        ((Z.filter (fun z => sampledCrossingAdjacent S i F P Q sample x z ∧ Good z)).card : ℝ) := by
  obtain ⟨f,hf⟩ := exists_slots_for_outer_neighborhood S i F P Q x hx Z hZ
  let U := univ.filter (fun z : ↥(Z.filter (tripartiteAdjacent F P Q x)) => Good z.1)
  refine ⟨U.map f,?_,?_,?_⟩
  · rw [card_map]
    exact (card_filter_le _ _).trans (by rw [card_univ,Fintype.card_coe]; exact card_filter_le _ _)
  · intro e he
    obtain ⟨z,_,rfl⟩ := mem_map.mp he
    exact (hf z).2
  · intro sample
    apply crossing_neighborhood_count_eq_graph
    intro z
    exact ⟨(hf z).1.imp (fun h => Prod.ext h.1 h.2) (fun h => Prod.ext h.1 h.2),(hf z).2⟩

/-- The deviation estimate for a protected-prefix test is exactly the
upper bound on the corresponding neighborhood in (R5). -/
theorem crossing_neighborhood_test_upper
    {T : Finset (CyclicEdgeSlot (V := CrossingPart S i) crossingNext)}
    {x : TripartiteVertex A B W} {Z : Finset (TripartiteVertex A B W)}
    {Good : TripartiteVertex A B W → Prop}
    (p : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → ℝ)
    (sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool)
    {μ ξ n : ℝ} (hμ : 0 ≤ μ) (hcard : T.card ≤ Z.card)
    (hP : ∀ e ∈ T, p e ≤ 3*μ)
    (hEq : count T sample =
      ((Z.filter (fun z => sampledCrossingAdjacent S i F P Q sample x z ∧ Good z)).card : ℝ))
    (hSample : |count T sample-mean p T| ≤ ξ*n) :
    ((Z.filter (fun z => sampledCrossingAdjacent S i F P Q sample x z ∧ Good z)).card : ℝ)
      ≤ 3*μ*(Z.card : ℝ)+ξ*n := by
  rw [← hEq]
  apply (reserve_sample_protected_prefix_count p T sample hP hSample).trans
  gcongr

/-- Simultaneously impose neighborhood counts specified by their outside
vertex, target set and extra filter, alongside (R1) and (R3). -/
theorem exists_crossing_reserve_with_neighborhood_counts
    {H : Type*} [Fintype H]
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (p : (j : Fin 6) → CrossingPart S i j → CrossingPart S i (crossingNext j) → ℝ)
    (x : H → TripartiteVertex A B W) (Z : H → Finset (TripartiteVertex A B W))
    (Good : H → TripartiteVertex A B W → Prop)
    (hx : ∀ j, x j ∈ S.vertices i \ S.vertices (i+1))
    (hZ : ∀ j, Z j ⊆ S.vertices (i+1))
    (hCard : ∀ j, (Z j).card ≤ 2*nestedCoreSize ρ m i)
    {μ ξ δ C : ℝ} (hμ : 0 < μ) (hξ : 0 < ξ) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hi : i+1 ≤ l) (hm : 0 < m) (hK : (k:ℝ)/m ≤ 3/2) (hHalf : 1/2 ≤ (k:ℝ)/m)
    (hn : 2 ≤ (nestedCoreSize ρ m i : ℝ)) (hInit : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hδ : 0 ≤ δ) (hSmall : 18*δ ≤ ρ) (hRound : 1/2 ≤ δ*nestedCoreSize ρ m i)
    (hBounds : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hExtraCount : (Fintype.card H : ℝ) ≤ C*(nestedCoreSize ρ m i : ℝ)^2)
    (hLarge : (54*(40+C))/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 < (nestedCoreSize ρ m i : ℝ))
    (hZero : ∀ j a b, ¬crossingArc S i F P Q j (crossingNext j) a b → p j a b=0)
    (hp : ∀ j a b, crossingArc S i F P Q j (crossingNext j) a b →
      p j a b ∈ Set.Ioo (0:ℝ) 1 ∧ μ/2 ≤ p j a b ∧ p j a b ≤ 2*μ)
    (hMean : ∀ j (a : CrossingPart S i (crossingNext j)),
      (∑ b, p (crossingNext j) a b) = ∑ b, p j b a) :
    let n : ℝ := nestedCoreSize ρ m i
    let X := S.vertices i \ S.vertices (i+1)
    let I := CyclicEdgeSlot (V := CrossingPart S i) crossingNext
    let prob := fun e : I => p e.1 e.2.1 e.2.2
    ∃ tests : H → Finset I, ∃ sample : I → Bool,
      (∀ v, let R := sampledCrossingArcs S i F P Q sample
        |(arcDivergence R v : ℝ)| ≤ ξ*n ∧ (incidentDegree R v : ℝ) ≤ 10*μ*n) ∧
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y →
        let c : ℝ := (sampledCrossingCommonNeighbors S i F P Q sample x y).card
        c ≤ 50*μ^2*ρ*n ∧ (tripartiteAdjacent F P Q x y → μ^2*ρ*n/20 ≤ c)) ∧
      ∀ j, (tests j).card ≤ (Z j).card ∧
        (∀ e ∈ tests j, let arc := crossingArcSlotEmbedding S i e
          tripartiteArc F P Q arc.1 arc.2) ∧
        |((Z j).filter (fun z => sampledCrossingAdjacent S i F P Q sample (x j) z ∧ Good j z)).card
          - mean prob (tests j)| ≤ min (ξ*n/2) (μ*n) := by
  dsimp only
  have hTests (j : H) := exists_crossing_neighborhood_test (F := F) (P := P) (Q := Q)
    (x j) (hx j) (Z j) (hZ j) (Good j)
  choose tests hSize hArc hCount using hTests
  let prob := fun e : CyclicEdgeSlot (V := CrossingPart S i) crossingNext => p e.1 e.2.1 e.2.2
  have hBound (j : H) : mean prob (tests j) ≤ 4*μ*nestedCoreSize ρ m i := by
    have hLe : mean prob (tests j) ≤ 2*μ*((tests j).card : ℝ) := by
      unfold mean
      rw [mul_comm (2*μ), ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun e he => (hp e.1 e.2.1 e.2.2 (hArc j e he)).2.2
    have hc : ((tests j).card : ℝ) ≤ 2*(nestedCoreSize ρ m i : ℝ) := by
      exact_mod_cast (hSize j).trans (hCard j)
    have hb := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*μ by positivity)
    linarith only [hLe,hb]
  obtain ⟨sample,hR1,hR3,hs⟩ := exists_crossing_reserve_with_extra_counts
    S i F P Q p tests hμ hξ hρ hρsmall hi hm hK hHalf hn hInit hδ hSmall hRound hBounds
    hBound hExtraCount hLarge hZero hp hMean
  refine ⟨tests,sample,hR1,hR3,fun j => ⟨hSize j,hArc j,?_⟩⟩
  rw [← hCount j sample]
  exact hs j

end OverfullWork.ChenShan
