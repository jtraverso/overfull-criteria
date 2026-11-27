module

public import OverfullWork.ChenShanCrossingReserveR2
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- One crossing reserve satisfies all five properties used by Chen and Shan.
The (R4) estimate applies to every vertex of the other eligible class. -/
theorem exists_crossing_reserve_all_five
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (p : (j : Fin 6) → CrossingPart S i j → CrossingPart S i (crossingNext j) → ℝ)
    {μ ξ δ η η₀ : ℝ} (hμ : 0 < μ) (hξ : 0 < ξ) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hi : i+1 ≤ l) (hm : 0 < m) (hK : (k:ℝ)/m ≤ 3/2) (hDensity : 1/2+η ≤ (k:ℝ)/m)
    (hn : 2 ≤ (nestedCoreSize ρ m i : ℝ)) (hInit : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hδ : 0 ≤ δ) (hSmall : 32*δ ≤ ρ) (hRound : 1/2 ≤ δ*nestedCoreSize ρ m i)
    (hη₀ : 0 < η₀) (hη₀small : η₀ ≤ 1/80) (hEta : 40*η₀ ≤ η)
    (hColor : 4*δ ≤ η*ρ) (hξsmall : ξ ≤ η₀*(μ*ρ)/2)
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
    ∃ sample : I → Bool,
      (∀ v, let R := sampledCrossingArcs S i F P Q sample
        |(arcDivergence R v : ℝ)| ≤ ξ*n ∧ (incidentDegree R v : ℝ) ≤ 10*μ*n) ∧
      (∀ x ∈ X, ∀ c, c ≠ crossingPartTag x →
        let a : ℝ := ((prefixPartVertices S (i+1) c).filter
          (sampledCrossingAdjacent S i F P Q sample x)).card
        μ*(ρ*n)/4 ≤ a ∧ a ≤ 4*μ*(ρ*n)) ∧
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y →
        let c : ℝ := (sampledCrossingCommonNeighbors S i F P Q sample x y).card
        c ≤ 50*μ^2*ρ*n ∧ (tripartiteAdjacent F P Q x y → μ^2*ρ*n/20 ≤ c)) ∧
      (∀ u ∈ X, ∀ x ∈ S.vertices (i+1), crossingPartTag u ≠ crossingPartTag x →
        let c := remainingCrossingPart (crossingPartTag u) (crossingPartTag x)
        let Y := (prefixPartVertices S (i+1) c).filter
          (sampledCrossingAdjacent S i F P Q sample u)
        (1/2+8*η₀)*(Y.card : ℝ) ≤ (Y.filter (tripartiteAdjacent F P Q x)).card) ∧
      ∀ x ∈ X, ∀ c, let V := protectedCrossingPart S i c
        ((V.filter (sampledCrossingAdjacent S i F P Q sample x)).card : ℝ)
          ≤ 3*μ*(V.card : ℝ)+ξ*n := by
  let n : ℝ := nestedCoreSize ρ m i
  have hn₀ : 0 < n := by linarith only [hn]
  have hHalf : 1/2 ≤ (k:ℝ)/m := by linarith only [hEta,hη₀,hDensity]
  have hBudget : 16*δ ≤ ρ := by linarith only [hSmall,hδ]
  have hηsmall : η₀ ≤ 1/40 := by linarith only [hη₀small]
  have hξ₂ : ξ ≤ μ*ρ/4 := by
    have h := mul_le_mul_of_nonneg_right hη₀small (mul_nonneg hμ.le hρ.le)
    linarith only [h,hξsmall,mul_nonneg hμ.le hρ.le]
  obtain ⟨tests,sample,hR1,hR3,hCounts,hR5,hR2⟩ :=
    exists_crossing_reserve_with_r2 S i F P Q p hμ hξ hρ hρsmall hi hm hK hHalf hn
      hInit hδ hSmall hRound hη₀small hξ₂ hBounds hLarge hZero hp hNear hMean
  refine ⟨sample,hR1,hR2,hR3,?_,hR5⟩
  intro u hu x hx hne
  let c := remainingCrossingPart (crossingPartTag u) (crossingPartTag x)
  let Z := prefixPartVertices S (i+1) c
  let N := Z.filter (tripartiteAdjacent F P Q u)
  let j₀ : CrossingNeighborhoodTests S i := .inr (.inl (false,⟨u,hu⟩,⟨x,hx⟩))
  let j₁ : CrossingNeighborhoodTests S i := .inr (.inl (true,⟨u,hu⟩,⟨x,hx⟩))
  let prob := fun e : CyclicEdgeSlot (V := CrossingPart S i) crossingNext => p e.1 e.2.1 e.2.2
  have hCard₀ := (hCounts j₀).2.2.1
  have hCard₁ := (hCounts j₁).2.2.1
  have hDev₀ := (hCounts j₀).2.2.2
  have hDev₁ := (hCounts j₁).2.2.2
  simp only [j₀,j₁,crossingNeighborhoodTestTarget,crossingNeighborhoodTestVertex,
    crossingNeighborhoodTestFilter,and_true] at hCard₀ hCard₁ hDev₀ hDev₁
  have filterBoth (a b : TripartiteVertex A B W → Prop) :
      (Z.filter a).filter b = Z.filter (fun z => a z ∧ b z) := by
    ext z
    simp only [mem_filter,and_assoc]
  have hDet := reserve_tagged_r4_margin hBounds hi hm hη₀.le hη₀small hEta hDensity
    hBudget hColor u x (mem_sdiff.mp hu).1 hx hne
  change (1/2+20*η₀)*(N.card : ℝ) ≤ (N.filter (tripartiteAdjacent F P Q x)).card at hDet
  have hRatioCard : (1/2+20*η₀)*((tests j₀).card : ℝ) ≤ (tests j₁).card := by
    rw [hCard₀,hCard₁]
    simp only [N,Z,c,filterBoth] at hDet
    convert hDet using 1
    congr 3
  have hc : c ≠ crossingPartTag u := remainingCrossingPart_ne_left hne
  have hBefore := reserve_part_neighbor_card_bounds hBounds hi hm hρ hρsmall hInit
    hSmall hHalf hK u (mem_sdiff.mp hu).1 c hc
  dsimp only at hBefore
  have hLo : 15*(ρ*n)/32 ≤ ((tests j₀).card : ℝ) := by rw [hCard₀]; exact hBefore.1
  have hHi : ((tests j₀).card : ℝ) ≤ 97*(ρ*n)/32 := by rw [hCard₀]; exact hBefore.2
  have hNearSlot (j : CrossingNeighborhoodTests S i) (e) (he : e ∈ tests j) :
      |prob e-μ| ≤ μ*η₀/100 :=
    hNear e.1 e.2.1 e.2.2 ((hCounts j).2.1 e he)
  have hNonempty : (tests j₀).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (show (0:ℝ) < (tests j₀).card from
      (div_pos (mul_pos (by norm_num) (mul_pos hρ hn₀)) (by norm_num)).trans_le hLo)
  have hMeans := reserve_neighborhood_mean_ratio_of_card prob (tests j₀) (tests j₁)
    hNonempty hμ hη₀ hηsmall (hNearSlot j₀) (hNearSlot j₁) hRatioCard
  have hMuLo := (reserve_inner_count_mean prob (tests j₀) hμ hLo hHi
    (fun e he => reserve_probability_window hμ hη₀small (hNearSlot j₀ e he))
    (mul_nonneg hρ.le hn₀.le)).1
  have hError : min (ξ*n/2) (μ*n) ≤ η₀*mean prob (tests j₀) := by
    apply (min_le_left _ _).trans
    have h₁ := mul_le_mul_of_nonneg_right hξsmall hn₀.le
    have h₂ := mul_le_mul_of_nonneg_left hMuLo hη₀.le
    have h₃ := mul_nonneg hη₀.le (mul_nonneg hμ.le (mul_nonneg hρ.le hn₀.le))
    linarith only [h₁,h₂,h₃]
  have hCount := reserve_sample_neighborhood_ratio hη₀.le hηsmall
    ((by positivity : 0 ≤ 3*μ*(ρ*n)/8).trans hMuLo) (le_min (by positivity) (by positivity))
    hError hMeans.le hDev₀ hDev₁
  simp only [Z,c,filterBoth]
  convert hCount using 1
  congr 3

/-- Starting from the crossing estimates of (4.23), choose the balanced
probabilities and a reserve satisfying (R1)–(R5). -/
theorem exists_crossing_graph_reserve_all_five
    {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i+1 ≤ l)
    {η η₀ δ μ ξ : ℝ} (hm : 0 < m) (hη₀ : 0 < η₀) (hη₀small : η₀ ≤ 1/80)
    (hEta : 40*η₀ ≤ η) (hηhalf : η ≤ 1/2)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4) (hδ : 0 ≤ δ)
    (hInit : 6 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hSlack : 1 ≤ δ*(nestedCoreSize ρ m i : ℝ))
    (hDensity : 1/2+η ≤ (k:ℝ)/m) (hK : (k:ℝ)/m ≤ 3/2) (hMin : 18*δ ≤ η*ρ)
    (hClose : (8/η)*(16*δ/ρ) ≤ η₀/100)
    (hμ : 0 < μ) (hμupper : μ < 1/4) (hξ : 0 < ξ) (hξsmall : ξ ≤ η₀*(μ*ρ)/2)
    (hb : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hLarge : 5184/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 <
      (nestedCoreSize ρ m i : ℝ)) :
    let n : ℝ := nestedCoreSize ρ m i
    let U := S.vertices (i+1)
    let X := S.vertices i \ U
    ∃ R : Finset (TripartiteVertex A B W × TripartiteVertex A B W),
      let Adj := fun x y => (x,y) ∈ R ∨ (y,x) ∈ R
      R ⊆ tripartiteArcs F P Q \ (U ×ˢ U) ∧
      (∀ a b, (a,b) ∈ R → CrossesNestedPrefix S i a b) ∧
      (∀ v, |(arcDivergence R v : ℝ)| ≤ ξ*n ∧ (incidentDegree R v : ℝ) ≤ 10*μ*n) ∧
      (∀ x ∈ X, ∀ c, c ≠ crossingPartTag x →
        let a : ℝ := ((prefixPartVertices S (i+1) c).filter (Adj x)).card
        μ*(ρ*n)/4 ≤ a ∧ a ≤ 4*μ*(ρ*n)) ∧
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y →
        let c : ℝ := (U.filter (fun z => Adj x z ∧ Adj y z)).card
        c ≤ 50*μ^2*ρ*n ∧ (tripartiteAdjacent F P Q x y → μ^2*ρ*n/20 ≤ c)) ∧
      (∀ u ∈ X, ∀ x ∈ U, crossingPartTag u ≠ crossingPartTag x →
        let c := remainingCrossingPart (crossingPartTag u) (crossingPartTag x)
        let Y := (prefixPartVertices S (i+1) c).filter (Adj u)
        (1/2+8*η₀)*(Y.card : ℝ) ≤ (Y.filter (tripartiteAdjacent F P Q x)).card) ∧
      ∀ x ∈ X, ∀ c, let V := protectedCrossingPart S i c
        ((V.filter (Adj x)).card : ℝ) ≤ 3*μ*(V.card : ℝ)+ξ*n := by
  let n : ℝ := nestedCoreSize ρ m i
  have hη : 0 < η := by linarith only [hη₀,hEta]
  have hn₀ : 0 ≤ n := by positivity
  have hRn := mul_le_mul_of_nonneg_right hρsmall hn₀
  have hn : 2 ≤ n := by linarith only [hRn,hInit]
  have hθ₀ : 0 ≤ 16*δ/ρ := by positivity
  have hFactor : 1 ≤ 8/η := (le_div_iff₀ hη).mpr (by linarith only [hηhalf])
  have hθ := mul_le_mul_of_nonneg_right hFactor hθ₀
  have hθsmall : 16*δ/ρ ≤ 1/4 := by linarith only [hθ,hClose,hη₀small]
  have hθtight : (8/η)*(16*δ/ρ) < 1/2 := by linarith only [hClose,hη₀small]
  have hSmall : 32*δ ≤ ρ := by
    have h := (div_le_iff₀ hρ).mp hθsmall
    linarith only [h,hδ]
  have hColor : 4*δ ≤ η*ρ := by linarith only [hMin,hδ]
  obtain ⟨p,hZero,hProb,hBalance⟩ := exists_crossing_cycle_reserve_probabilities S i hi
    hm hη hηhalf hρ hρsmall hδ hInit hSlack hDensity hMin hθsmall hθtight hμ hμupper hb
  have hNear (j : Fin 6) a b (h : crossingArc S i F P Q j (crossingNext j) a b) :
      |p j a b-μ| ≤ μ*η₀/100 := by
    exact (hProb j a b h).2.trans (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hClose hμ.le)
  have hWindow (j : Fin 6) a b (h : crossingArc S i F P Q j (crossingNext j) a b) :
      p j a b ∈ Set.Ioo (0:ℝ) 1 ∧ μ/2 ≤ p j a b ∧ p j a b ≤ 2*μ := by
    obtain ⟨hlo,hhi⟩ := reserve_probability_window hμ hη₀small (hNear j a b h)
    exact ⟨(hProb j a b h).1, by linarith only [hlo,hμ], by linarith only [hhi,hμ]⟩
  obtain ⟨sample,hR1,hR2,hR3,hR4,hR5⟩ := exists_crossing_reserve_all_five S i F P Q p
    hμ hξ hρ hρsmall hi hm hK hDensity hn (by linarith only [hInit]) hδ hSmall
    (by linarith only [hSlack]) hη₀ hη₀small hEta hColor hξsmall hb hLarge
    hZero hWindow hNear hBalance
  refine ⟨sampledCrossingArcs S i F P Q sample,
    sampledCrossingArcs_subset_outside_inner S i F P Q sample,
    fun _ _ h => sampledCrossingArcs_crosses S i F P Q sample h,hR1,?_,?_,?_,?_⟩
  · intro x hx c hc
    convert hR2 x hx c hc using 1
    apply Iff.of_eq
    dsimp only
    congr 8
  · intro x hx y hy hxy
    convert hR3 x hx y hy hxy using 1
    apply Iff.of_eq
    dsimp only
    congr 8
  · intro u hu x hx hne
    convert hR4 u hu x hx hne using 1
    apply Iff.of_eq
    dsimp only
    congr 8
  · intro x hx c
    convert hR5 x hx c using 1
    apply Iff.of_eq
    dsimp only
    congr 8

end OverfullWork.ChenShan
