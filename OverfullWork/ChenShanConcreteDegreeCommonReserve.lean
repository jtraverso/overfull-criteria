module

public import OverfullWork.ChenShanCrossingSampleGraph
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- A single sample on Chen–Shan's actual six crossing pairs meets
the degree tests (R1) and every common-neighbor test (R3). The constants
come from the per-test estimates and the quadratic count of outer pairs. -/
theorem exists_crossing_reserve_degree_and_common_sample
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (p : (j : Fin 6) → CrossingPart S i j → CrossingPart S i (crossingNext j) → ℝ)
    {μ ξ δ : ℝ} (hμ : 0 < μ) (hξ : 0 < ξ) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hi : i+1 ≤ l) (hm : 0 < m) (hK : (k:ℝ)/m ≤ 3/2) (hHalf : 1/2 ≤ (k:ℝ)/m)
    (hn : 2 ≤ (nestedCoreSize ρ m i : ℝ)) (hInit : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hδ : 0 ≤ δ) (hSmall : 18*δ ≤ ρ) (hRound : 1/2 ≤ δ*nestedCoreSize ρ m i)
    (hBounds : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hLarge : 2160/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 < (nestedCoreSize ρ m i : ℝ))
    (hZero : ∀ j a b, ¬crossingArc S i F P Q j (crossingNext j) a b → p j a b=0)
    (hp : ∀ j a b, crossingArc S i F P Q j (crossingNext j) a b →
      p j a b ∈ Set.Ioo (0:ℝ) 1 ∧ μ/2 ≤ p j a b ∧ p j a b ≤ 2*μ)
    (hMean : ∀ j (a : CrossingPart S i (crossingNext j)),
      (∑ b, p (crossingNext j) a b) = ∑ b, p j b a) :
    let n : ℝ := nestedCoreSize ρ m i
    let X := S.vertices i \ S.vertices (i+1)
    ∃ sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool,
      (∀ v, let R := sampledCrossingArcs S i F P Q sample
        |(arcDivergence R v : ℝ)| ≤ ξ*n ∧ (incidentDegree R v : ℝ) ≤ 10*μ*n) ∧
      ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
        let c : ℝ := (sampledCrossingCommonNeighbors S i F P Q sample x y).card
        c ≤ 50*μ^2*ρ*n ∧ (tripartiteAdjacent F P Q x y → μ^2*ρ*n/20 ≤ c) := by
  dsimp only
  let E := fun j => crossingArc S i F P Q j (crossingNext j)
  let n : ℝ := nestedCoreSize ρ m i
  let X := S.vertices i \ S.vertices (i+1)
  let I := CyclicEdgeSlot (V := CrossingPart S i) crossingNext
  let V := Σ j, CrossingPart S i (crossingNext j)
  let J := {q : ↥X × ↥X // q.1 ≠ q.2}
  let prob (e : I) := p e.1 e.2.1 e.2.2
  let In (v : V) := cyclicInNeighbors crossingNext E v.1 v.2
  let Out (v : V) := cyclicOutNeighbors crossingNext E (crossingNext v.1) v.2
  let Z (j : J) := crossingCommonCandidates S i F P Q j.1.1.1 j.1.2.1
  have hn₀ : 0 < n := by linarith only [hn]
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hK' := (div_le_iff₀ hmR).mp hK
  obtain ⟨hs₀,hs₁,_⟩ := nested_crossing_core_window hρ hρsmall hInit
  have hsNat : 1 ≤ nestedCoreSize ρ m (i+1) := by
    have hh : (1:ℝ) ≤ nestedCoreSize ρ m (i+1) := hInit.trans hs₀
    exact_mod_cast hh
  have hSlots (j : J) : ∃ f : (↥(Z j) × Bool) ↪ I,
      ∀ z b, let out := if b then j.1.2.1 else j.1.1.1
        let arc := crossingArcSlotEmbedding S i (f (z,b))
        (arc=(out,z.1) ∨ arc=(z.1,out)) ∧ tripartiteArc F P Q arc.1 arc.2 := by
    have hne : j.1.1.1 ≠ j.1.2.1 := fun h => j.2 (Subtype.ext h)
    obtain ⟨f,hf⟩ := crossing_common_candidates_slots S i F P Q j.1.1.1 j.1.2.1
      hne j.1.1.2 j.1.2.2
    refine ⟨f,fun z b => ?_⟩
    exact ⟨(hf (z,b)).1.imp (fun h => Prod.ext h.1 h.2) (fun h => Prod.ext h.1 h.2),
      (hf (z,b)).2⟩
  choose f hf using hSlots
  have hLocal (j : J) (z : ↥(Z j)) (_ : z ∈ (univ : Finset ↥(Z j))) (b : Bool) :
      μ/2 ≤ prob (f j (z,b)) ∧ prob (f j (z,b)) ≤ 2*μ := by
    have hs := (hf j z b).2
    exact (hp _ _ _ hs).2
  have hCard (j : J) : (((univ : Finset ↥(Z j))).card : ℝ) ≤ 8*ρ*n := by
    have hSub : Z j ⊆ S.vertices (i+1) := filter_subset _ _
    have hh : ((Z j).card : ℝ) ≤ (S.vertices (i+1)).card := by exact_mod_cast card_le_card hSub
    simpa only [card_univ,Fintype.card_coe] using hh.trans
      (crossing_inner_vertices_card_le S i hi hm hK' hsNat hs₁)
  have hUpper (j : Fin 6) := crossingPart_card_le S i hi (by linarith only [hρsmall]) hn hK j
  have hV : (Fintype.card V : ℝ) ≤ 12*n := by
    unfold V
    rw [Fintype.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _ : Fin 6, 2*n := sum_le_sum fun j _ => hUpper (crossingNext j)
      _ = _ := by simp [nsmul_eq_mul]; ring
  have hJn : Fintype.card J ≤ Fintype.card (↥X × ↥X) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hJ : (Fintype.card J : ℝ) ≤ 16*n^2 :=
    (show (Fintype.card J : ℝ) ≤ Fintype.card (↥X × ↥X) by exact_mod_cast hJn).trans
      (crossing_outer_pair_test_budget S i (by omega) hm hK' (by
        have hh : (1:ℝ) ≤ nestedCoreSize ρ m i := by linarith only [hn]
        exact_mod_cast hh))
  have hTests : 2*(Fintype.card V : ℝ)+Fintype.card J ≤ 40*n^2 := by
    have hSq : n ≤ n^2 := by
      have hh := mul_le_mul_of_nonneg_right (show 1 ≤ n by linarith only [hn]) hn₀.le
      nlinarith only [hh]
    linarith only [hV,hJ,hSq]
  have hPall (j : Fin 6) a b : p j a b ∈ Set.Icc (0:ℝ) 1 ∧ p j a b ≤ 2*μ := by
    by_cases h : E j a b
    · exact ⟨⟨(hp _ _ _ h).1.1.le,(hp _ _ _ h).1.2.le⟩,(hp _ _ _ h).2.2⟩
    · rw [hZero _ _ _ h]
      exact ⟨⟨le_rfl,by norm_num⟩,by positivity⟩
  have hBal (v : V) : mean prob (In v) = mean prob (Out v) := by
    dsimp only [In,Out,prob]
    rw [cyclicInNeighbors_mean crossingNext E p hZero,cyclicOutNeighbors_mean crossingNext E p hZero]
    exact (hMean v.1 v.2).symm
  have hBound (v : V) : mean prob (Out v) ≤ 4*μ*n := by
    dsimp only [Out,prob]
    rw [cyclicOutNeighbors_mean crossingNext E p hZero]
    calc
      _ ≤ ∑ _ : CrossingPart S i (crossingNext (crossingNext v.1)), 2*μ :=
        sum_le_sum fun b _ => (hPall _ _ b).2
      _ = (Fintype.card (CrossingPart S i (crossingNext (crossingNext v.1))) : ℝ)*(2*μ) :=
        by simp [nsmul_eq_mul]
      _ ≤ (2*n)*(2*μ) := mul_le_mul_of_nonneg_right (hUpper _) (by positivity)
      _ = _ := by ring
  obtain ⟨sample,hDegree,hPairs⟩ := exists_reserve_with_degree_and_common_neighbor_tests
    prob (fun e => (hPall e.1 e.2.1 e.2.2).1.1) (fun e => (hPall e.1 e.2.1 e.2.2).1.2)
    In Out (fun j => (univ : Finset ↥(Z j))) f hμ hρ hξ hn₀ hBal hBound hLocal hCard hTests
    (by norm_num only [show (54:ℝ)*40=2160 by norm_num]; exact hLarge)
  refine ⟨sample,?_,?_⟩
  · exact sampledCrossingArc_degree_control S i F P Q sample (ξ*n) (10*μ*n)
      (mul_nonneg hξ.le hn₀.le) (by positivity) (fun j a => hDegree ⟨j,a⟩)
  · intro x hx y hy hxy
    let j : J := ⟨(⟨x,hx⟩,⟨y,hy⟩),fun h => hxy (congrArg Subtype.val h)⟩
    have hGraph := crossing_common_count_eq_graph S i F P Q sample x y (f j) (hf j)
    have h := hPairs j
    dsimp only at h
    rw [hGraph] at h
    refine ⟨h.1,fun hAdj => h.2 ?_⟩
    rw [card_univ,Fintype.card_coe]
    exact adjacent_crossing_common_candidate_card S i F P Q hBounds hi hHalf hs₀ hδ hSmall hRound
      (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1 hAdj


/-- The concrete joint conclusion follows from (4.23), selecting the
probabilities and the sample inside the proof. -/
theorem exists_crossing_graph_degree_and_common_reserve
    {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i+1 ≤ l)
    {η δ μ ξ : ℝ} (hm : 0 < m) (hη : 0 < η) (hηhalf : η ≤ 1/2)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4) (hδ : 0 ≤ δ)
    (hInit : 6 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hSlack : 1 ≤ δ*(nestedCoreSize ρ m i : ℝ))
    (hp : 1/2+η ≤ (k:ℝ)/m) (hK : (k:ℝ)/m ≤ 3/2) (hMin : 18*δ ≤ η*ρ)
    (hθsmall : 16*δ/ρ ≤ 1/4) (hθtight : (8/η)*(16*δ/ρ) < 1/2)
    (hμ : 0 < μ) (hμupper : μ < 1/4) (hξ : 0 < ξ)
    (hb : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hLarge : 2160/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 <
      (nestedCoreSize ρ m i : ℝ)) :
    let n : ℝ := nestedCoreSize ρ m i
    let U := S.vertices (i+1)
    let X := S.vertices i \ U
    ∃ R : Finset (TripartiteVertex A B W × TripartiteVertex A B W),
      R ⊆ tripartiteArcs F P Q \ (U ×ˢ U) ∧
      (∀ v, |(arcDivergence R v : ℝ)| ≤ ξ*n ∧ (incidentDegree R v : ℝ) ≤ 10*μ*n) ∧
      ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
        let c : ℝ := (U.filter (fun z => ((x,z) ∈ R ∨ (z,x) ∈ R) ∧
          ((y,z) ∈ R ∨ (z,y) ∈ R))).card
        c ≤ 50*μ^2*ρ*n ∧ (tripartiteAdjacent F P Q x y → μ^2*ρ*n/20 ≤ c) := by
  dsimp only
  let n : ℝ := nestedCoreSize ρ m i
  have hn₀ : 0 ≤ n := by dsimp only [n]; positivity
  have hRn := mul_le_mul_of_nonneg_right hρsmall hn₀
  have hn : 2 ≤ n := by linarith only [hRn,hInit]
  have hSmall : 18*δ ≤ ρ := by
    have h := (div_le_iff₀ hρ).mp hθsmall
    linarith only [h,hδ]
  have hHalf : 1/2 ≤ (k:ℝ)/m := by linarith only [hp,hη]
  obtain ⟨p,hZero,hProb,hBalance⟩ := exists_crossing_cycle_reserve_probabilities S i hi
    hm hη hηhalf hρ hρsmall hδ hInit hSlack hp hMin hθsmall hθtight hμ hμupper hb
  have hWindow (j : Fin 6) a b (h : crossingArc S i F P Q j (crossingNext j) a b) :
      p j a b ∈ Set.Ioo (0:ℝ) 1 ∧ μ/2 ≤ p j a b ∧ p j a b ≤ 2*μ := by
    have hh := (abs_le.mp (hProb j a b h).2)
    have hT := mul_lt_mul_of_pos_left hθtight hμ
    exact ⟨(hProb j a b h).1, by linarith only [hh.1,hT],
      by linarith only [hh.2,hT,hμ]⟩
  obtain ⟨sample,hDeg,hPair⟩ := exists_crossing_reserve_degree_and_common_sample S i F P Q p
    hμ hξ hρ hρsmall hi hm hK hHalf hn (by linarith only [hInit])
    hδ hSmall (by linarith only [hSlack]) hb hLarge hZero hWindow hBalance
  let R := sampledCrossingArcs S i F P Q sample
  refine ⟨R,sampledCrossingArcs_subset_outside_inner S i F P Q sample,hDeg,?_⟩
  intro x hx y hy hxy
  have hEq : sampledCrossingCommonNeighbors S i F P Q sample x y =
      (S.vertices (i+1)).filter (fun z => ((x,z) ∈ R ∨ (z,x) ∈ R) ∧
        ((y,z) ∈ R ∨ (z,y) ∈ R)) := by
    ext z
    simp only [sampledCrossingCommonNeighbors,mem_filter]
    rfl
  rw [← hEq]
  exact hPair x hx y hy hxy

end OverfullWork.ChenShan
