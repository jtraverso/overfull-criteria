module

public import OverfullWork.ChenShanConcreteDegreeCommonReserve
public import OverfullWork.ChenShanReserveTestBudget
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

def crossingPartTag : TripartiteVertex A B W → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

noncomputable def prefixPartVertices (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (c : Fin 3) : Finset (TripartiteVertex A B W) :=
  (S.vertices i).filter (fun v => crossingPartTag v = c)

theorem prefixPartVertices_subset (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (c : Fin 3) : prefixPartVertices S i c ⊆ S.vertices i := filter_subset _ _

theorem prefixPartVertices_antitone (S : NestedTripartitePrefixes A B W ρ m k l)
    (c : Fin 3) : Antitone (fun i => prefixPartVertices S i c) :=
  fun _ _ h => filter_subset_filter _ (S.vertices_antitone h)

def remainingCrossingPart (a b : Fin 3) : Fin 3 := 0-(a+b)

theorem remainingCrossingPart_ne_left {a b : Fin 3} (h : a ≠ b) :
    remainingCrossingPart a b ≠ a := by fin_cases a <;> fin_cases b <;> first | contradiction | decide

theorem remainingCrossingPart_ne_right {a b : Fin 3} (h : a ≠ b) :
    remainingCrossingPart a b ≠ b := by fin_cases a <;> fin_cases b <;> first | contradiction | decide

theorem remainingCrossingPart_unique {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    remainingCrossingPart a b = c := by fin_cases a <;> fin_cases b <;> fin_cases c <;> first | contradiction | decide

theorem card_prefixPart_filter_left (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (P : TripartiteVertex A B W → Prop) (Q : A → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ a, P (Sum.inl a) ↔ Q a) :
    ((prefixPartVertices S i 0).filter P).card = ((S.left i).filter Q).card := by
  have hEq : (prefixPartVertices S i 0).filter P =
      ((S.left i).filter Q).map (Function.Embedding.inl) := by
    ext z
    simp only [prefixPartVertices,mem_filter,mem_map]
    rcases z with a | (a | a) <;>
      simp [crossingPartTag,mem_vertices_left,h]
  rw [hEq,card_map]

theorem card_prefixPart_filter_right (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (P : TripartiteVertex A B W → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ a, P (Sum.inr (Sum.inl a)) ↔ Q a) :
    ((prefixPartVertices S i 1).filter P).card = ((S.right i).filter Q).card := by
  have hEq : (prefixPartVertices S i 1).filter P =
      ((S.right i).filter Q).map (Function.Embedding.inl.trans Function.Embedding.inr) := by
    ext z
    simp only [prefixPartVertices,mem_filter,mem_map]
    rcases z with a | (a | a) <;>
      simp [crossingPartTag,mem_vertices_right,h]
  rw [hEq,card_map]

theorem card_prefixPart_filter_color (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (P : TripartiteVertex A B W → Prop) (Q : W → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ a, P (Sum.inr (Sum.inr a)) ↔ Q a) :
    ((prefixPartVertices S i 2).filter P).card = ((S.colors i).filter Q).card := by
  have hEq : (prefixPartVertices S i 2).filter P =
      ((S.colors i).filter Q).map (Function.Embedding.inr.trans Function.Embedding.inr) := by
    ext z
    simp only [prefixPartVertices,mem_filter,mem_map]
    rcases z with a | (a | a) <;>
      simp [crossingPartTag,mem_vertices_color,h]
  rw [hEq,card_map]


/-- The two eligible target classes of an exterior vertex have (R2)'s
deterministic degree bounds. -/
theorem reserve_part_neighbor_card_bounds
    {S : NestedTripartitePrefixes A B W ρ m k l} {i : ℕ}
    {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop} {δ : ℝ}
    (hb : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hi : i+1 ≤ l) (hm : 0 < m)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4) (hInit : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hSmall : 32*δ ≤ ρ)
    (hHalf : 1/2 ≤ (k:ℝ)/m) (hK : (k:ℝ)/m ≤ 3/2)
    (x : TripartiteVertex A B W) (hx : x ∈ S.vertices i)
    (c : Fin 3) (hc : c ≠ crossingPartTag x) :
    let t : ℝ := ρ*nestedCoreSize ρ m i
    let N := (prefixPartVertices S (i+1) c).filter (tripartiteAdjacent F P Q x)
    15*t/32 ≤ (N.card : ℝ) ∧ (N.card : ℝ) ≤ 97*t/32 := by
  dsimp only
  let n : ℝ := nestedCoreSize ρ m i
  let s : ℝ := nestedCoreSize ρ m (i+1)
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hs₀ : 0 ≤ s := by dsimp only [s]; positivity
  obtain ⟨hs,hs',_⟩ := nested_crossing_core_window hρ hρsmall hInit
  change ρ*n ≤ s at hs
  change s ≤ 2*ρ*n at hs'
  have hL := mul_le_mul_of_nonneg_right hHalf hs₀
  have hU := mul_le_mul_of_nonneg_right hK hs₀
  have hSwap : s/m*k = ((k:ℝ)/m)*s := by ring
  have hCancel : s/m*m = s := div_mul_cancel₀ _ (by exact_mod_cast hm.ne')
  have hp₀ : ρ*n/2 ≤ s/m*k := by rw [hSwap]; linarith only [hs,hL]
  have hp₁ : s/m*k ≤ 3*ρ*n := by rw [hSwap]; linarith only [hs',hU]
  have hsLo : ρ*n/2 ≤ s/m*m := by rw [hCancel]; linarith only [hs,hInit]
  have hsHi : s/m*m ≤ 3*ρ*n := by rw [hCancel]; linarith only [hs',hInit]
  have hE := mul_le_mul_of_nonneg_right hSmall hn
  have hWindow {d g : ℝ} (hl : ρ*n/2 ≤ g) (hu : g ≤ 3*ρ*n) (he : |d-g| ≤ δ*n) :
      15*(ρ*n)/32 ≤ d ∧ d ≤ 97*(ρ*n)/32 := by
    obtain ⟨hl',hu'⟩ := abs_le.mp he
    exact ⟨by linarith only [hE,hl,hl'],by linarith only [hE,hu,hu']⟩
  rcases x with a | (b | w) <;> fin_cases c <;> try (exact False.elim (hc rfl))
  · erw [card_prefixPart_filter_right S (i+1) (tripartiteAdjacent F P Q (Sum.inl a)) (fun b => F a b)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hWindow hp₀ hp₁ (hb.leftRight 1 (by decide) hi a ((mem_vertices_left S i a).mp hx)).1
  · erw [card_prefixPart_filter_color S (i+1) (tripartiteAdjacent F P Q (Sum.inl a)) (fun w => P a w)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hWindow hp₀ hp₁ (hb.leftColors 1 (by decide) hi a ((mem_vertices_left S i a).mp hx)).1
  · erw [card_prefixPart_filter_left S (i+1) (tripartiteAdjacent F P Q (Sum.inr (Sum.inl b))) (fun a => F a b)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hWindow hp₀ hp₁ (hb.rightLeft 1 (by decide) hi b ((mem_vertices_right S i b).mp hx)).1
  · erw [card_prefixPart_filter_color S (i+1) (tripartiteAdjacent F P Q (Sum.inr (Sum.inl b))) (fun w => Q b w)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hWindow hp₀ hp₁ (hb.rightColors 1 (by decide) hi b ((mem_vertices_right S i b).mp hx)).1
  · erw [card_prefixPart_filter_left S (i+1) (tripartiteAdjacent F P Q (Sum.inr (Sum.inr w))) (fun a => P a w)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hWindow hsLo hsHi (hb.colorsLeft 1 (by decide) hi w ((mem_vertices_color S i w).mp hx)).1
  · erw [card_prefixPart_filter_right S (i+1) (tripartiteAdjacent F P Q (Sum.inr (Sum.inr w))) (fun b => Q b w)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hWindow hsLo hsHi (hb.colorsRight 1 (by decide) hi w ((mem_vertices_color S i w).mp hx)).1

/-- Property (R4), with its target class selected by the two vertices'
tags instead of an external case distinction. -/
theorem reserve_tagged_r4_margin
    {S : NestedTripartitePrefixes A B W ρ m k l} {i : ℕ}
    {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop} {δ η η₀ : ℝ}
    (hb : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hi : i+1 ≤ l) (hm : 0 < m)
    (hη₀ : 0 ≤ η₀) (hη₀small : η₀ ≤ 1/80) (hEta : 40*η₀ ≤ η)
    (hp : 1/2+η ≤ (k:ℝ)/m) (hBudget : 16*δ ≤ ρ) (hColor : 4*δ ≤ η*ρ)
    (u x : TripartiteVertex A B W) (hu : u ∈ S.vertices i) (hx : x ∈ S.vertices (i+1))
    (hne : crossingPartTag u ≠ crossingPartTag x) :
    let c := remainingCrossingPart (crossingPartTag u) (crossingPartTag x)
    let N := (prefixPartVertices S (i+1) c).filter (tripartiteAdjacent F P Q u)
    (1/2+20*η₀)*(N.card : ℝ) ≤ (N.filter (tripartiteAdjacent F P Q x)).card := by
  dsimp only
  let c := remainingCrossingPart (crossingPartTag u) (crossingPartTag x)
  let Z := prefixPartVertices S (i+1) c
  have hEq : (Z.filter (tripartiteAdjacent F P Q u)).filter (tripartiteAdjacent F P Q x) =
      Z.filter (fun z => tripartiteAdjacent F P Q u z ∧ tripartiteAdjacent F P Q x z) := by
    ext z
    simp only [mem_filter]
    tauto
  change (1/2+20*η₀)*((Z.filter (tripartiteAdjacent F P Q u)).card : ℝ) ≤
    ((Z.filter (tripartiteAdjacent F P Q u)).filter (tripartiteAdjacent F P Q x)).card
  rw [hEq]
  obtain ⟨hAB,hAW,hBA,hBW,hWA,hWB⟩ :=
    crossing_r4_candidate_margins hb hi hm hη₀ hη₀small hEta hp hBudget hColor
  rcases u with a | (b | w) <;> rcases x with a' | (b' | w') <;>
    try (exact False.elim (hne rfl))
  · have hc : c = 2 := by
      change remainingCrossingPart 0 1 = 2
      decide
    have hZ : Z = prefixPartVertices S (i+1) 2 := congrArg (prefixPartVertices S (i+1)) hc
    erw [hZ,card_prefixPart_filter_color S (i+1) (tripartiteAdjacent F P Q (Sum.inl a)) (fun w => P a w)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc]),
      card_prefixPart_filter_color S (i+1) (fun z => tripartiteAdjacent F P Q (Sum.inl a) z ∧ tripartiteAdjacent F P Q (Sum.inr (Sum.inl b')) z) (fun w => P a w ∧ Q b' w)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hAB a ((mem_vertices_left S _ _).mp hu) b' ((mem_vertices_right S _ _).mp hx)
  · have hc : c = 1 := by
      change remainingCrossingPart 0 2 = 1
      decide
    have hZ : Z = prefixPartVertices S (i+1) 1 := congrArg (prefixPartVertices S (i+1)) hc
    erw [hZ,card_prefixPart_filter_right S (i+1) (tripartiteAdjacent F P Q (Sum.inl a)) (fun b => F a b)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc]),
      card_prefixPart_filter_right S (i+1) (fun z => tripartiteAdjacent F P Q (Sum.inl a) z ∧ tripartiteAdjacent F P Q (Sum.inr (Sum.inr w')) z) (fun b => F a b ∧ Q b w')
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hAW a ((mem_vertices_left S _ _).mp hu) w' ((mem_vertices_color S _ _).mp hx)
  · have hc : c = 2 := by
      change remainingCrossingPart 1 0 = 2
      decide
    have hZ : Z = prefixPartVertices S (i+1) 2 := congrArg (prefixPartVertices S (i+1)) hc
    erw [hZ,card_prefixPart_filter_color S (i+1) (tripartiteAdjacent F P Q (Sum.inr (Sum.inl b))) (fun w => Q b w)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc]),
      card_prefixPart_filter_color S (i+1) (fun z => tripartiteAdjacent F P Q (Sum.inr (Sum.inl b)) z ∧ tripartiteAdjacent F P Q (Sum.inl a') z) (fun w => Q b w ∧ P a' w)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hBA b ((mem_vertices_right S _ _).mp hu) a' ((mem_vertices_left S _ _).mp hx)
  · have hc : c = 0 := by
      change remainingCrossingPart 1 2 = 0
      decide
    have hZ : Z = prefixPartVertices S (i+1) 0 := congrArg (prefixPartVertices S (i+1)) hc
    erw [hZ,card_prefixPart_filter_left S (i+1) (tripartiteAdjacent F P Q (Sum.inr (Sum.inl b))) (fun a => F a b)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc]),
      card_prefixPart_filter_left S (i+1) (fun z => tripartiteAdjacent F P Q (Sum.inr (Sum.inl b)) z ∧ tripartiteAdjacent F P Q (Sum.inr (Sum.inr w')) z) (fun a => F a b ∧ P a w')
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hBW b ((mem_vertices_right S _ _).mp hu) w' ((mem_vertices_color S _ _).mp hx)
  · have hc : c = 1 := by
      change remainingCrossingPart 2 0 = 1
      decide
    have hZ : Z = prefixPartVertices S (i+1) 1 := congrArg (prefixPartVertices S (i+1)) hc
    erw [hZ,card_prefixPart_filter_right S (i+1) (tripartiteAdjacent F P Q (Sum.inr (Sum.inr w))) (fun b => Q b w)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc]),
      card_prefixPart_filter_right S (i+1) (fun z => tripartiteAdjacent F P Q (Sum.inr (Sum.inr w)) z ∧ tripartiteAdjacent F P Q (Sum.inl a') z) (fun b => Q b w ∧ F a' b)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hWA w ((mem_vertices_color S _ _).mp hu) a' ((mem_vertices_left S _ _).mp hx)
  · have hc : c = 0 := by
      change remainingCrossingPart 2 1 = 0
      decide
    have hZ : Z = prefixPartVertices S (i+1) 0 := congrArg (prefixPartVertices S (i+1)) hc
    erw [hZ,card_prefixPart_filter_left S (i+1) (tripartiteAdjacent F P Q (Sum.inr (Sum.inr w))) (fun a => P a w)
      (by intro z; simp [tripartiteAdjacent,tripartiteArc]),
      card_prefixPart_filter_left S (i+1) (fun z => tripartiteAdjacent F P Q (Sum.inr (Sum.inr w)) z ∧ tripartiteAdjacent F P Q (Sum.inr (Sum.inl b')) z) (fun a => P a w ∧ F a b')
      (by intro z; simp [tripartiteAdjacent,tripartiteArc])]
    exact hWB w ((mem_vertices_color S _ _).mp hu) b' ((mem_vertices_right S _ _).mp hx)

end OverfullWork.ChenShan
