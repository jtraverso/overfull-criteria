module

public import OverfullWork.ChenShanResidualPrefixDegrees
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

private theorem ambient_degree_error {V : Type*} [Fintype V] (P : V → Prop) {q m : ℕ}
    {ε : ℝ} (hQ : Fintype.card V = q)
    (hMiss : ((univ.filter fun v => ¬ P v).card : ℝ) ≤ ε*m) :
    |((univ.filter P).card : ℝ)-q| ≤ ε*m := by
  have hCard := card_filter_add_card_filter_not (s := (univ : Finset V)) P
  rw [card_univ,hQ] at hCard
  have hCardR : ((univ.filter P).card : ℝ)+((univ.filter fun v => ¬ P v).card : ℝ) = q := by
    exact_mod_cast hCard
  have hNonneg := Nat.cast_nonneg (α := ℝ) ((univ.filter fun v => ¬ P v).card)
  rw [abs_of_nonpos (by linarith only [hCardR,hNonneg])]
  linarith only [hCardR,hMiss]

private theorem left_mem_vertices (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (a : A) (ha : a ∈ S.left i) : (Sum.inl a) ∈ S.vertices i :=
  mem_union_left _ (mem_union_left _ (mem_map.mpr ⟨a,ha,rfl⟩))

private theorem right_mem_vertices (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (b : B) (hb : b ∈ S.right i) : (Sum.inr (Sum.inl b)) ∈ S.vertices i :=
  mem_union_left _ (mem_union_right _ (mem_map.mpr ⟨b,hb,rfl⟩))

private theorem color_mem_vertices (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (w : W) (hw : w ∈ S.colors i) : (Sum.inr (Sum.inr w)) ∈ S.vertices i :=
  mem_union_right _ (mem_map.mpr ⟨w,hw,rfl⟩)

private def outgoingArc {Y V : Type*} (x : V) (f : Y ↪ V) : Y ↪ (V × V) :=
  ⟨fun y => (x,f y),fun _ _ e => f.injective (congrArg Prod.snd e)⟩

private def incomingArc {Y V : Type*} (x : V) (f : Y ↪ V) : Y ↪ (V × V) :=
  ⟨fun y => (f y,x),fun _ _ e => f.injective (congrArg Prod.fst e)⟩

/-- The neighborhood estimates at the current and the next retained level.
When the center is also the target size up to rounding, the second estimate
bounds the number of nonneighbors. -/
def ResidualPrefixPairBounds {X Y : Type*}
    (F : X → Y → Prop) (source : Finset X) (target : ℕ → Finset Y)
    (ρ : ℝ) (m i l D : ℕ) (budget : ℝ) : Prop :=
  ∀ t ≤ 1, i+t ≤ l → ∀ v ∈ source,
    let center := ((nestedCoreSize ρ m (i+t) : ℝ)/m)*D
    |(((target (i+t)).filter (F v)).card : ℝ)-center| ≤ budget ∧
    (|(((target (i+t)).card : ℝ))-center| ≤ 1/2 →
      (((target (i+t)).filter (fun w => ¬F v w)).card : ℝ) ≤ budget)

structure TripartiteResidualPrefixBounds
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (budget : ℝ) : Prop where
  leftRight : ResidualPrefixPairBounds F (S.left i) S.right ρ m i l k budget
  rightLeft : ResidualPrefixPairBounds (fun b a => F a b) (S.right i) S.left ρ m i l k budget
  leftColors : ResidualPrefixPairBounds P (S.left i) S.colors ρ m i l k budget
  rightColors : ResidualPrefixPairBounds Q (S.right i) S.colors ρ m i l k budget
  colorsLeft : ResidualPrefixPairBounds (fun w a => P a w) (S.colors i) S.left ρ m i l m budget
  colorsRight : ResidualPrefixPairBounds (fun w b => Q b w) (S.colors i) S.right ρ m i l m budget

/-- Edges of the original graph inside the current prefix that are
absent from the residual graph. -/
noncomputable def prefixLostArcs {V : Type*} (G H : Finset (V × V)) (U : Finset V) :
    Finset (V × V) :=
  (G ∩ (U ×ˢ U)) \ H

private theorem residual_pair_bounds_of_arc_encoding
    {X Y V : Type*} [Fintype Y]
    (E F : X → Y → Prop) (S : ℕ → Finset X) (T : ℕ → Finset Y)
    (ρ : ℝ) (m i l D : ℕ) (ε ξ β : ℝ)
    (G H : Finset (V × V)) (U : Finset V) (src : X → V) (edge : X → Y ↪ (V × V))
    (hm : 0 < m) (hρ : ρ ≤ 1) (hi : i ≤ l)
    (hε : 0 ≤ ε) (hξ : 0 ≤ ξ) (hHalf : 1/2 ≤ ξ*nestedCoreSize ρ m i)
    (hSample : PrefixDegreeControl E S T (nestedCoreSize ρ m) l ξ)
    (hAmbient : ∀ v, |((univ.filter (E v)).card : ℝ)-D| ≤ ε*m)
    (hMean : ∀ j ≤ l, ∀ v,
      |(((T j).card : ℝ)/Fintype.card Y)*((univ.filter (E v)).card : ℝ) -
        ((nestedCoreSize ρ m j : ℝ)/m)*((univ.filter (E v)).card : ℝ)| ≤ 1/2)
    (hIncident : ∀ v w, (edge v w).1 = src v ∨ (edge v w).2 = src v)
    (hInside : ∀ j, i ≤ j → ∀ v ∈ S i, ∀ w ∈ T j, edge v w ∈ U ×ˢ U)
    (hG : ∀ v w, edge v w ∈ G ↔ E v w)
    (hH : ∀ v w, edge v w ∈ H ↔ F v w)
    (hSub : H ⊆ G)
    (hBudget : ∀ v, (incidentDegree (prefixLostArcs G H U) v : ℝ) ≤ β*nestedCoreSize ρ m i) :
    ResidualPrefixPairBounds F (S i) T ρ m i l D ((4*ε+10*ξ+β)*nestedCoreSize ρ m i) := by
  intro t ht hEnd v hv
  have hLevels : i ≤ i+t := Nat.le_add_right _ _
  have hSizes := (antitone_nat_of_succ_le (nestedCoreSize_monotone_down ρ hρ m)) hLevels
  apply residual_prefix_pair_degrees E F v (T (i+t)) D m (nestedCoreSize ρ m i)
    (nestedCoreSize ρ m (i+t)) ε ξ β (prefixLostArcs G H U) (src v) (edge v)
    hm hSizes hε hξ hHalf (hAmbient v) (hMean _ hEnd v)
    (hSample i hi t (by omega) hEnd v hv)
  · intro w _ hw
    exact (hG v w).mp (hSub ((hH v w).mpr hw))
  · exact hIncident v
  · intro w hw hwE hwF
    unfold prefixLostArcs
    exact mem_sdiff.mpr ⟨mem_inter.mpr ⟨(hG v w).mpr hwE,hInside _ hLevels v hv w hw⟩,
      fun h => hwF ((hH v w).mp h)⟩
  · exact hBudget (src v)

private theorem core_prefix_mean_error
    {X Y : Type*} [Fintype Y] (E : X → Y → Prop) (T : ℕ → Finset Y)
    (hY : Fintype.card Y = m) (hT : ∀ j ≤ l, (T j).card = nestedCoreSize ρ m j)
    (j : ℕ) (hj : j ≤ l) (v : X) :
    |(((T j).card : ℝ)/Fintype.card Y)*((univ.filter (E v)).card : ℝ) -
      ((nestedCoreSize ρ m j : ℝ)/m)*((univ.filter (E v)).card : ℝ)| ≤ 1/2 := by
  rw [hY,hT j hj,sub_self,abs_zero]
  norm_num

private theorem color_prefix_mean_error
    {X : Type*} (E : X → W → Prop) (T : ℕ → Finset W)
    (hW : Fintype.card W = k) (hm : 0 < m) (hk : 0 < k)
    (hT : ∀ j ≤ l, (T j).card = nestedColorSize ((k:ℝ)/m) (nestedCoreSize ρ m j))
    (j : ℕ) (hj : j ≤ l) (v : X) :
    |(((T j).card : ℝ)/Fintype.card W)*((univ.filter (E v)).card : ℝ) -
      ((nestedCoreSize ρ m j : ℝ)/m)*((univ.filter (E v)).card : ℝ)| ≤ 1/2 := by
  rw [hW,hT j hj]
  exact color_rounding_degree_gap hm hk _ (Nat.cast_nonneg _)
    (by exact_mod_cast (card_le_univ (univ.filter (E v))).trans_eq hW)

/-- Equation (4.23) at the current and next retained levels, from
(4.9), (4.20), and the deletion budget of (4.22). -/
theorem tripartite_residual_prefix_degrees
    {E F : A → B → Prop} {L P : A → W → Prop} {R Q : B → W → Prop}
    {η ε ξ β : ℝ}
    (G : DenseTripartite E L R m η ε) (S : NestedTripartitePrefixes A B W ρ m k l)
    (hm : 0 < m) (hk : 0 < k) (hW : Fintype.card W = k)
    (hρ : ρ ≤ 1) (hε : 0 ≤ ε) (hξ : 0 ≤ ξ)
    (hSample : TripartitePrefixDegreeControl E L R S ξ)
    (i : ℕ) (hi : i ≤ l) (hHalf : 1/2 ≤ ξ*nestedCoreSize ρ m i)
    (hSub : tripartiteArcs F P Q ⊆ tripartiteArcs E L R)
    (hBudget : ∀ v, (incidentDegree
      (prefixLostArcs (tripartiteArcs E L R) (tripartiteArcs F P Q) (S.vertices i)) v : ℝ)
      ≤ β*nestedCoreSize ρ m i) :
    TripartiteResidualPrefixBounds F P Q S i ((4*ε+10*ξ+β)*nestedCoreSize ρ m i) := by
  let orig := tripartiteArcs E L R
  let kept := tripartiteArcs F P Q
  let U := S.vertices i
  let fa : A ↪ TripartiteVertex A B W := Function.Embedding.inl
  let fb : B ↪ TripartiteVertex A B W :=
    Function.Embedding.inl.trans Function.Embedding.inr
  let fw : W ↪ TripartiteVertex A B W :=
    Function.Embedding.inr.trans Function.Embedding.inr
  have hAW (a : A) := ambient_degree_error (L a) hW (G.missingAW a)
  have hBW (b : B) := ambient_degree_error (R b) hW (G.missingBW b)
  have hWA (w : W) := ambient_degree_error (fun a => L a w) G.sizeA (G.missingWA w)
  have hWB (w : W) := ambient_degree_error (fun b => R b w) G.sizeB (G.missingWB w)
  have hAB (a : A) : |((univ.filter (E a)).card : ℝ)-k| ≤ ε*m := by
    have hEq := G.balanced.1 a
    rw [Fintype.card_subtype,Fintype.card_subtype] at hEq
    simpa only [hEq] using hAW a
  have hBA (b : B) : |((univ.filter (fun a => E a b)).card : ℝ)-k| ≤ ε*m := by
    have hEq := G.balanced.2.1 b
    rw [Fintype.card_subtype,Fintype.card_subtype] at hEq
    simpa only [hEq] using hBW b
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · refine residual_pair_bounds_of_arc_encoding E F S.left S.right
      ρ m i l k ε ξ β orig kept U fa (fun a => outgoingArc (fa a) fb)
      hm hρ hi hε hξ hHalf hSample.leftRight hAB
      (core_prefix_mean_error E S.right G.sizeB S.rightSize)
      (fun _ _ => Or.inl rfl) ?_ ?_ ?_ hSub hBudget
    · intro j hj a ha b hb
      exact mem_product.mpr ⟨left_mem_vertices S i a ha,
        right_mem_vertices S i b (S.rightAntitone hj hb)⟩
    · intro a b
      simp [orig,outgoingArc,fa,fb,tripartiteArc]
    · intro a b
      simp [kept,outgoingArc,fa,fb,tripartiteArc]
  · refine residual_pair_bounds_of_arc_encoding (fun b a => E a b) (fun b a => F a b) S.right S.left
      ρ m i l k ε ξ β orig kept U fb (fun b => incomingArc (fb b) fa)
      hm hρ hi hε hξ hHalf hSample.rightLeft hBA
      (core_prefix_mean_error (fun b a => E a b) S.left G.sizeA S.leftSize)
      (fun _ _ => Or.inr rfl) ?_ ?_ ?_ hSub hBudget
    · intro j hj b hb a ha
      exact mem_product.mpr ⟨left_mem_vertices S i a (S.leftAntitone hj ha),
        right_mem_vertices S i b hb⟩
    · intro b a
      simp [orig,incomingArc,fb,fa,tripartiteArc]
    · intro b a
      simp [kept,incomingArc,fb,fa,tripartiteArc]
  · refine residual_pair_bounds_of_arc_encoding L P S.left S.colors
      ρ m i l k ε ξ β orig kept U fa (fun a => incomingArc (fa a) fw)
      hm hρ hi hε hξ hHalf hSample.leftColors hAW
      (color_prefix_mean_error L S.colors hW hm hk S.colorsSize)
      (fun _ _ => Or.inr rfl) ?_ ?_ ?_ hSub hBudget
    · intro j hj a ha w hw
      exact mem_product.mpr ⟨color_mem_vertices S i w (S.colorsAntitone hj hw),
        left_mem_vertices S i a ha⟩
    · intro a w
      simp [orig,incomingArc,fa,fw,tripartiteArc]
    · intro a w
      simp [kept,incomingArc,fa,fw,tripartiteArc]
  · refine residual_pair_bounds_of_arc_encoding R Q S.right S.colors
      ρ m i l k ε ξ β orig kept U fb (fun b => outgoingArc (fb b) fw)
      hm hρ hi hε hξ hHalf hSample.rightColors hBW
      (color_prefix_mean_error R S.colors hW hm hk S.colorsSize)
      (fun _ _ => Or.inl rfl) ?_ ?_ ?_ hSub hBudget
    · intro j hj b hb w hw
      exact mem_product.mpr ⟨right_mem_vertices S i b hb,
        color_mem_vertices S i w (S.colorsAntitone hj hw)⟩
    · intro b w
      simp [orig,outgoingArc,fb,fw,tripartiteArc]
    · intro b w
      simp [kept,outgoingArc,fb,fw,tripartiteArc]
  · refine residual_pair_bounds_of_arc_encoding (fun w a => L a w) (fun w a => P a w) S.colors S.left
      ρ m i l m ε ξ β orig kept U fw (fun w => outgoingArc (fw w) fa)
      hm hρ hi hε hξ hHalf hSample.colorsLeft hWA
      (core_prefix_mean_error (fun w a => L a w) S.left G.sizeA S.leftSize)
      (fun _ _ => Or.inl rfl) ?_ ?_ ?_ hSub hBudget
    · intro j hj w hw a ha
      exact mem_product.mpr ⟨color_mem_vertices S i w hw,
        left_mem_vertices S i a (S.leftAntitone hj ha)⟩
    · intro w a
      simp [orig,outgoingArc,fw,fa,tripartiteArc]
    · intro w a
      simp [kept,outgoingArc,fw,fa,tripartiteArc]
  · refine residual_pair_bounds_of_arc_encoding (fun w b => R b w) (fun w b => Q b w) S.colors S.right
      ρ m i l m ε ξ β orig kept U fw (fun w => incomingArc (fw w) fb)
      hm hρ hi hε hξ hHalf hSample.colorsRight hWB
      (core_prefix_mean_error (fun w b => R b w) S.right G.sizeB S.rightSize)
      (fun _ _ => Or.inr rfl) ?_ ?_ ?_ hSub hBudget
    · intro j hj w hw b hb
      exact mem_product.mpr ⟨right_mem_vertices S i b (S.rightAntitone hj hb),
        color_mem_vertices S i w hw⟩
    · intro w b
      simp [orig,incomingArc,fw,fb,tripartiteArc]
    · intro w b
      simp [kept,incomingArc,fw,fb,tripartiteArc]

end OverfullWork.ChenShan
