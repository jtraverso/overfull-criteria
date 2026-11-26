module

public import OverfullWork.ChenShanNestedDegreeControl
public import OverfullWork.ChenShanUniversalAbsorber
public import OverfullWork.ChenShanFractionalCorrection
public import OverfullWork.ChenShanDenseTripartiteDegree
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

noncomputable def NestedTripartitePrefixes.vertices
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) :
    Finset (TripartiteVertex A B W) :=
  (S.left i).map (Function.Embedding.inl) ∪
    (S.right i).map ((Function.Embedding.inl).trans (Function.Embedding.inr)) ∪
    (S.colors i).map ((Function.Embedding.inr).trans (Function.Embedding.inr))

theorem NestedTripartitePrefixes.vertices_antitone
    (S : NestedTripartitePrefixes A B W ρ m k l) : Antitone S.vertices := by
  intro i j hij
  unfold NestedTripartitePrefixes.vertices
  exact union_subset_union
    (union_subset_union (map_subset_map.mpr (S.leftAntitone hij))
      (map_subset_map.mpr (S.rightAntitone hij)))
    (map_subset_map.mpr (S.colorsAntitone hij))

theorem NestedTripartitePrefixes.vertices_card_le
    (S : NestedTripartitePrefixes A B W ρ m k l)
    (hm : 0 < m) (hk : (k : ℝ) ≤ (3/2)*(m : ℝ))
    (i : ℕ) (hi : i ≤ l) (hs : 1 ≤ nestedCoreSize ρ m i) :
    (S.vertices i).card ≤ 4*nestedCoreSize ρ m i := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hRatio : (k:ℝ)/m ≤ 3/2 := (div_le_iff₀ hmR).mpr hk
  have hRound := (abs_le.mp (nestedColorSize_error ((k:ℝ)/m) (by positivity)
    (nestedCoreSize ρ m i))).2
  have hProd := mul_le_mul_of_nonneg_right hRatio
    (Nat.cast_nonneg (α := ℝ) (nestedCoreSize ρ m i))
  have hsR : (1:ℝ) ≤ nestedCoreSize ρ m i := by exact_mod_cast hs
  have hColorR : (nestedColorSize ((k:ℝ)/m) (nestedCoreSize ρ m i) : ℝ)
      ≤ 2*(nestedCoreSize ρ m i : ℝ) := by linarith only [hRound,hProd,hsR]
  have hColor : (S.colors i).card ≤ 2*nestedCoreSize ρ m i := by
    rw [S.colorsSize i hi]
    exact_mod_cast hColorR
  unfold NestedTripartitePrefixes.vertices
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
  rw [card_map,card_map,card_map,S.leftSize i hi,S.rightSize i hi]
  omega

private theorem color_count_le_of_small_missing
    {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}
    {η ε : ℝ} (G : DenseTripartite E L R m η ε) (hm : 0 < m) (hε : ε ≤ 1/2) :
    (Fintype.card W : ℝ) ≤ (3/2)*(m : ℝ) := by
  have hA : 0 < Fintype.card A := G.sizeA.symm ▸ hm
  let a : A := Classical.choice (Fintype.card_pos_iff.mp hA)
  have hDeg : (univ.filter (E a)).card = (univ.filter (L a)).card := by
    simpa only [Fintype.card_subtype] using G.balanced.1 a
  have hLeft : ((univ.filter (L a)).card : ℝ) ≤ m := by
    rw [← hDeg]
    exact_mod_cast (card_le_univ (univ.filter (E a))).trans G.sizeB.le
  have hTot := card_filter_add_card_filter_not (s := (univ : Finset W)) (L a)
  rw [card_univ] at hTot
  have hTotR : ((univ.filter (L a)).card : ℝ) +
      ((univ.filter (fun w => ¬L a w)).card : ℝ) = Fintype.card W := by exact_mod_cast hTot
  have hMiss := G.missingAW a
  have hεm := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) m)
  linarith only [hLeft,hTotR,hMiss,hεm]

private theorem incidentDegree_le_card {V : Type*} (G : Finset (V × V)) (v : V) :
    incidentDegree G v ≤ G.card := by
  unfold incidentDegree
  exact card_filter_le _ _

/-- The absorber at the end of Step 1 of Theorem 4.15, with explicit
size conditions for the initial core. -/
theorem exists_absorber_for_nested_prefixes
    {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}
    {η ε μ : ℝ} {h H : ℕ} (G : DenseTripartite E L R m η ε)
    (S : NestedTripartitePrefixes A B W ρ m k l)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ min η (1/2)/128)
    (hη : 0 < η) (hηhalf : η < 1/2) (hε : 0 ≤ ε) (hεsmall : ε ≤ η/32)
    (hCycles : (H : ℝ)*ε ≤ 1/32) (hm : 0 < m)
    (hScale : (h : ℝ)/ρ ≤ m) (hLarge : 128/min η (1/2) ≤ (m : ℝ))
    (hH : 4*(h : ℝ)/ρ ≤ H) (hk : Fintype.card W = k)
    (hKeep : ∀ i ≤ l, h ≤ nestedCoreSize ρ m i) (hh : 1 ≤ h)
    (hExit : nestedCoreSize ρ m (l+1) < h) (hTop : (nestedCoreSize ρ m l : ℝ) < h/ρ)
    (hRoom : ((4*(H*H)*2^(H*H) : ℕ) : ℝ) ≤ min η (1/2)*m/16)
    (hBudget : ((4*(H*H)*2^(H*H) : ℕ) : ℝ) ≤ μ*m) :
    ∃ (P : A → B → Prop) (Q : A → W → Prop) (T : B → W → Prop),
      tripartiteArcs P Q T ⊆ tripartiteArcs E L R ∧
      Disjoint (tripartiteArcs P Q T) (S.vertices 1 ×ˢ S.vertices 1) ∧
      (∀ v, (incidentDegree (tripartiteArcs P Q T) v : ℝ) ≤ μ*m) ∧
      Nonempty (TripartiteTriangleDecomposition P Q T) ∧
      ∀ (EL : A → B → Prop) (LL : A → W → Prop) (RL : B → W → Prop),
        tripartiteArcs EL LL RL ⊆ tripartiteArcs E L R →
        tripartiteArcs EL LL RL ⊆ S.vertices l ×ˢ S.vertices l →
        TripartiteLocallyBalanced EL LL RL →
        Nonempty (TripartiteTriangleDecomposition
          (fun a b => P a b ∨ EL a b) (fun a w => Q a w ∨ LL a w)
          (fun b w => T b w ∨ RL b w)) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hOne : 1 ≤ l := by
    by_contra! hZero
    have hZero' : l = 0 := by omega
    subst l
    have hFirst : ρ*(m : ℝ) ≤ nestedCoreSize ρ m 1 := nestedCoreSize_step_lower ρ m 0
    have hBelow : (nestedCoreSize ρ m 1 : ℝ) < h := by exact_mod_cast hExit
    have hAbove := (div_le_iff₀ hρ).mp hScale
    linarith only [hFirst,hBelow,hAbove]
  have hεη : ε ≤ η := by linarith only [hεsmall,hη]
  have hkLarge : (1/2)*(m : ℝ) ≤ Fintype.card W := by
    linarith only [(G.color_count_bounds hm hη hηhalf hεη).1]
  have hkSmall : (k : ℝ) ≤ (3/2)*(m : ℝ) := by
    have hhW := color_count_le_of_small_missing G hm (by linarith only [hεsmall,hηhalf])
    simpa only [hk] using hhW
  have hCard (i : ℕ) (hi : i ≤ l) : ((S.vertices i).card : ℝ) ≤ 4*nestedCoreSize ρ m i := by
    exact_mod_cast S.vertices_card_le hm hkSmall i hi (hh.trans (hKeep i hi))
  have hFinal : (S.vertices l).card ≤ H := by
    have hFinalR : ((S.vertices l).card : ℝ) ≤ H := by
      have hTop' : 4*(nestedCoreSize ρ m l : ℝ) < 4*(h:ℝ)/ρ := by
        rw [mul_div_assoc]
        linarith only [hTop]
      exact (hCard l le_rfl).trans (hTop'.le.trans hH)
    exact_mod_cast hFinalR
  have hGap : 0 < min η (1/2) := lt_min hη (by norm_num)
  have hFirstUpper : (nestedCoreSize ρ m 1 : ℝ) < ρ*(m:ℝ)+1 :=
    nestedCoreSize_step_upper ρ hρ.le m 0
  have hExcluded : ((S.vertices 1).card : ℝ) ≤ min η (1/2)*m/16 := by
    have hLarge' := (div_le_iff₀ hGap).mp hLarge
    have hρm := mul_le_mul_of_nonneg_right hρsmall hmR.le
    linarith only [hCard 1 hOne,hFirstUpper,hLarge',hρm]
  have hSizeA : (Fintype.card A : ℝ) = m := by exact_mod_cast G.sizeA
  obtain ⟨aux,P,Q,T,hAux,hSub,hFoot,hTotal,hDecomp,hAbsorb⟩ :=
    exists_universal_tripartite_absorber E L R (S.vertices l) (S.vertices 1) H
      (m:ℝ) η (1/2) ε hmR hη (by norm_num) hSizeA hkLarge
      G.degreeA G.degreeB G.missingAW G.missingBW G.missingWA G.missingWB
      hε hεsmall (by linarith only [hCycles]) (S.vertices_antitone hOne) hFinal hExcluded hRoom
  refine ⟨P,Q,T,hSub,?_,?_,hDecomp,hAbsorb⟩
  · refine disjoint_left.mpr fun e he hInside => ?_
    have hEnds := mem_product.mp hInside
    rcases hFoot e he with ⟨hLeft,_⟩ | ⟨hRight,_⟩
    · exact disjoint_left.mp hAux hLeft hEnds.1
    · exact disjoint_left.mp hAux hRight hEnds.2
  · intro v
    have hInc : incidentDegree (tripartiteArcs P Q T) v ≤ (tripartiteArcs P Q T).card :=
      incidentDegree_le_card _ _
    have hBound : incidentDegree (tripartiteArcs P Q T) v ≤ 4*(H*H)*2^(H*H) := by omega
    exact (show (incidentDegree (tripartiteArcs P Q T) v : ℝ) ≤
      ((4*(H*H)*2^(H*H) : ℕ) : ℝ) by exact_mod_cast hBound).trans hBudget

end OverfullWork.ChenShan
