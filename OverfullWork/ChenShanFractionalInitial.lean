module

public import OverfullWork.ChenShanFractionalCorrection

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical BigOperators

universe uA uB uW

variable {A : Type uA} {B : Type uB} {W : Type uW}
variable {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}

noncomputable def edgeOnes (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop) :
    TripartiteEdgeWeights A B W :=
  ⟨fun a b => if E a b then 1 else 0, fun a w => if L a w then 1 else 0,
   fun b w => if R b w then 1 else 0⟩

theorem edgeOnes_supported : (edgeOnes E L R).Supported E L R := by
  exact ⟨fun a b h => by simp [edgeOnes,h],fun a w h => by simp [edgeOnes,h],
    fun b w h => by simp [edgeOnes,h]⟩

noncomputable def initialTriangleWeights [Fintype W] (E : A → B → Prop)
    (L : A → W → Prop) (R : B → W → Prop) (a : A) (b : B) (w : W) : ℝ :=
  if E a b ∧ L a w ∧ R b w then 1/(Fintype.card W : ℝ) else 0

theorem initialTriangleWeights_supported [Fintype W] :
    TriangleSupported E L R (initialTriangleWeights E L R) := by
  intro a b w h
  simp [initialTriangleWeights,h]

private theorem sum_const_on_support {V : Type*} [Fintype V] (P : V → Prop) [DecidablePred P] (c : ℝ) :
    (∑ v, if P v then c else 0) = (#(univ.filter P) : ℝ)*c := by
  rw [← sum_filter,sum_const,nsmul_eq_mul]

variable [Fintype A] [Fintype B] [Fintype W]

theorem edgeOnes_balanced (h : TripartiteLocallyBalanced E L R) :
    (edgeOnes E L R).Balanced := by
  have hCountsA (a : A) : #(univ.filter (E a)) = #(univ.filter (L a)) := by
    simpa only [Fintype.card_subtype] using h.1 a
  have hCountsB (b : B) : #(univ.filter (fun a => E a b)) = #(univ.filter (R b)) := by
    simpa only [Fintype.card_subtype] using h.2.1 b
  have hCountsW (w : W) : #(univ.filter (fun a => L a w)) = #(univ.filter (fun b => R b w)) := by
    simpa only [Fintype.card_subtype] using h.2.2 w
  exact ⟨fun a => by simp only [edgeOnes,sum_const_on_support,hCountsA a],
    fun b => by simp only [edgeOnes,sum_const_on_support,hCountsB b],
    fun w => by simp only [edgeOnes,sum_const_on_support,hCountsW w]⟩

private theorem card_filter_plus_missing {V : Type*} [Fintype V] (P : V → Prop)
    [DecidablePred P] [(v : V) → Decidable (¬ P v)] :
    (#(univ.filter P) : ℝ) + (#(univ.filter (fun v => ¬ P v)) : ℝ) =
      (Fintype.card V : ℝ) := by
  exact_mod_cast (card_filter_add_card_filter_not (s := (univ : Finset V)) P).trans card_univ

private theorem card_filter_inter_le {V : Type*} [Fintype V] (P Q : V → Prop) :
    (#(univ.filter (fun v => P v ∧ Q v)) : ℝ) ≤ (#(univ.filter P) : ℝ) := by
  exact_mod_cast (card_le_card (fun _ hv => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2.1⟩) :
    #(univ.filter (fun v => P v ∧ Q v)) ≤ #(univ.filter P))

private theorem card_filter_inter_loss {V : Type*} [Fintype V] (P Q : V → Prop) :
    (#(univ.filter P) : ℝ) ≤ (#(univ.filter (fun v => P v ∧ Q v)) : ℝ) +
      (#(univ.filter (fun v => ¬ Q v)) : ℝ) := by
  exact_mod_cast card_filter_le_inter_add_missing P Q

private theorem initial_defect_le {k m ε c : ℝ}
    (hk : 0 < k) (hkm : m/2 ≤ k) (hε : 0 ≤ ε)
    (hLow : k-2*ε*m ≤ c) (hHigh : c ≤ k) :
    |1-c/k| ≤ 4*ε := by
  have hOne : c/k ≤ 1 := (div_le_iff₀ hk).mpr (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr hOne)]
  have hComp : k-c ≤ 4*ε*k := by
    have h := mul_le_mul_of_nonneg_left hkm (show 0 ≤ 4*ε by positivity)
    linarith
  have hEq : 1-c/k = (k-c)/k := by rw [sub_div,div_self (ne_of_gt hk)]
  rw [hEq,div_le_iff₀ hk]
  exact hComp

/-- The uniform starting assignment of Lemma 4.8 misses every edge
by at most 4ε. -/
theorem initial_triangle_residual_bounded {m : ℕ} {η ε : ℝ}
    (h : DenseTripartite E L R m η ε) (hm : 0 < m)
    (hη : 0 < η) (hηhalf : η < 1/2) (hε₀ : 0 ≤ ε) (hε : ε ≤ η) :
    ((edgeOnes E L R).sub (triangleBoundary (initialTriangleWeights E L R))).Bounded (4*ε) := by
  let k := (Fintype.card W : ℝ)
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hkm : (m : ℝ)/2 ≤ k := (h.color_count_bounds hm hη hηhalf hε).1
  have hk : 0 < k := by linarith
  have hCountsA (a : A) : (#(univ.filter (E a)) : ℝ) = (#(univ.filter (L a)) : ℝ) := by
    exact_mod_cast (show #(univ.filter (E a)) = #(univ.filter (L a)) by
      simpa only [Fintype.card_subtype] using h.balanced.1 a)
  have hCountsB (b : B) : (#(univ.filter (fun a => E a b)) : ℝ) = (#(univ.filter (R b)) : ℝ) := by
    exact_mod_cast (show #(univ.filter (fun a => E a b)) = #(univ.filter (R b)) by
      simpa only [Fintype.card_subtype] using h.balanced.2.1 b)
  have hSupport := triangleBoundary_supported (initialTriangleWeights_supported (E := E) (L := L) (R := R))
  have hZero := edgeOnes_supported.sub hSupport
  refine ⟨?_,?_,?_⟩
  · intro a b
    by_cases he : E a b
    · dsimp only [TripartiteEdgeWeights.sub,edgeOnes,triangleBoundary,initialTriangleWeights]
      simp only [he,true_and,ite_true,sum_const_on_support]
      rw [mul_one_div]
      apply initial_defect_le hk hkm hε₀
      · have hC : (#(univ.filter (fun w => ¬ (L a w ∧ R b w))) : ℝ) ≤
            (#(univ.filter (fun w => ¬ L a w)) : ℝ) + (#(univ.filter (fun w => ¬ R b w)) : ℝ) := by
          exact_mod_cast card_missing_conjunction_le (L a) (R b)
        linarith [card_filter_plus_missing (fun w => L a w ∧ R b w),h.missingAW a,h.missingBW b]
      · dsimp only [k]
        exact_mod_cast (card_filter_le (univ : Finset W) (fun w => L a w ∧ R b w)).trans_eq card_univ
    · rw [hZero.1 a b he,abs_zero]
      positivity
  · intro a w
    by_cases ha : L a w
    · dsimp only [TripartiteEdgeWeights.sub,edgeOnes,triangleBoundary,initialTriangleWeights]
      simp only [ha,true_and,ite_true,sum_const_on_support]
      rw [mul_one_div]
      apply initial_defect_le hk hkm hε₀
      · linarith [card_filter_inter_loss (E a) (fun b => R b w),
          hCountsA a,card_filter_plus_missing (L a),h.missingAW a,h.missingWB w]
      · have hh : (#(univ.filter (L a)) : ℝ) ≤ k := by
          dsimp only [k]
          exact_mod_cast (card_filter_le (univ : Finset W) (L a)).trans_eq card_univ
        exact (card_filter_inter_le (E a) (fun b => R b w)).trans ((hCountsA a).trans_le hh)
    · rw [hZero.2.1 a w ha,abs_zero]
      positivity
  · intro b w
    by_cases hb : R b w
    · dsimp only [TripartiteEdgeWeights.sub,edgeOnes,triangleBoundary,initialTriangleWeights]
      simp only [hb,and_true,ite_true,sum_const_on_support]
      rw [mul_one_div]
      apply initial_defect_le hk hkm hε₀
      · linarith [card_filter_inter_loss (fun a => E a b) (fun a => L a w),
          hCountsB b,card_filter_plus_missing (R b),h.missingBW b,h.missingWA w]
      · have hh : (#(univ.filter (R b)) : ℝ) ≤ k := by
          dsimp only [k]
          exact_mod_cast (card_filter_le (univ : Finset W) (R b)).trans_eq card_univ
        exact (card_filter_inter_le (fun a => E a b) (fun a => L a w)).trans ((hCountsB b).trans_le hh)
    · rw [hZero.2.2 b w hb,abs_zero]
      positivity

end OverfullWork.ChenShan
