module

public import OverfullWork.OsthusStadenGoodVertices

@[expose] public section


/-! Restrict each directed copy to the retained vertices on its two
sides. Both its regularity and its marked semidegrees survive the trim. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion
open scoped Classical
variable {W X : Type*}

def pullDirectedPair (a b : X ↪ W) (D : Digraph W) : Digraph X :=
  ⟨fun x y => D.Adj (a x) (b y)⟩

variable [Fintype W] [Fintype X]

theorem density_pullDirectedPair (a b : X ↪ W) (D : Digraph W) (A B : Finset X) :
    density (pullDirectedPair a b D) A B = density D (A.map a) (B.map b) := by
  unfold density
  simp only [incidences_eq_sum,card_map,sum_map]
  rfl

theorem centred_regular_pull_of_trim (a b : X ↪ W) (D : Digraph W) (ε δ d : ℝ)
    (hD : IsCentredRegular D ε d) (hδ : 2*ε ≤ δ)
    (hLarge : (Fintype.card W : ℝ)*ε ≤ Fintype.card X)
    (hScale : (Fintype.card W : ℝ)*ε ≤ (Fintype.card X : ℝ)*δ) :
    IsCentredRegular (pullDirectedPair a b D) δ d := by
  let A := (univ : Finset X).map a
  let B := (univ : Finset X).map b
  have hLargeA : ((univ : Finset W).card : ℝ)*ε ≤ A.card := by simpa [A] using hLarge
  have hLargeB : ((univ : Finset W).card : ℝ)*ε ≤ B.card := by simpa [B] using hLarge
  have hScaleA : ((univ : Finset W).card : ℝ)*ε ≤ (A.card : ℝ)*δ := by simpa [A] using hScale
  have hScaleB : ((univ : Finset W).card : ℝ)*ε ≤ (B.card : ℝ)*δ := by simpa [B] using hScale
  have h := uniform_on_subcells D hD.1 (subset_univ A) (subset_univ B)
    hLargeA hLargeB hScaleA hScaleB hδ
  constructor
  · intro S _ T _ hS hT
    rw [density_pullDirectedPair,density_pullDirectedPair]
    exact h _ (map_subset_map.mpr (subset_univ S)) _ (map_subset_map.mpr (subset_univ T))
      (by simpa [A] using hS) (by simpa [B] using hT)
  · rw [density_pullDirectedPair]
    change |density D A B-d| ≤ δ
    have hAB := (hD.1 A (subset_univ _) B (subset_univ _) hLargeA hLargeB).le
    have hBoth := (abs_add_le (density D A B-density D univ univ) (density D univ univ-d)).trans
      (add_le_add hAB hD.2)
    rw [sub_add_sub_cancel] at hBoth
    exact hBoth.trans (by linarith only [hδ])

omit [Fintype W] in
theorem pullDirectedPair_semidegree (a b : X ↪ W) (D : Digraph W) (s : Bool) (x : X) :
    pairSemidegree s (pullDirectedPair a b D) x =
      if s then (((univ : Finset X).map b).filter (D.Adj (a x))).card
      else (((univ : Finset X).map a).filter (fun y => D.Adj y (b x))).card := by
  have hMap (f : X ↪ W) (P : W → Prop) :
      ((univ : Finset X).filter (fun x => P (f x))).map f =
        ((univ : Finset X).map f).filter P := by
    ext v
    simp only [mem_map,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨⟨w,rfl⟩,hw⟩
    · rintro ⟨⟨w,rfl⟩,hw⟩
      exact ⟨w,hw,rfl⟩
  cases s
  · change ((univ : Finset X).filter (fun y => D.Adj (a y) (b x))).card = _
    rw [if_neg Bool.false_ne_true,← hMap,card_map]
  · change ((univ : Finset X).filter (fun y => D.Adj (a x) (b y))).card = _
    rw [if_pos rfl,← hMap,card_map]

/-- A pointwise degree deviation in a retained copy is bounded by its
original deviation and the number of vertices removed from the opposite
side. The estimate is in the new cell size. -/
theorem typical_semidegree_pull_of_trim (a b : X ↪ W) (D : Digraph W)
    (s : Bool) (x : X) (d e δ : ℝ) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hSize : Fintype.card X ≤ Fintype.card W)
    (hTypical : |(pairSemidegree s D (if s then a x else b x) : ℝ)-
      d*(Fintype.card W : ℝ)| ≤ e*(Fintype.card W : ℝ))
    (hBudget : e*(Fintype.card W : ℝ)+((Fintype.card W-Fintype.card X : ℕ) : ℝ) ≤
      δ*(Fintype.card X : ℝ)) :
    |(pairSemidegree s (pullDirectedPair a b D) x : ℝ)-d*(Fintype.card X : ℝ)|
      ≤ δ*(Fintype.card X : ℝ) := by
  let M := Fintype.card W
  let m := Fintype.card X
  let old := pairSemidegree s D (if s then a x else b x)
  let new := pairSemidegree s (pullDirectedPair a b D) x
  have hBounds (E : X ↪ W) (P : W → Prop) :
      let A := (univ : Finset X).map E
      (A.filter P).card ≤ ((univ : Finset W).filter P).card ∧
      ((univ : Finset W).filter P).card ≤ (A.filter P).card+(M-m) := by
    intro A
    refine ⟨card_le_card (filter_subset_filter _ (subset_univ _)),?_⟩
    have h := card_le_card_sdiff_add_card (s := (univ : Finset W).filter P) (t := Aᶜ)
    have he : (univ : Finset W).filter P \ Aᶜ = A.filter P := by
      ext v
      simp [and_comm]
    rw [he,card_compl] at h
    simpa [A,M,m] using h
  have hDeg : new ≤ old ∧ old ≤ new+(M-m) := by
    dsimp [old,new]
    rw [pullDirectedPair_semidegree]
    cases s
    · exact hBounds a (fun y => D.Adj y (b x))
    · exact hBounds b (D.Adj (a x))
  have hp : (M:ℝ) = m+((M-m:ℕ):ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le hSize).symm
  have hDrop : (new:ℝ) ≤ old ∧ (old:ℝ) ≤ new+((M-m:ℕ):ℝ) := by
    exact ⟨by exact_mod_cast hDeg.1,by exact_mod_cast hDeg.2⟩
  have hb₁ := mul_nonneg hd (Nat.cast_nonneg (M-m) : (0 : ℝ) ≤ _)
  have hb₂ := mul_le_of_le_one_left (Nat.cast_nonneg (M-m) : (0 : ℝ) ≤ _) hd1
  change |(old:ℝ)-d*(M:ℝ)| ≤ e*(M:ℝ) at hTypical
  change |(new:ℝ)-d*(m:ℝ)| ≤ δ*(m:ℝ)
  rw [abs_le]
  have h := abs_le.mp hTypical
  have hId : d*(M:ℝ) = d*(m:ℝ)+d*((M-m:ℕ):ℝ) := by exact congrArg (d*·) hp |>.trans (mul_add _ _ _)
  constructor <;> linarith only [h.1,h.2,hDrop.1,hDrop.2,hId,hBudget,hb₁,hb₂]

end OverfullWork.DirectedRegularPairs
