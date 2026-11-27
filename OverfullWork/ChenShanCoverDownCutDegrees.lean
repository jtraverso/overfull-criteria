module

public import OverfullWork.ChenShanCoverDownLeave
public import OverfullWork.ChenShanCrossingReserveR4
import OverfullWork.ChenShanAbsorberCatalogue
import OverfullWork.DenseHall
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

/-- In a fixed target class, deleting the induced interior loses at most
the size of that target's interior part. The reserve costs at most its
incident degree at the source. -/
theorem cover_down_pair_cut_loss {X V : Type*}
    (T I : Finset X) (G R : Finset (V × V)) (U : Finset V)
    (v : V) (f : X ↪ (V × V))
    (hInc : ∀ x, (f x).1 = v ∨ (f x).2 = v)
    (hInner : ∀ x, f x ∈ U ×ˢ U → x ∈ I)
    (P Q : X → Prop)
    (hP : ∀ x, P x ↔ f x ∈ G)
    (hQ : ∀ x, Q x ↔ f x ∈ (G \ (G ∩ (U ×ˢ U))) \ R) :
    let loss : ℝ := (I.card : ℝ) + incidentDegree R v
    (T.filter P).card ≤ (T.filter Q).card + loss ∧
    (T.filter (fun x => ¬ Q x)).card ≤ (T.filter (fun x => ¬ P x)).card + loss := by
  let J := T.filter (fun x => f x ∈ R)
  have hJ : J.card ≤ incidentDegree R v := by
    rw [← card_map f]
    apply card_le_card
    intro e he
    obtain ⟨x,hx,rfl⟩ := mem_map.mp he
    exact mem_filter.mpr ⟨(mem_filter.mp hx).2,hInc x⟩
  have hLost (x : X) (hx : x ∈ T) (hp : P x) (hq : ¬ Q x) : x ∈ I ∪ J := by
    by_cases hi : f x ∈ U ×ˢ U
    · exact mem_union_left _ (hInner x hi)
    by_cases hr : f x ∈ R
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,hr⟩)
    exact False.elim (hq ((hQ x).mpr
      (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨(hP x).mp hp,fun he => hi (mem_inter.mp he).2⟩,hr⟩)))
  have hD : (T.filter P).card ≤ (T.filter Q).card + (I.card + J.card) := by
    apply (card_le_card (t := (T.filter Q) ∪ (I ∪ J)) ?_).trans
      ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _))
    intro x hx
    obtain ⟨hx,hp⟩ := mem_filter.mp hx
    by_cases hq : Q x
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,hq⟩)
    · exact mem_union_right _ (hLost x hx hp hq)
  have hN : (T.filter (fun x => ¬ Q x)).card ≤
      (T.filter (fun x => ¬ P x)).card + (I.card + J.card) := by
    apply (card_le_card (t := (T.filter (fun x => ¬ P x)) ∪ (I ∪ J)) ?_).trans
      ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _))
    intro x hx
    obtain ⟨hx,hq⟩ := mem_filter.mp hx
    by_cases hp : P x
    · exact mem_union_right _ (hLost x hx hp hq)
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,hp⟩)
  have hj : (J.card : ℝ) ≤ incidentDegree R v := by exact_mod_cast hJ
  have hd : ((T.filter P).card : ℝ) ≤ (T.filter Q).card + ((I.card : ℝ) + J.card) := by
    exact_mod_cast hD
  have hn : ((T.filter (fun x => ¬ Q x)).card : ℝ) ≤
      (T.filter (fun x => ¬ P x)).card + ((I.card : ℝ) + J.card) := by
    exact_mod_cast hN
  dsimp only
  exact ⟨by linarith only [hd,hj],by linarith only [hn,hj]⟩

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

noncomputable def coverDownRemainder {V : Type*}
    (G R : Finset (V × V)) (U : Finset V) : Finset (V × V) :=
  (G \ (G ∩ (U ×ˢ U))) \ R

/-- Cut-degree inputs to the repair and packing lemmas, on the current
three classes. The bound (4ρ n) covers the rounded color class too. -/
theorem cover_down_cut_degrees
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i+1 ≤ l)
    (R : TripartiteArcSet A B W) {η δ μ : ℝ} (hm : 0 < m)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4) (hInit : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hRatio : (k:ℝ)/m ≤ 3/2) (hBase : 1/2+η ≤ (k:ℝ)/m)
    (hMargin : δ+4*ρ+10*μ ≤ η/2)
    (hBounds : TripartiteResidualPrefixBounds E P Q S i (δ*nestedCoreSize ρ m i))
    (hReserve : ∀ v, (incidentDegree R v : ℝ) ≤ 10*μ*nestedCoreSize ρ m i) :
    let n : ℝ := nestedCoreSize ρ m i
    let H := coverDownRemainder (tripartiteArcs E P Q) R (S.vertices (i+1))
    let ε := δ+4*ρ+10*μ
    (∀ a : ↥(S.left i), (1/2+η/2)*n ≤ ((univ.filter (fun b : ↥(S.right i) => baseRelation H a.val b.val)).card : ℝ)) ∧
    (∀ b : ↥(S.right i), (1/2+η/2)*n ≤ ((univ.filter (fun a : ↥(S.left i) => baseRelation H a.val b.val)).card : ℝ)) ∧
    (∀ a : ↥(S.left i), ((univ.filter (fun w : ↥(S.colors i) => ¬ leftColorRelation H a.val w.val)).card : ℝ) ≤ ε*n) ∧
    (∀ b : ↥(S.right i), ((univ.filter (fun w : ↥(S.colors i) => ¬ rightColorRelation H b.val w.val)).card : ℝ) ≤ ε*n) ∧
    (∀ w : ↥(S.colors i), ((univ.filter (fun a : ↥(S.left i) => ¬ leftColorRelation H a.val w.val)).card : ℝ) ≤ ε*n) ∧
    ∀ w : ↥(S.colors i), ((univ.filter (fun b : ↥(S.right i) => ¬ rightColorRelation H b.val w.val)).card : ℝ) ≤ ε*n := by
  let n : ℝ := nestedCoreSize ρ m i
  let s : ℝ := nestedCoreSize ρ m (i+1)
  let U := S.vertices (i+1)
  let G := tripartiteArcs E P Q
  let H := coverDownRemainder G R U
  have hi₀ : i ≤ l := by omega
  obtain ⟨_,hs,_⟩ := nested_crossing_core_window hρ hρsmall hInit
  change s ≤ 2*ρ*n at hs
  have hs₀ : 0 ≤ s := by positivity
  have hn₀ : 0 ≤ n := by positivity
  have hρn : 0 ≤ ρ*n := mul_nonneg hρ.le hn₀
  have hSL : ((S.left (i+1)).card : ℝ) ≤ 4*ρ*n := by
    rw [S.leftSize _ hi]
    change s ≤ 4*ρ*n
    linarith only [hs,hρn]
  have hSR : ((S.right (i+1)).card : ℝ) ≤ 4*ρ*n := by
    rw [S.rightSize _ hi]
    change s ≤ 4*ρ*n
    linarith only [hs,hρn]
  have hSW : ((S.colors (i+1)).card : ℝ) ≤ 4*ρ*n := by
    have h := (abs_le.mp (S.crossing_color_sizes hi).1).2
    change ((S.colors (i+1)).card : ℝ)-((k:ℝ)/m)*s ≤ 1/2 at h
    have hScale := mul_le_mul_of_nonneg_right hRatio hs₀
    linarith only [h,hScale,hs,hInit]
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hCore : n/(m:ℝ)*m = n := div_mul_cancel₀ _ hmR
  have hColor : n/(m:ℝ)*k = ((k:ℝ)/m)*n := by ring
  have hCW : |((S.colors i).card : ℝ)-n/(m:ℝ)*k| ≤ 1/2 := by
    rw [S.colorsSize _ hi₀,hColor]
    exact nestedColorSize_error _ (by positivity) _
  have hCL : |((S.left i).card : ℝ)-n/(m:ℝ)*m| ≤ 1/2 := by
    rw [S.leftSize _ hi₀,hCore]
    change |n-n| ≤ (1/2:ℝ)
    norm_num
  have hCR : |((S.right i).card : ℝ)-n/(m:ℝ)*m| ≤ 1/2 := by
    rw [S.rightSize _ hi₀,hCore]
    change |n-n| ≤ (1/2:ℝ)
    norm_num
  have hDensity := mul_le_mul_of_nonneg_right hBase hn₀
  have hBudget := mul_le_mul_of_nonneg_right hMargin hn₀
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro u
    let a : A := u.val
    let f : B ↪ OrientedTripartiteEdge A B W :=
      ⟨fun b => (.inl a,.inr (.inl b)),by intro t t' h; simpa using congrArg Prod.snd h⟩
    have hInner (b : B) (h : f b ∈ U ×ˢ U) : b ∈ S.right (i+1) :=
      (mem_vertices_right S _ _).mp (mem_product.mp h).2
    have hOriginal (b : B) : E a b ↔ f b ∈ G := by
      rw [mem_tripartiteArcs]
      rfl
    have hLoss := (cover_down_pair_cut_loss (S.right i) (S.right (i+1)) G R U
      (.inl a) f (fun _ => Or.inl rfl) hInner _ _ hOriginal
      (fun b => (Iff.rfl : baseRelation H a b ↔ f b ∈ H))).1
    have hBefore := hBounds.leftRight 0 (by omega) (by simpa using hi₀) a u.property
    simp only [Nat.add_zero] at hBefore
    have hRes := hReserve (.inl a)
    have hZ := hSR
    have hBefore' := (abs_le.mp hBefore.1).1
    rw [← hColor] at hDensity
    have hLoss' : (((S.right i).filter (E a)).card : ℝ) ≤ (((S.right i).filter (fun b => baseRelation H a b)).card : ℝ) + (((S.right (i+1)).card : ℝ) + incidentDegree R (.inl a)) := by
      convert hLoss using 1
      congr 4
    have hBound : (1/2+η/2)*n ≤ (((S.right i).filter (fun b => baseRelation H a b)).card : ℝ) := by
      dsimp only [n] at hZ hDensity hBudget ⊢
      linarith only [hLoss',hBefore',hRes,hZ,hDensity,hBudget]
    have hCard := DenseHall.subtype_filter_card (S.right i) (fun b => baseRelation H a b)
    have hEq : ((univ.filter (fun b : ↥(S.right i) => baseRelation H a b.val)).card : ℝ) = (((S.right i).filter (fun b => baseRelation H a b)).card : ℝ) := by
      have h := congrArg (fun t : ℕ => (t:ℝ)) hCard
      convert h using 1 <;> congr 4
    have hSub : (1/2+η/2)*n ≤ ((univ.filter (fun b : ↥(S.right i) => baseRelation H a b.val)).card : ℝ) := by
      rw [hEq]
      exact hBound
    exact hSub
  · intro u
    let b : B := u.val
    let f : A ↪ OrientedTripartiteEdge A B W :=
      ⟨fun a => (.inl a,.inr (.inl b)),by intro t t' h; simpa using congrArg Prod.fst h⟩
    have hInner (a : A) (h : f a ∈ U ×ˢ U) : a ∈ S.left (i+1) :=
      (mem_vertices_left S _ _).mp (mem_product.mp h).1
    have hOriginal (a : A) : E a b ↔ f a ∈ G := by
      rw [mem_tripartiteArcs]
      rfl
    have hLoss := (cover_down_pair_cut_loss (S.left i) (S.left (i+1)) G R U
      (.inr (.inl b)) f (fun _ => Or.inr rfl) hInner _ _ hOriginal
      (fun a => (Iff.rfl : baseRelation H a b ↔ f a ∈ H))).1
    have hBefore := hBounds.rightLeft 0 (by omega) (by simpa using hi₀) b u.property
    simp only [Nat.add_zero] at hBefore
    have hRes := hReserve (.inr (.inl b))
    have hZ := hSL
    have hBefore' := (abs_le.mp hBefore.1).1
    rw [← hColor] at hDensity
    have hLoss' : (((S.left i).filter (fun a => E a b)).card : ℝ) ≤ (((S.left i).filter (fun a => baseRelation H a b)).card : ℝ) + (((S.left (i+1)).card : ℝ) + incidentDegree R (.inr (.inl b))) := by
      convert hLoss using 1
      congr 4
    have hBound : (1/2+η/2)*n ≤ (((S.left i).filter (fun a => baseRelation H a b)).card : ℝ) := by
      dsimp only [n] at hZ hDensity hBudget ⊢
      linarith only [hLoss',hBefore',hRes,hZ,hDensity,hBudget]
    have hCard := DenseHall.subtype_filter_card (S.left i) (fun a => baseRelation H a b)
    have hEq : ((univ.filter (fun a : ↥(S.left i) => baseRelation H a.val b)).card : ℝ) = (((S.left i).filter (fun a => baseRelation H a b)).card : ℝ) := by
      have h := congrArg (fun t : ℕ => (t:ℝ)) hCard
      convert h using 1 <;> congr 4
    have hSub : (1/2+η/2)*n ≤ ((univ.filter (fun a : ↥(S.left i) => baseRelation H a.val b)).card : ℝ) := by
      rw [hEq]
      exact hBound
    exact hSub
  · intro u
    let a : A := u.val
    let f : W ↪ OrientedTripartiteEdge A B W :=
      ⟨fun w => (.inr (.inr w),.inl a),by intro t t' h; simpa using congrArg Prod.fst h⟩
    have hInner (w : W) (h : f w ∈ U ×ˢ U) : w ∈ S.colors (i+1) :=
      (mem_vertices_color S _ _).mp (mem_product.mp h).1
    have hOriginal (w : W) : P a w ↔ f w ∈ G := by
      rw [mem_tripartiteArcs]
      rfl
    have hLoss := (cover_down_pair_cut_loss (S.colors i) (S.colors (i+1)) G R U
      (.inl a) f (fun _ => Or.inr rfl) hInner _ _ hOriginal
      (fun w => (Iff.rfl : leftColorRelation H a w ↔ f w ∈ H))).2
    have hBefore := hBounds.leftColors 0 (by omega) (by simpa using hi₀) a u.property
    simp only [Nat.add_zero] at hBefore
    have hRes := hReserve (.inl a)
    have hZ := hSW
    have hBefore' := hBefore.2 hCW
    have hLoss' : (((S.colors i).filter (fun w => ¬ leftColorRelation H a w)).card : ℝ) ≤ (((S.colors i).filter (fun w => ¬ P a w)).card : ℝ) + (((S.colors (i+1)).card : ℝ) + incidentDegree R (.inl a)) := by
      convert hLoss using 1
      congr 4
    have hBound : (((S.colors i).filter (fun w => ¬ leftColorRelation H a w)).card : ℝ) ≤ (δ+4*ρ+10*μ)*n := by
      dsimp only [n] at hZ hDensity hBudget ⊢
      linarith only [hLoss',hBefore',hRes,hZ]
    have hCard := DenseHall.subtype_filter_card (S.colors i) (fun w => ¬ leftColorRelation H a w)
    have hEq : ((univ.filter (fun w : ↥(S.colors i) => ¬ leftColorRelation H a w.val)).card : ℝ) = (((S.colors i).filter (fun w => ¬ leftColorRelation H a w)).card : ℝ) := by
      have h := congrArg (fun t : ℕ => (t:ℝ)) hCard
      convert h using 1 <;> congr 4
    have hSub : ((univ.filter (fun w : ↥(S.colors i) => ¬ leftColorRelation H a w.val)).card : ℝ) ≤ (δ+4*ρ+10*μ)*n := by
      rw [hEq]
      exact hBound
    exact hSub
  · intro u
    let b : B := u.val
    let f : W ↪ OrientedTripartiteEdge A B W :=
      ⟨fun w => (.inr (.inl b),.inr (.inr w)),by intro t t' h; simpa using congrArg Prod.snd h⟩
    have hInner (w : W) (h : f w ∈ U ×ˢ U) : w ∈ S.colors (i+1) :=
      (mem_vertices_color S _ _).mp (mem_product.mp h).2
    have hOriginal (w : W) : Q b w ↔ f w ∈ G := by
      rw [mem_tripartiteArcs]
      rfl
    have hLoss := (cover_down_pair_cut_loss (S.colors i) (S.colors (i+1)) G R U
      (.inr (.inl b)) f (fun _ => Or.inl rfl) hInner _ _ hOriginal
      (fun w => (Iff.rfl : rightColorRelation H b w ↔ f w ∈ H))).2
    have hBefore := hBounds.rightColors 0 (by omega) (by simpa using hi₀) b u.property
    simp only [Nat.add_zero] at hBefore
    have hRes := hReserve (.inr (.inl b))
    have hZ := hSW
    have hBefore' := hBefore.2 hCW
    have hLoss' : (((S.colors i).filter (fun w => ¬ rightColorRelation H b w)).card : ℝ) ≤ (((S.colors i).filter (fun w => ¬ Q b w)).card : ℝ) + (((S.colors (i+1)).card : ℝ) + incidentDegree R (.inr (.inl b))) := by
      convert hLoss using 1
      congr 4
    have hBound : (((S.colors i).filter (fun w => ¬ rightColorRelation H b w)).card : ℝ) ≤ (δ+4*ρ+10*μ)*n := by
      dsimp only [n] at hZ hDensity hBudget ⊢
      linarith only [hLoss',hBefore',hRes,hZ]
    have hCard := DenseHall.subtype_filter_card (S.colors i) (fun w => ¬ rightColorRelation H b w)
    have hEq : ((univ.filter (fun w : ↥(S.colors i) => ¬ rightColorRelation H b w.val)).card : ℝ) = (((S.colors i).filter (fun w => ¬ rightColorRelation H b w)).card : ℝ) := by
      have h := congrArg (fun t : ℕ => (t:ℝ)) hCard
      convert h using 1 <;> congr 4
    have hSub : ((univ.filter (fun w : ↥(S.colors i) => ¬ rightColorRelation H b w.val)).card : ℝ) ≤ (δ+4*ρ+10*μ)*n := by
      rw [hEq]
      exact hBound
    exact hSub
  · intro u
    let w : W := u.val
    let f : A ↪ OrientedTripartiteEdge A B W :=
      ⟨fun a => (.inr (.inr w),.inl a),by intro t t' h; simpa using congrArg Prod.snd h⟩
    have hInner (a : A) (h : f a ∈ U ×ˢ U) : a ∈ S.left (i+1) :=
      (mem_vertices_left S _ _).mp (mem_product.mp h).2
    have hOriginal (a : A) : P a w ↔ f a ∈ G := by
      rw [mem_tripartiteArcs]
      rfl
    have hLoss := (cover_down_pair_cut_loss (S.left i) (S.left (i+1)) G R U
      (.inr (.inr w)) f (fun _ => Or.inl rfl) hInner _ _ hOriginal
      (fun a => (Iff.rfl : leftColorRelation H a w ↔ f a ∈ H))).2
    have hBefore := hBounds.colorsLeft 0 (by omega) (by simpa using hi₀) w u.property
    simp only [Nat.add_zero] at hBefore
    have hRes := hReserve (.inr (.inr w))
    have hZ := hSL
    have hBefore' := hBefore.2 hCL
    have hLoss' : (((S.left i).filter (fun a => ¬ leftColorRelation H a w)).card : ℝ) ≤ (((S.left i).filter (fun a => ¬ P a w)).card : ℝ) + (((S.left (i+1)).card : ℝ) + incidentDegree R (.inr (.inr w))) := by
      convert hLoss using 1
      congr 4
    have hBound : (((S.left i).filter (fun a => ¬ leftColorRelation H a w)).card : ℝ) ≤ (δ+4*ρ+10*μ)*n := by
      dsimp only [n] at hZ hDensity hBudget ⊢
      linarith only [hLoss',hBefore',hRes,hZ]
    have hCard := DenseHall.subtype_filter_card (S.left i) (fun a => ¬ leftColorRelation H a w)
    have hEq : ((univ.filter (fun a : ↥(S.left i) => ¬ leftColorRelation H a.val w)).card : ℝ) = (((S.left i).filter (fun a => ¬ leftColorRelation H a w)).card : ℝ) := by
      have h := congrArg (fun t : ℕ => (t:ℝ)) hCard
      convert h using 1 <;> congr 4
    have hSub : ((univ.filter (fun a : ↥(S.left i) => ¬ leftColorRelation H a.val w)).card : ℝ) ≤ (δ+4*ρ+10*μ)*n := by
      rw [hEq]
      exact hBound
    exact hSub
  · intro u
    let w : W := u.val
    let f : B ↪ OrientedTripartiteEdge A B W :=
      ⟨fun b => (.inr (.inl b),.inr (.inr w)),by intro t t' h; simpa using congrArg Prod.fst h⟩
    have hInner (b : B) (h : f b ∈ U ×ˢ U) : b ∈ S.right (i+1) :=
      (mem_vertices_right S _ _).mp (mem_product.mp h).1
    have hOriginal (b : B) : Q b w ↔ f b ∈ G := by
      rw [mem_tripartiteArcs]
      rfl
    have hLoss := (cover_down_pair_cut_loss (S.right i) (S.right (i+1)) G R U
      (.inr (.inr w)) f (fun _ => Or.inr rfl) hInner _ _ hOriginal
      (fun b => (Iff.rfl : rightColorRelation H b w ↔ f b ∈ H))).2
    have hBefore := hBounds.colorsRight 0 (by omega) (by simpa using hi₀) w u.property
    simp only [Nat.add_zero] at hBefore
    have hRes := hReserve (.inr (.inr w))
    have hZ := hSR
    have hBefore' := hBefore.2 hCR
    have hLoss' : (((S.right i).filter (fun b => ¬ rightColorRelation H b w)).card : ℝ) ≤ (((S.right i).filter (fun b => ¬ Q b w)).card : ℝ) + (((S.right (i+1)).card : ℝ) + incidentDegree R (.inr (.inr w))) := by
      convert hLoss using 1
      congr 4
    have hBound : (((S.right i).filter (fun b => ¬ rightColorRelation H b w)).card : ℝ) ≤ (δ+4*ρ+10*μ)*n := by
      dsimp only [n] at hZ hDensity hBudget ⊢
      linarith only [hLoss',hBefore',hRes,hZ]
    have hCard := DenseHall.subtype_filter_card (S.right i) (fun b => ¬ rightColorRelation H b w)
    have hEq : ((univ.filter (fun b : ↥(S.right i) => ¬ rightColorRelation H b.val w)).card : ℝ) = (((S.right i).filter (fun b => ¬ rightColorRelation H b w)).card : ℝ) := by
      have h := congrArg (fun t : ℕ => (t:ℝ)) hCard
      convert h using 1 <;> congr 4
    have hSub : ((univ.filter (fun b : ↥(S.right i) => ¬ rightColorRelation H b.val w)).card : ℝ) ≤ (δ+4*ρ+10*μ)*n := by
      rw [hEq]
      exact hBound
    exact hSub

/-- The current classes have the sizes required by Lemma 4.13. -/
theorem cover_down_class_sizes
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i ≤ l)
    {η : ℝ} (hBase : 1/2+η ≤ (k:ℝ)/m) (hRatio : (k:ℝ)/m ≤ 3/2)
    (hn : 1 ≤ (nestedCoreSize ρ m i : ℝ)) (hSlack : 1/2 ≤ η*nestedCoreSize ρ m i) :
    let n := nestedCoreSize ρ m i
    Fintype.card ↥(S.left i) = n ∧ Fintype.card ↥(S.right i) = n ∧
      (n:ℝ)/2 ≤ Fintype.card ↥(S.colors i) ∧
      (Fintype.card ↥(S.colors i) : ℝ) ≤ 2*n := by
  dsimp only
  simp only [Fintype.card_coe]
  refine ⟨S.leftSize _ hi,S.rightSize _ hi,?_⟩
  have hSize : |((S.colors i).card : ℝ)-((k:ℝ)/m)*(nestedCoreSize ρ m i)| ≤ 1/2 := by
    rw [S.colorsSize _ hi]
    exact nestedColorSize_error _ (by positivity) _
  have hn₀ : 0 ≤ (nestedCoreSize ρ m i : ℝ) := by positivity
  have hLower := mul_le_mul_of_nonneg_right hBase hn₀
  have hUpper := mul_le_mul_of_nonneg_right hRatio hn₀
  exact ⟨by linarith only [(abs_le.mp hSize).1,hLower,hSlack],
    by linarith only [(abs_le.mp hSize).2,hUpper,hn]⟩

end OverfullWork.ChenShan
