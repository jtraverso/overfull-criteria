module

public import OverfullWork.KuhnOsthusPrescribedMatchings
public import OverfullWork.KuhnOsthusOrderedClusterPaths
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset DirectedRobustExpansion
open scoped Classical

variable {V : Type*}

private noncomputable def joinClusterParts {A U : Finset V} (h : U ⊆ A) :
    U ⊕ ↥(A \ U) ≃ A where
  toFun
    | .inl x => ⟨x.val, h x.prop⟩
    | .inr x => ⟨x.val, (mem_sdiff.mp x.prop).1⟩
  invFun x :=
    if hx : x.val ∈ U then .inl ⟨x.val, hx⟩
    else .inr ⟨x.val, mem_sdiff.mpr ⟨x.prop, hx⟩⟩
  left_inv x := by
    cases x with
    | inl u => simp [u.prop]
    | inr u => simp [(mem_sdiff.mp u.prop).2]
  right_inv x := by
    by_cases hx : x.val ∈ U <;> simp [hx]

/-- Complete one auxiliary bijection with a matching in the filling
reserve on the free endpoints. The auxiliary endpoints need not
be adjacent in the reserve. -/
theorem exists_special_path_step [Fintype V]
    (G : Digraph V) (A B U W : Finset V) (d ε : ℝ) (r : ℕ)
    (hU : U ⊆ A) (hW : W ⊆ B) (hAB : A.card = B.card) (hUW : U.card = W.card)
    (hPair : IsLowerSuperregularPair G ε d A B)
    (hGap : 2*ε < d) (hr : 0 < r) (hCut : (A.card:ℝ)*ε ≤ (r:ℝ))
    (hMargin : (r:ℝ)+(U.card:ℝ) ≤ (d-ε)*(A.card:ℝ)) :
    ∃ e : A ≃ B, ∃ aux : U ≃ W,
      (∀ x : U, (e ⟨x.val, hU x.prop⟩).val = (aux x).val) ∧
      (∀ x : A, x.val ∈ U ↔ (e x).val ∈ W) ∧
      ∀ x : A, x.val ∉ U → G.Adj x (e x) := by
  classical
  obtain ⟨g, hg⟩ := IsLowerSuperregularPair.exists_matching_on_free_vertices
    G A B U W d ε r hPair hU hW hAB hUW hGap hr hCut hMargin
  let aux : U ≃ W := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hUW)
  let e : A ≃ B := (joinClusterParts hU).symm.trans
    ((aux.sumCongr g).trans (joinClusterParts hW))
  have hOccupied (x : A) (hx : x.val ∈ U) :
      (e x).val = (aux ⟨x.val, hx⟩).val := by
    change (joinClusterParts hW ((aux.sumCongr g) ((joinClusterParts hU).symm x))).val = _
    simp [joinClusterParts, hx]
  have hFree (x : A) (hx : x.val ∉ U) :
      (e x).val = (g ⟨x.val, mem_sdiff.mpr ⟨x.prop, hx⟩⟩).val := by
    change (joinClusterParts hW ((aux.sumCongr g) ((joinClusterParts hU).symm x))).val = _
    simp [joinClusterParts, hx]
  refine ⟨e, aux, fun x => hOccupied _ x.prop, ?_, ?_⟩
  · intro x
    by_cases hx : x.val ∈ U
    · simp only [hx, true_iff, hOccupied x hx]
      exact (aux ⟨x.val, hx⟩).prop
    · simp only [hx, false_iff, hFree x hx]
      exact (mem_sdiff.mp (g ⟨x.val, mem_sdiff.mpr ⟨x.prop, hx⟩⟩).prop).2
  · intro x hx
    rw [show G.Adj (x : V) (e x : V) ↔
      G.Adj (x : V) (g ⟨x.val, mem_sdiff.mpr ⟨x.prop, hx⟩⟩ : V) from
      iff_of_eq (congrArg (G.Adj (x : V)) (hFree x hx))]
    exact hg ⟨x.val, mem_sdiff.mpr ⟨x.prop, hx⟩⟩

private def clusterPathOrder {A : ℕ → Finset V} {t n : ℕ}
    (initial : Fin n ≃ A 0) (step : ∀ i < t, A i ≃ A (i+1)) :
    ∀ i ≤ t, Fin n ≃ A i
  | 0, _ => initial
  | i+1, hi => (clusterPathOrder initial step i (by omega)).trans (step i hi)

/-- Construct the special path system of §5.1.5 from the covered
endpoints of the two augmented matchings. The covered sets for
consecutive pairs can differ at their common cluster. Every step
is either auxiliary with the prescribed endpoint sets or a real
edge in the filling reserve. -/
theorem exists_special_path_system_of_covered_sets [Fintype V]
    (G : Digraph V) (A U W : ℕ → Finset V) (t n : ℕ)
    (d ε : ℝ) (r : ℕ)
    (hSize : ∀ i ≤ t, (A i).card = n)
    (hDisj : ∀ i j, i ≤ t → j ≤ t → i ≠ j → Disjoint (A i) (A j))
    (hU : ∀ i < t, U i ⊆ A i) (hW : ∀ i < t, W i ⊆ A (i+1))
    (hUW : ∀ i < t, (U i).card = (W i).card)
    (hPair : ∀ i < t, IsLowerSuperregularPair G ε d (A i) (A (i+1)))
    (hGap : 2*ε < d) (hr : 0 < r) (hCut : (n:ℝ)*ε ≤ (r:ℝ))
    (hMargin : ∀ i < t, (r:ℝ)+((U i).card:ℝ) ≤ (d-ε)*(n:ℝ)) :
    let H : Digraph V := ⟨fun x y => G.Adj x y ∨ ∃ i < t, x ∈ U i ∧ y ∈ W i⟩
    ∃ P : OrderedClusterPaths H A (Fin n) 0 t,
      (∀ i < t, ∀ j, (P.vertex i j ∈ U i ↔ P.vertex (i+1) j ∈ W i) ∧
        (P.vertex i j ∉ U i → G.Adj (P.vertex i j) (P.vertex (i+1) j))) ∧
      (∀ i j : ℕ, i ≤ t → j ≤ t → ∀ a b : Fin n,
        P.vertex i a = P.vertex j b → i = j ∧ a = b) := by
  classical
  intro H
  have hEach (i : ℕ) (hi : i < t) :
      ∃ e : A i ≃ A (i+1), (∀ x : A i, x.val ∈ U i ↔ (e x).val ∈ W i) ∧
        ∀ x : A i, x.val ∉ U i → G.Adj x (e x) := by
    obtain ⟨e, _, _, hClasses, hEdges⟩ := exists_special_path_step
      G (A i) (A (i+1)) (U i) (W i) d ε r (hU i hi) (hW i hi)
      ((hSize i hi.le).trans (hSize (i+1) hi).symm) (hUW i hi) (hPair i hi) hGap hr
      (by rw [hSize i hi.le]; exact hCut) (by rw [hSize i hi.le]; exact hMargin i hi)
    exact ⟨e, hClasses, hEdges⟩
  let step (i : ℕ) (hi : i < t) := Classical.choose (hEach i hi)
  let initial : Fin n ≃ A 0 := Fintype.equivOfCardEq (by simp [hSize 0 (Nat.zero_le _)])
  let order := clusterPathOrder initial step
  let vertex (i : ℕ) (j : Fin n) : V :=
    if hi : i ≤ t then (order i hi j).val else (initial j).val
  have hTransitions (i : ℕ) (hi : i < t) (j : Fin n) :
      (vertex i j ∈ U i ↔ vertex (i+1) j ∈ W i) ∧
      (vertex i j ∉ U i → G.Adj (vertex i j) (vertex (i+1) j)) := by
    have h := Classical.choose_spec (hEach i hi)
    have hle : i+1 ≤ t := by omega
    have hOrder : order (i+1) hle = (order i hi.le).trans (step i hi) := by
      simp [order, clusterPathOrder]
    simp only [vertex, dite_eq_left hi.le, dite_eq_left hle, hOrder]
    change ((order i hi.le j).val ∈ U i ↔ (step i hi (order i hi.le j)).val ∈ W i) ∧
      ((order i hi.le j).val ∉ U i → G.Adj (order i hi.le j) (step i hi (order i hi.le j)))
    exact ⟨h.1 _, h.2 _⟩
  let P : OrderedClusterPaths H A (Fin n) 0 t := {
    vertex := vertex
    part := fun i _ hi j => by simp [vertex, hi]
    injective := fun i _ hi j k hjk =>
      (order i hi).injective (Subtype.ext (by simpa [vertex, hi] using hjk))
    covers := fun i _ hi v hv => by
      obtain ⟨j, hj⟩ := (order i hi).surjective ⟨v, hv⟩
      exact ⟨j, by simp [vertex, hi, hj]⟩
    edge := fun i _ hi j => by
      have h := hTransitions i hi j
      by_cases hx : vertex i j ∈ U i
      · exact Or.inr ⟨i, hi, hx, h.1.mp hx⟩
      · exact Or.inl (h.2 hx) }
  refine ⟨P, hTransitions, fun i j hi hj a b h => ?_⟩
  exact P.unique_coordinates (fun i j _ hi _ hj hne => hDisj i j hi hj hne)
    (Nat.zero_le _) hi (Nat.zero_le _) hj h

/-- Place the endpoint sets of the two augmentations in their
alternating positions on the interval. The first augmentation
uses Aᵢ and Bᵢ, and the second uses Bᵢ and Aᵢ₊₁. -/
theorem exists_special_path_system_of_alternating_augmentations [Fintype V]
    (G : Digraph V) (A : ℕ → Finset V)
    (left₁ right₁ left₂ right₂ : Finset V)
    (ℓ n b : ℕ) (d ε : ℝ) (r : ℕ)
    (hSize : ∀ i ≤ 2*ℓ, (A i).card = n)
    (hDisj : ∀ i j, i ≤ 2*ℓ → j ≤ 2*ℓ → i ≠ j → Disjoint (A i) (A j))
    (hFirst : ∀ i < ℓ, (A (2*i) ∩ left₁).card = b ∧ (A (2*i+1) ∩ right₁).card = b)
    (hSecond : ∀ i < ℓ, (A (2*i+1) ∩ right₂).card = b ∧ (A (2*i+2) ∩ left₂).card = b)
    (hPair : ∀ i < 2*ℓ, IsLowerSuperregularPair G ε d (A i) (A (i+1)))
    (hGap : 2*ε < d) (hr : 0 < r) (hCut : (n:ℝ)*ε ≤ (r:ℝ))
    (hMargin : (r:ℝ)+(b:ℝ) ≤ (d-ε)*(n:ℝ)) :
    let U (i : ℕ) := A i ∩ (if i % 2 = 0 then left₁ else right₂)
    let W (i : ℕ) := A (i+1) ∩ (if i % 2 = 0 then right₁ else left₂)
    let H : Digraph V := ⟨fun x y => G.Adj x y ∨ ∃ i < 2*ℓ, x ∈ U i ∧ y ∈ W i⟩
    ∃ P : OrderedClusterPaths H A (Fin n) 0 (2*ℓ),
      (∀ i < 2*ℓ, ∀ j, (P.vertex i j ∈ U i ↔ P.vertex (i+1) j ∈ W i) ∧
        (P.vertex i j ∉ U i → G.Adj (P.vertex i j) (P.vertex (i+1) j))) ∧
      (∀ i j : ℕ, i ≤ 2*ℓ → j ≤ 2*ℓ → ∀ a b : Fin n,
        P.vertex i a = P.vertex j b → i = j ∧ a = b) := by
  intro U W H
  have hCards (i : ℕ) (hi : i < 2*ℓ) : (U i).card = b ∧ (W i).card = b := by
    have hHalf : i/2 < ℓ := by omega
    by_cases he : i % 2 = 0
    · have hIndex : i = 2*(i/2) := by omega
      simpa only [U, W, ite_eq_left he, ← hIndex] using hFirst (i/2) hHalf
    · have hIndex : i = 2*(i/2)+1 := by omega
      have hNext : i+1 = 2*(i/2)+2 := by omega
      simp only [U, W, ite_eq_right he]
      exact ⟨hIndex.symm ▸ (hSecond (i/2) hHalf).1, hNext.symm ▸ (hSecond (i/2) hHalf).2⟩
  exact exists_special_path_system_of_covered_sets G A U W (2*ℓ) n d ε r hSize hDisj
    (fun _ _ => inter_subset_left) (fun _ _ => inter_subset_left)
    (fun i hi => (hCards i hi).1.trans (hCards i hi).2.symm) hPair hGap hr hCut
    (fun i hi => by rw [(hCards i hi).1]; exact hMargin)

end OverfullWork.ChenShan
