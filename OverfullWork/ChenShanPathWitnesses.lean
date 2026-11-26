module

public import Mathlib

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

/-- Vertex budget for a rooted witness tree of the given depth. -/
def pathWitnessBudget (length : ℕ) : ℕ → ℕ
  | 0 => length
  | d+1 => length + length * pathWitnessBudget length d

/-- Retain short witnesses for every deletion of at most `depth`
additional vertices. On an intersection, branch on a forbidden vertex
of the current witness and recurse with that vertex excluded. -/
theorem exists_path_witness_set {V : Type*} (K : Finset V → Prop) (length depth : ℕ)
    (hLen : ∀ P, K P → P.card ≤ length) (B : Finset V) :
    ∃ W : Finset V, W.card ≤ pathWitnessBudget length depth ∧
      ∀ Y : Finset V, B ⊆ Y → (Y \ B).card ≤ depth →
        (∃ P, K P ∧ Disjoint P Y) → ∃ P ⊆ W, K P ∧ Disjoint P Y := by
  classical
  induction depth generalizing B with
  | zero =>
    by_cases h : ∃ P, K P ∧ Disjoint P B
    · obtain ⟨P,hK,hB⟩ := h
      refine ⟨P,hLen P hK,?_⟩
      intro Y hSub hCard _
      have hEmpty : Y \ B = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hCard)
      have he : Y = B := Subset.antisymm (sdiff_eq_empty_iff_subset.mp hEmpty) hSub
      exact ⟨P,Subset.rfl,hK,he.symm ▸ hB⟩
    · refine ⟨∅,by simp,?_⟩
      rintro Y hSub _ ⟨P,hK,hY⟩
      exact (h ⟨P,hK,hY.mono_right hSub⟩).elim
  | succ d ih =>
    by_cases h : ∃ P, K P ∧ Disjoint P B
    · obtain ⟨P,hK,hB⟩ := h
      choose Z hSize hStored using fun v : V => ih (insert v B)
      let W := P ∪ P.biUnion Z
      have hCard : W.card ≤ pathWitnessBudget length (d+1) := by
        have ht : (P.biUnion Z).card ≤ P.card * pathWitnessBudget length d := by
          calc
            _ ≤ ∑ v ∈ P, (Z v).card := card_biUnion_le
            _ ≤ ∑ _ ∈ P, pathWitnessBudget length d := sum_le_sum fun v _ => hSize v
            _ = _ := by simp
        have hP := hLen P hK
        have hv := Nat.mul_le_mul_right (pathWitnessBudget length d) hP
        have hw := card_union_le P (P.biUnion Z)
        change W.card ≤ P.card + (P.biUnion Z).card at hw
        simp only [pathWitnessBudget]
        omega
      refine ⟨W,hCard,?_⟩
      intro Y hBY hY hExist
      by_cases hPY : Disjoint P Y
      · exact ⟨P,subset_union_left,hK,hPY⟩
      · obtain ⟨v,hvP,hvY⟩ : ∃ v ∈ P, v ∈ Y := by
          by_contra! hAll
          exact hPY (Finset.disjoint_left.mpr hAll)
        have hvB : v ∉ B := (Finset.disjoint_left.mp hB) hvP
        have hSub : insert v B ⊆ Y := insert_subset_iff.mpr ⟨hvY,hBY⟩
        have he : Y \ insert v B = (Y \ B).erase v := by
          ext w
          simp [and_comm, and_assoc]
        have hs : (Y \ insert v B).card ≤ d := by
          rw [he,card_erase_of_mem (mem_sdiff.mpr ⟨hvY,hvB⟩)]
          omega
        obtain ⟨Q,hQ,hKQ,hYQ⟩ := hStored v Y hSub hs hExist
        refine ⟨Q,?_,hKQ,hYQ⟩
        intro v' hv'
        exact mem_union_right _ (mem_biUnion.mpr ⟨v,hvP,hQ hv'⟩)
    · refine ⟨∅,by simp,?_⟩
      rintro Y hSub _ ⟨P,hK,hY⟩
      exact (h ⟨P,hK,hY.mono_right hSub⟩).elim

/-- Six core pairs, witnesses with at most twelve vertices, and
three levels of forbidden vertices give the paper's constant. -/
theorem exists_path_witness_union_135720 {I V : Type*}
    (S : Finset I) (hS : S.card ≤ 6) (K : I → Finset V → Prop)
    (hLen : ∀ i P, K i P → P.card ≤ 12) :
    ∃ W : Finset V, W.card ≤ 135720 ∧
      ∀ i ∈ S, ∀ Y : Finset V, Y.card ≤ 3 →
        (∃ P, K i P ∧ Disjoint P Y) → ∃ P ⊆ W, K i P ∧ Disjoint P Y := by
  choose W hW hStore using fun i => exists_path_witness_set (K i) 12 3 (hLen i) (∅ : Finset V)
  let R := S.biUnion W
  have hSize : R.card ≤ 135720 := by
    calc
      _ ≤ ∑ i ∈ S, (W i).card := card_biUnion_le
      _ ≤ ∑ _ ∈ S, pathWitnessBudget 12 3 := sum_le_sum fun i _ => hW i
      _ = S.card * pathWitnessBudget 12 3 := by simp
      _ ≤ 6 * pathWitnessBudget 12 3 := Nat.mul_le_mul_right _ hS
      _ = _ := by decide
  refine ⟨R,hSize,?_⟩
  intro i hi Y hY hSome
  obtain ⟨P,hP,hKP,hNo⟩ := hStore i Y (empty_subset _)
    (by simpa only [sdiff_empty] using hY) hSome
  exact ⟨P,fun _ hp => mem_biUnion.mpr ⟨i,hi,hP hp⟩,hKP,hNo⟩


/-- Deleting vertices outside the stored set keeps short witnesses
available after every further deletion of at most three vertices. -/
theorem exists_fault_tolerant_path_reserve {I V : Type*}
    (S : Finset I) (hS : S.card ≤ 6) (K : I → Finset V → Prop)
    (hLen : ∀ i P, K i P → P.card ≤ 12) :
    ∃ W : Finset V, W.card ≤ 135720 ∧
      ∀ i ∈ S, ∀ Y D : Finset V, Y.card ≤ 3 → Disjoint W D →
        (∃ P, K i P ∧ Disjoint P Y) → ∃ P ⊆ W, K i P ∧ Disjoint P (Y ∪ D) := by
  obtain ⟨W,hW,hKeep⟩ := exists_path_witness_union_135720 S hS K hLen
  refine ⟨W,hW,?_⟩
  intro i hi Y D hY hWD hSome
  obtain ⟨P,hP,hK,hNo⟩ := hKeep i hi Y hY hSome
  refine ⟨P,hP,hK,Finset.disjoint_left.mpr ?_⟩
  intro v hv hu
  rcases mem_union.mp hu with hy | hd
  · exact Finset.disjoint_left.mp hNo hv hy
  · exact Finset.disjoint_left.mp hWD (hP hv) hd

end OverfullWork.ChenShan
