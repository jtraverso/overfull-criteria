module

public import OverfullWork.DirectedRobustShortPaths

@[expose] public section


/-! The greedy disjoint-path construction of Lo–Patel, Lemma 3.4.
The marked set may also include vertices off all of the prescribed pairs. -/
namespace OverfullWork.DirectedRobustShortPaths
open Finset DirectedRobustExpansion DirectedListRoutes
open scoped Classical
variable {V : Type*} [Fintype V] {ι : Type*}

theorem exists_disjoint_short_paths (D : Digraph V) {r r' t L : ℕ}
    (hRobust : IsRobustAt D r t) (hr' : 0 < r')
    (hL : Fintype.card V/r'+4 ≤ L)
    (M : Finset V) (x y : ι → V) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i ≠ y j)
    (hMarks : ∀ i, x i ∈ M ∧ y i ∈ M)
    (hIn : ∀ v, t ≤ inDegree D v) :
    ∀ (I : Finset ι) (Z : Finset V),
      (∀ i ∈ I, x i ∉ Z ∧ y i ∉ Z) →
      Z.card+M.card+I.card*L+r' ≤ r →
      (∀ v, t+Z.card+M.card+I.card*L ≤ outDegree D v) →
      ∃ f : ι → List V,
        (∀ i ∈ I, Route D (x i) (y i) (f i) ∧ (x i :: f i).Nodup ∧
          (x i :: f i).length ≤ L ∧
          ∀ v ∈ x i :: f i, v ∉ Z ∧ (v ∈ M → v = x i ∨ v = y i)) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → List.Disjoint (x i :: f i) (x j :: f j)) := by
  intro I
  induction I using Finset.induction_on with
  | empty =>
    intro Z _ _ _
    exact ⟨fun _ => [], by simp, by simp⟩
  | @insert i I hi ih =>
    intro Z hEnds hBudget hOut
    let F := Z ∪ ((M.erase (x i)).erase (y i))
    have hF : F.card ≤ Z.card+M.card :=
      (card_union_le _ _).trans (Nat.add_le_add_left (card_erase_le.trans card_erase_le) _)
    have hxF : x i ∉ F := by simp [F, (hEnds i (mem_insert_self _ _)).1]
    have hyF : y i ∉ F := by simp [F, (hEnds i (mem_insert_self _ _)).2]
    obtain ⟨l, hRoute, hSimple, hLength, hAvoid⟩ := exists_short_path_avoiding D F r r' t
      hRobust hr' (by have := Nat.zero_le ((insert i I).card*L); omega) (x i) (y i)
      hxF hyF (by have := hOut (x i); omega) (hIn (y i))
    have hPathLen : (x i :: l).length ≤ L := by simp only [List.length_cons]; omega
    have hPath : ∀ v ∈ x i :: l, v ∉ Z ∧ (v ∈ M → v = x i ∨ v = y i) := by
      intro v hv
      have hn := hAvoid v hv
      refine ⟨fun hz => hn (mem_union_left _ hz), fun hm => ?_⟩
      by_contra hEq
      push Not at hEq
      exact hn (mem_union_right _ (mem_erase.mpr ⟨hEq.2, mem_erase.mpr ⟨hEq.1, hm⟩⟩))
    let Z' := Z ∪ (x i :: l).toFinset
    have hZ' : Z'.card ≤ Z.card+L :=
      (card_union_le _ _).trans (Nat.add_le_add_left ((List.toFinset_card_le _).trans hPathLen) _)
    have hPaid : Z'.card+M.card+I.card*L ≤ Z.card+M.card+(insert i I).card*L := by
      rw [card_insert_of_notMem hi, Nat.succ_mul]
      omega
    have hEnds' : ∀ j ∈ I, x j ∉ Z' ∧ y j ∉ Z' := by
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      obtain ⟨hjx, hjy⟩ := hEnds j (mem_insert_of_mem hj)
      constructor
      · intro hh
        rcases mem_union.mp hh with hz|hl
        · exact hjx hz
        · rcases (hPath _ (List.mem_toFinset.mp hl)).2 (hMarks j).1 with he|he
          · exact hji (hx he)
          · exact hxy j i he
      · intro hh
        rcases mem_union.mp hh with hz|hl
        · exact hjy hz
        · rcases (hPath _ (List.mem_toFinset.mp hl)).2 (hMarks j).2 with he|he
          · exact hxy i j he.symm
          · exact hji (hy he)
    obtain ⟨f, hf, hDisjoint⟩ := ih Z' hEnds' (by omega)
      (fun v => by have hd := hOut v; omega)
    refine ⟨Function.update f i l, ?_, ?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl|hj
      · simpa using And.intro hRoute (And.intro hSimple (And.intro hPathLen hPath))
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        obtain ⟨hR, hN, hLen, hA⟩ := hf j hj
        rw [Function.update_of_ne hji]
        exact ⟨hR, hN, hLen, fun v hv =>
          ⟨fun hz => (hA v hv).1 (mem_union_left _ hz), (hA v hv).2⟩⟩
    · have hCross : ∀ j ∈ I, List.Disjoint (x i :: l) (x j :: f j) := by
        intro j hj v hv₁ hv₂
        exact ((hf j hj).2.2.2 v hv₂).1 (mem_union_right _ (List.mem_toFinset.mpr hv₁))
      intro j hj k hk hjk
      rcases mem_insert.mp hj with rfl|hjI
      · have hk' := mem_of_mem_insert_of_ne hk (Ne.symm hjk)
        simpa [Function.update_of_ne (Ne.symm hjk)] using hCross k hk'
      · rcases mem_insert.mp hk with rfl|hkI
        · simpa [Function.update_of_ne hjk] using (hCross j hjI).symm
        · have hji : j ≠ i := fun h => hi (h ▸ hjI)
          have hki : k ≠ i := fun h => hi (h ▸ hkI)
          simpa only [Function.update_of_ne hji, Function.update_of_ne hki]
            using hDisjoint j hjI k hkI hjk

end OverfullWork.DirectedRobustShortPaths
