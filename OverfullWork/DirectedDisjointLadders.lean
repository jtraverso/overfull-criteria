module

public import OverfullWork.DirectedAbsorbingLadder

@[expose] public section


/-! Packing disjoint ladders for prescribed pairs (Lo–Patel, Lemma 4.10). -/
namespace OverfullWork.DirectedAbsorbingLadder
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] {ι : Type*}

omit [Fintype V] in
private theorem disjoint_of_avoids_union {A B Z : Finset V} (h : Disjoint A (Z ∪ B)) :
    Disjoint A B :=
  disjoint_left.mpr (fun _ ha hb => disjoint_left.mp h ha (mem_union_right _ hb))

/-- Pack one ladder per active pair, reserving all other marked vertices
and all vertices previously used by the packing. -/
theorem exists_disjoint_ladders (D : Digraph V) {r s t r' L P B : ℕ}
    (hs : 0 < s) (hsr : s ≤ r) (hrt : r ≤ t)
    (hRevBudget : s*Fintype.card V ≤ r*(r-s))
    (hIn : ∀ v, 2*t+s ≤ inDegree D v) (hOut : ∀ v, 2*t+s ≤ outDegree D v)
    (hRobust : IsRobustAt D r t) (hr' : 0 < r')
    (hL : Fintype.card V/r'+4 ≤ L)
    (hP : Fintype.card V/s+8 ≤ P) (hB : P+P/4*L ≤ B)
    (M : Finset V) (x y : ι → V) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i ≠ y j) (hMarks : ∀ i, x i ∈ M ∧ y i ∈ M) :
    ∀ (I : Finset ι) (Z : Finset V),
      (∀ i ∈ I, x i ∉ Z ∧ y i ∉ Z) →
      Z.card+M.card+I.card*B+P ≤ s →
      Z.card+M.card+I.card*B+B+r' ≤ r →
      (∀ w, t+Z.card+M.card+I.card*B+B ≤ outDegree D w) →
      ∃ F : (i : ι) → Option (Σ q, Ladder D (x i) (y i) q),
        (∀ i ∈ I, ∃ q, ∃ A : Ladder D (x i) (y i) q,
          F i = some ⟨q, A⟩ ∧ 4*q+2 ≤ P ∧ A.vertices.card ≤ B ∧
          Disjoint A.vertices Z ∧ ∀ v ∈ A.vertices, v ∈ M → v = x i ∨ v = y i) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ∀ a b, F i = some a → F j = some b → Disjoint a.2.vertices b.2.vertices) := by
  intro I
  induction I using Finset.induction_on with
  | empty =>
    intro Z _ _ _ _
    exact ⟨fun _ => none, by simp, by simp⟩
  | @insert i I hi ih =>
    intro Z hEnds hSpine hRoute hOutRoute
    let W := Z ∪ ((M.erase (x i)).erase (y i))
    have hW : W.card ≤ Z.card+M.card :=
      (card_union_le _ _).trans (Nat.add_le_add_left (card_erase_le.trans card_erase_le) _)
    have hxW : x i ∉ W := by simp [W, (hEnds i (mem_insert_self _ _)).1]
    have hyW : y i ∉ W := by simp [W, (hEnds i (mem_insert_self _ _)).2]
    have hBL : (Fintype.card V/s+8)+(Fintype.card V/s+8)/4*L ≤ B := by
      exact (Nat.add_le_add hP (Nat.mul_le_mul_right L (Nat.div_le_div_right hP))).trans hB
    obtain ⟨q, hSize, A, hCard, hAvoid⟩ :=
      exists_ladder_avoiding D hs hsr hrt hRevBudget hIn hOut hRobust hr' hL
        W (x i) (y i) hxW hyW (hxy i i)
        (by have := Nat.zero_le ((insert i I).card*B); omega)
        (by have := Nat.zero_le ((insert i I).card*B); omega)
        (fun v => by have := hOutRoute v; omega)
    have hCard' : A.vertices.card ≤ B := by
      have hq : q ≤ P/4 := by omega
      exact hCard.trans ((Nat.add_le_add (hSize.trans hP) (Nat.mul_le_mul_right L hq)).trans hB)
    have hMeet : ∀ v ∈ A.vertices, v ∈ M → v = x i ∨ v = y i := by
      intro v hv hm
      by_contra h
      push Not at h
      exact disjoint_left.mp hAvoid hv
        (mem_union_right _ (mem_erase.mpr ⟨h.2, mem_erase.mpr ⟨h.1, hm⟩⟩))
    let Z' := Z ∪ A.vertices
    have hPaid : Z'.card+M.card+I.card*B ≤ Z.card+M.card+(insert i I).card*B := by
      have hZ' := (card_union_le Z A.vertices).trans (Nat.add_le_add_left hCard' _)
      change Z'.card ≤ Z.card+B at hZ'
      rw [card_insert_of_notMem hi, Nat.succ_mul]
      omega
    have hEnds' : ∀ j ∈ I, x j ∉ Z' ∧ y j ∉ Z' := by
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      obtain ⟨hjx, hjy⟩ := hEnds j (mem_insert_of_mem hj)
      constructor
      · intro hh
        rcases mem_union.mp hh with hz|ha
        · exact hjx hz
        · rcases hMeet _ ha (hMarks j).1 with he|he
          · exact hji (hx he)
          · exact hxy j i he
      · intro hh
        rcases mem_union.mp hh with hz|ha
        · exact hjy hz
        · rcases hMeet _ ha (hMarks j).2 with he|he
          · exact hxy i j he.symm
          · exact hji (hy he)
    obtain ⟨F, hF, hDisj⟩ := ih Z' hEnds' (by omega) (by omega)
      (fun v => by have := hOutRoute v; omega)
    refine ⟨Function.update F i (some ⟨q, A⟩), ?_, ?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl|hjI
      · exact ⟨q, A, Function.update_self .., hSize.trans hP, hCard',
          disjoint_left.mpr (fun _ ha hz => disjoint_left.mp hAvoid ha (mem_union_left _ hz)),
          hMeet⟩
      · have hji : j ≠ i := fun h => hi (h ▸ hjI)
        obtain ⟨q', A', hEq, hSize', hCardA', hD, hM⟩ := hF j hjI
        exact ⟨q', A', (Function.update_of_ne hji ..).trans hEq, hSize', hCardA',
          disjoint_left.mpr (fun _ ha hz => disjoint_left.mp hD ha (mem_union_left _ hz)), hM⟩
    · have hCross : ∀ j ∈ I, ∀ b, F j = some b → Disjoint b.2.vertices A.vertices := by
        intro j hj b hb
        obtain ⟨q', A', he, _, _, hD, _⟩ := hF j hj
        have hb' : b = ⟨q', A'⟩ := Option.some.inj (hb.symm.trans he)
        subst b
        exact disjoint_of_avoids_union hD
      intro j hj k hk hjk a b ha hb
      rcases mem_insert.mp hj with rfl|hjI
      · have hkI := mem_of_mem_insert_of_ne hk (Ne.symm hjk)
        rw [Function.update_self] at ha
        rw [Function.update_of_ne (Ne.symm hjk)] at hb
        obtain rfl := Option.some.inj ha.symm
        exact (hCross k hkI b hb).symm
      · rcases mem_insert.mp hk with rfl|hkI
        · rw [Function.update_of_ne hjk] at ha
          rw [Function.update_self] at hb
          obtain rfl := Option.some.inj hb.symm
          exact hCross j hjI a ha
        · have hji : j ≠ i := fun h => hi (h ▸ hjI)
          have hki : k ≠ i := fun h => hi (h ▸ hkI)
          rw [Function.update_of_ne hji] at ha
          rw [Function.update_of_ne hki] at hb
          exact hDisj j hjI k hkI hjk a b ha hb

end OverfullWork.DirectedAbsorbingLadder
