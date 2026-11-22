module

public import OverfullWork.DirectedRobustShortPaths

@[expose] public section


/-! Shared-endpoint short paths for the short portion of GGKLO Lemma 7.3(i).
Each route uses an interior vertex, even if the endpoint pair is already an arc. -/
namespace OverfullWork.DirectedLayoutShortPaths

open Finset DirectedRobustExpansion DirectedListRoutes DirectedRobustShortPaths
open scoped Classical
variable {V : Type*} [Fintype V] {I : Type*}

private theorem exists_with_interior (D : Digraph V) (M Z : Finset V)
    {r s t : ℕ} (hRobust : IsRobustAt D r t) (hs : 0 < s)
    (hBudget : (M ∪ Z).card+s ≤ r) (x y : V) (hxy : x ≠ y)
    (hxM : x ∈ M) (hyM : y ∈ M) (hxZ : x ∉ Z) (hyZ : y ∉ Z)
    (hx : (M ∪ Z).card < outDegree D x)
    (hOut : ∀ v, t+(M ∪ Z).card ≤ outDegree D v) (hy : t ≤ inDegree D y) :
    ∃ l, Route D x y l ∧ (x :: l).Nodup ∧ 2 ≤ l.length ∧
      l.length ≤ Fintype.card V/s+4 ∧
      ∀ v ∈ x :: l, v ∉ Z ∧ (v ∈ M → v = x ∨ v = y) := by
  let A := univ.filter (fun w => D.Adj x w)
  have hA : outDegree D x ≤ (A \ (M ∪ Z)).card+(M ∪ Z).card :=
    card_le_card_sdiff_add_card
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < (A \ (M ∪ Z)).card by omega)
  obtain ⟨hwA,hwF⟩ := mem_sdiff.mp hw
  have hEdge := (mem_filter.mp hwA).2
  let F := (M ∪ Z).erase y
  have hF : F.card ≤ (M ∪ Z).card := card_erase_le
  have hwF' : w ∉ F := fun h => hwF (mem_of_mem_erase h)
  obtain ⟨l,hPath,hSimple,hLength,hAvoid⟩ := exists_short_path_avoiding D F r s t
    hRobust hs (by omega) w y hwF' (notMem_erase _ _) (by have := hOut w; omega) hy
  have hxF : x ∈ F := mem_erase.mpr ⟨hxy,mem_union_left _ hxM⟩
  have hLen : 0 < l.length := by
    cases l with
    | nil =>
      have he : w = y := Option.some.inj hPath.2
      exact (hwF (he.symm ▸ mem_union_left Z hyM)).elim
    | cons _ _ => simp
  refine ⟨w :: l,⟨List.IsChain.cons_cons hEdge hPath.1,?_⟩,
    List.nodup_cons.mpr ⟨fun h => hAvoid _ h hxF,hSimple⟩,?_,?_,?_⟩
  · exact hPath.2
  · simpa using Nat.succ_le_succ hLen
  · simp only [List.length_cons]
    omega
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨hxZ,fun _ => Or.inl rfl⟩
    · have hn := hAvoid _ hv
      by_cases he : v = y
      · subst v
        exact ⟨hyZ,fun _ => Or.inr rfl⟩
      · exact ⟨fun hz => hn (mem_erase.mpr ⟨he,mem_union_right _ hz⟩),
          fun hm => (hn (mem_erase.mpr ⟨he,mem_union_left _ hm⟩)).elim⟩

/-- Forbidding used interiors allows repeated endpoints, including repeated
ordered pairs. Every chosen path has at least two arcs, so no arc between
layout vertices is used by these paths. -/
theorem exists_shared_endpoint_paths (D : Digraph V) {r s t L : ℕ}
    (hRobust : IsRobustAt D r t) (hs : 0 < s) (hLength : Fintype.card V/s+5 ≤ L)
    (M : Finset V) (x y : I → V)
    (hEnds : ∀ i, x i ∈ M ∧ y i ∈ M ∧ x i ≠ y i)
    (hIn : ∀ v, t ≤ inDegree D v) :
    ∀ (J : Finset I) (Z : Finset V), Disjoint M Z →
      Z.card+M.card+J.card*L+s ≤ r →
      (∀ v, t+Z.card+M.card+J.card*L+1 ≤ outDegree D v) →
      ∃ f : I → List V,
        (∀ i ∈ J, Route D (x i) (y i) (f i) ∧ (x i :: f i).Nodup ∧
          2 ≤ (f i).length ∧ (x i :: f i).length ≤ L ∧
          ∀ v ∈ x i :: f i, v ∉ Z ∧ (v ∈ M → v = x i ∨ v = y i)) ∧
        (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ v, v ∉ M →
          v ∈ x i :: f i → v ∉ x j :: f j) := by
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro Z _ _ _
    exact ⟨fun _ => [],by simp,by simp⟩
  | @insert i J hi ih =>
    intro Z hMZ hBudget hOut
    have hCard : (M ∪ Z).card ≤ M.card+Z.card := card_union_le _ _
    obtain ⟨hx,hy,hxy⟩ := hEnds i
    obtain ⟨l,hRoute,hSimple,hMin,hLen,hAvoid⟩ :=
      exists_with_interior D M Z hRobust hs (by omega) (x i) (y i) hxy hx hy
        (disjoint_left.mp hMZ hx) (disjoint_left.mp hMZ hy)
        (by have := hOut (x i); omega) (fun v => by have := hOut v; omega) (hIn (y i))
    have hL : (x i :: l).length ≤ L := by simp only [List.length_cons]; omega
    let Z' := Z ∪ (x i :: l).toFinset \ M
    have hZ' : Z'.card ≤ Z.card+L := by
      exact (card_union_le _ _).trans (Nat.add_le_add_left
        ((card_le_card sdiff_subset).trans ((List.toFinset_card_le _).trans hL)) _)
    have hApart : Disjoint M Z' := disjoint_left.mpr fun _ hv hz => by
      rcases mem_union.mp hz with hz | hz
      · exact disjoint_left.mp hMZ hv hz
      · exact (mem_sdiff.mp hz).2 hv
    have hPaid : Z'.card+M.card+J.card*L ≤ Z.card+M.card+(insert i J).card*L := by
      rw [card_insert_of_notMem hi,Nat.succ_mul]
      omega
    obtain ⟨f,hf,hDis⟩ := ih Z' hApart (by omega) (fun v => by have := hOut v; omega)
    refine ⟨Function.update f i l,?_,?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · simpa using And.intro hRoute (And.intro hSimple (And.intro hMin (And.intro hL hAvoid)))
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
        obtain ⟨hR,hN,hMin',hL',hA⟩ := hf j hj
        exact ⟨hR,hN,hMin',hL',fun v hv =>
          ⟨fun hz => (hA v hv).1 (mem_union_left _ hz),(hA v hv).2⟩⟩
    · have hCross : ∀ j ∈ J, ∀ v, v ∉ M → v ∈ x i :: l → v ∉ x j :: f j := by
        intro j hj v hv hvi hvj
        exact ((hf j hj).2.2.2.2 v hvj).1
          (mem_union_right _ (mem_sdiff.mpr ⟨List.mem_toFinset.mpr hvi,hv⟩))
      intro j hj k hk hne v hv hvj hvk
      rcases mem_insert.mp hj with rfl | hj
      · have hk' := mem_of_mem_insert_of_ne hk hne.symm
        exact hCross k hk' v hv (by simpa using hvj)
          (by simpa [Function.update_of_ne hne.symm] using hvk)
      · rcases mem_insert.mp hk with rfl | hk
        · exact hCross j (mem_of_mem_insert_of_ne hj hne) v hv (by simpa using hvk)
            (by simpa [Function.update_of_ne hne] using hvj)
        · exact hDis j hj k hk hne v hv
            (by simpa [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using hvj)
            (by simpa [Function.update_of_ne (ne_of_mem_of_not_mem hk hi)] using hvk)

end OverfullWork.DirectedLayoutShortPaths
