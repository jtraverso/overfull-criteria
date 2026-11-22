module

public import OverfullWork.OsthusStadenCoreExceptionTrimmedPieces
public import OverfullWork.KuhnOsthusCodegreeCount

@[expose] public section


/-! Exact core degrees from the two oriented supplies, with disjointness
and the ordinary endpoint bounds inherited from the trimmed pieces. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- Combine the outgoing supplies, reversing the incoming supply, and
trim to exact degrees. The exceptional set may depend on the layer. -/
theorem exists_exact_layer_exception_arcs
    {V L : Type*} [Fintype V]
    (G : Digraph V) (Z : L → Finset V) (red : Bool → L → V → Prop)
    (supplied : Bool → L → Digraph V) (κ : ℕ) (cap : ℝ)
    (hSupport : ∀ q j x y, (supplied q j).Adj x y → x ∈ Z j ∧ y ∉ Z j ∧ red q j y ∧
      (if q then G.Adj x y else G.Adj y x))
    (hDegree : ∀ q j x, x ∈ Z j → κ ≤ outDegree (supplied q j) x)
    (hCap : ∀ q j y, (inDegree (supplied q j) y:ℝ) ≤ cap)
    (hDis : ∀ q j k, j ≠ k → Disjoint (supplied q j) (supplied q k))
    (hMixed : ∀ j k x y, (supplied true j).Adj x y → ¬ (supplied false k).Adj y x) :
    ∃ E : L → Digraph V,
      (∀ j, E j ≤ G) ∧ (∀ j k, j ≠ k → Disjoint (E j) (E k)) ∧
      (∀ j x y, (E j).Adj x y →
        (x ∈ Z j ∧ y ∉ Z j ∧ red true j y) ∨ (y ∈ Z j ∧ x ∉ Z j ∧ red false j x)) ∧
      (∀ j x, x ∈ Z j → inDegree (E j) x = κ ∧ outDegree (E j) x = κ) ∧
      ∀ j x, x ∉ Z j → (inDegree (E j) x:ℝ) ≤ cap ∧ (outDegree (E j) x:ℝ) ≤ cap := by
  let X (j : L) := supplied true j ⊔ reverseArcs (supplied false j)
  have hAdj (j : L) (x y : V) : (X j).Adj x y ↔
      (supplied true j).Adj x y ∨ (supplied false j).Adj y x := Iff.rfl
  have hInd (j : L) (x : V) (hx : x ∈ Z j) (y : V) (hy : y ∈ Z j) : ¬ (X j).Adj x y := by
    intro h
    rcases (hAdj _ _ _).mp h with h | h
    · exact (hSupport true j x y h).2.1 hy
    · exact (hSupport false j y x h).2.1 hx
  have hIn (j : L) (x : V) (hx : x ∈ Z j) : κ ≤ inDegree (X j) x := by
    refine (hDegree false j x hx).trans ?_
    unfold outDegree inDegree inNeighbours
    apply card_le_card
    intro y hy
    simp only [mem_filter,mem_univ,true_and] at hy ⊢
    exact (hAdj j y x).mpr (Or.inr hy)
  have hOut (j : L) (x : V) (hx : x ∈ Z j) : κ ≤ outDegree (X j) x := by
    refine (hDegree true j x hx).trans ?_
    unfold outDegree
    apply card_le_card
    intro y hy
    simp only [mem_filter,mem_univ,true_and] at hy ⊢
    exact (hAdj j x y).mpr (Or.inl hy)
  choose E hLe _ hExact using fun j => exists_trimmed_exceptional_arcs (X j) (Z j) κ (hInd j) (hIn j) (hOut j)
  have hSplit (j : L) (x y : V) (h : (E j).Adj x y) :
      (supplied true j).Adj x y ∨ (supplied false j).Adj y x := (hAdj j x y).mp (hLe j h)
  refine ⟨E,?_,?_,?_,hExact,?_⟩
  · intro j x y h
    rcases hSplit j x y h with h | h
    · exact (hSupport true j x y h).2.2.2
    · exact (hSupport false j y x h).2.2.2
  · intro j k hne
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hj,hk⟩
    rcases hSplit _ _ _ hj with h | h <;> rcases hSplit _ _ _ hk with h' | h'
    · exact disjoint_iff_inf_le.mp (hDis true j k hne) ⟨h,h'⟩
    · exact hMixed j k x y h h'
    · exact hMixed k j x y h' h
    · have hf : (⊥ : Digraph V).Adj y x := disjoint_iff_inf_le.mp (hDis false j k hne) ⟨h,h'⟩
      exact hf.elim
  · intro j x y h
    rcases hSplit _ _ _ h with h | h
    · exact Or.inl ⟨(hSupport true j _ _ h).1,(hSupport true j _ _ h).2.1,(hSupport true j _ _ h).2.2.1⟩
    · exact Or.inr ⟨(hSupport false j _ _ h).1,(hSupport false j _ _ h).2.1,(hSupport false j _ _ h).2.2.1⟩
  · intro j x hx
    have hIL : inDegree (E j) x ≤ inDegree (supplied true j) x := by
      unfold inDegree inNeighbours
      apply card_le_card
      intro y hy
      simp only [mem_filter,mem_univ,true_and] at hy ⊢
      rcases hSplit _ _ _ hy with h | h
      · exact h
      · exact (hx (hSupport false j x y h).1).elim
    have hOL : outDegree (E j) x ≤ inDegree (supplied false j) x := by
      unfold outDegree inDegree inNeighbours
      apply card_le_card
      intro y hy
      simp only [mem_filter,mem_univ,true_and] at hy ⊢
      rcases hSplit _ _ _ hy with h | h
      · exact (hx (hSupport true j x y h).1).elim
      · exact h
    exact ⟨(show (inDegree (E j) x:ℝ) ≤ (inDegree (supplied true j) x:ℝ) by exact_mod_cast hIL).trans
      (hCap true j x),
      (show (outDegree (E j) x:ℝ) ≤ (inDegree (supplied false j) x:ℝ) by exact_mod_cast hOL).trans
        (hCap false j x)⟩

/-- The core set is common to all layers, so the two directed supplies
are automatically disjoint after reversing the incoming one. -/
theorem exists_exact_core_exception_arcs
    {V L : Type*} [Fintype V]
    (G : Digraph V) (Z : Finset V) (red : Bool → L → V → Prop)
    (supplied : Bool → L → Digraph V) (κ : ℕ) (cap : ℝ)
    (hSupport : ∀ q j x y, (supplied q j).Adj x y → x ∈ Z ∧ y ∉ Z ∧ red q j y ∧
      (if q then G.Adj x y else G.Adj y x))
    (hDegree : ∀ q j x, x ∈ Z → κ ≤ outDegree (supplied q j) x)
    (hCap : ∀ q j y, (inDegree (supplied q j) y:ℝ) ≤ cap)
    (hDis : ∀ q j k, j ≠ k → Disjoint (supplied q j) (supplied q k)) :
    ∃ E : L → Digraph V,
      (∀ j, E j ≤ G) ∧ (∀ j k, j ≠ k → Disjoint (E j) (E k)) ∧
      (∀ j x y, (E j).Adj x y →
        (x ∈ Z ∧ y ∉ Z ∧ red true j y) ∨ (y ∈ Z ∧ x ∉ Z ∧ red false j x)) ∧
      (∀ j x, x ∈ Z → inDegree (E j) x = κ ∧ outDegree (E j) x = κ) ∧
      ∀ j x, x ∉ Z → (inDegree (E j) x:ℝ) ≤ cap ∧ (outDegree (E j) x:ℝ) ≤ cap :=
  exists_exact_layer_exception_arcs G (fun _ => Z) red supplied κ cap hSupport hDegree hCap hDis
    (fun j k x y h h' => (hSupport false k y x h').2.1 (hSupport true j x y h).1)

end OverfullWork.DirectedRobustExpansion
