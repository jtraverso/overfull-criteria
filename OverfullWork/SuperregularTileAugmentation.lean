module

public import OverfullWork.SuperregularTileSwitch

@[expose] public section


/-! The edges between old tiles pull back to rectangle bounds on
their indices. The unmatched tile imposes at most one additional
neighbourhood restriction per selected old index. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Lower density bound on rectangles large enough to be tested. -/
def TileRectangleBound (D : Digraph V) (A B : Finset V) (r : ℕ) (η : ℝ) : Prop :=
  ∀ X ⊆ A, ∀ Y ⊆ B, r ≤ X.card → r ≤ Y.card →
    η*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences D X Y:ℝ)

theorem TileRectangleBound.reverse {D : Digraph V} {A B : Finset V} {r : ℕ} {η : ℝ}
    (H : TileRectangleBound D A B r η) :
    TileRectangleBound (reverseArcs D) B A r η := by
  intro X hX Y hY hXsize hYsize
  rw [incidences_reverseArcs]
  calc
    η*(X.card:ℝ)*(Y.card:ℝ) = η*(Y.card:ℝ)*(X.card:ℝ) := by ring
    _ ≤ _ := H Y hY X hX hYsize hXsize

omit [Fintype V] in
/-- The rectangle bound remains valid after restricting the parts. -/
theorem TileRectangleBound.restrict {D : Digraph V} {A B A' B' : Finset V} {r : ℕ} {η : ℝ}
    (H : TileRectangleBound D A B r η) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    TileRectangleBound D A' B' r η :=
  fun X hX Y hY hx hy => H X (hX.trans hA) Y (hY.trans hB) hx hy

theorem LayeredTilePacking.exists_augmentation_of_root_neighbours {p k h : ℕ}
    {X : Fin p → Finset V} {E : Fin p → Fin p → Bool} {R : Fin p → Fin p → Digraph V}
    (P : LayeredTilePacking X E R k) (root : Fin p ↪ V)
    (hRoot : ∀ a, root a ∈ X a) (hFree : ∀ a i b, root a ≠ P.vertices (i,b))
    (shift : Fin p → Fin (h+1)) (S : TileShiftPattern E shift)
    (r : ℕ) (η : ℝ) (L : ℕ → ℝ) (hr : 0 < r) (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hRoom : ∀ n ≤ h, ((h*r+h : ℕ):ℝ) < L n)
    (hProgress : ∀ n < h, L (n+1) ≤ η*L n)
    (hPool : L 0 ≤ (k:ℝ))
    (hSym : ∀ a b u v, (R a b).Adj u v ↔ (R b a).Adj v u)
    (hRect : ∀ a b, tilesTouch E a b → TileRectangleBound (R a b) (X a) (X b) r η)
    (hNeighbours : ∀ a b, tilesTouch E a b →
      L 0 ≤ (((univ : Finset (Fin k)).filter
        (fun j => (R a b).Adj (root a) (P.vertices (j,b)))).card:ℝ)) :
    Nonempty (LayeredTilePacking X E R (k+1)) := by
  let C (i : Fin h) := (univ : Finset (Fin k)).filter (fun j =>
    ∀ a b, shiftedTileConstraint E shift 0 i.succ a b → (R a b).Adj (root a) (P.vertices (j,b)))
  let Q (i j : Fin h) (u v : Fin k) := ∀ a b, shiftedTileConstraint E shift i.succ j.succ a b →
    (R a b).Adj (P.vertices (u,a)) (P.vertices (v,b))
  have hInit (i : Fin h) : L 0 ≤ ((C i).card:ℝ) := by
    by_cases H : ∃ a b, shiftedTileConstraint E shift 0 i.succ a b
    · obtain ⟨a,b,hab⟩ := H
      have hEq : C i = (univ : Finset (Fin k)).filter
          (fun j => (R a b).Adj (root a) (P.vertices (j,b))) := by
        ext j
        simp only [C,mem_filter,mem_univ,true_and]
        exact ⟨fun h => h a b hab,fun h c d hcd => by
          obtain ⟨rfl,rfl⟩ := S.constraint_unique hab hcd
          exact h⟩
      rw [hEq]
      obtain ⟨_,he,_,_⟩ := hab
      exact hNeighbours a b he
    · have hEq : C i = univ := by
        ext j
        simp only [C,mem_filter,mem_univ,true_and,iff_true]
        exact fun a b hab => (H ⟨a,b,hab⟩).elim
      simpa [hEq] using hPool
  have hBad (i j : Fin h) (_ : i < j) (Y : Finset (Fin k)) (_ : Y ⊆ C j) (hY : r ≤ Y.card) :
      ((C i).filter (fun x => (((@Finset.filter _ (Q i j x) (Classical.decPred _) Y)).card:ℝ) < η*(Y.card:ℝ))).card ≤ r := by
    by_cases H : ∃ a b, shiftedTileConstraint E shift i.succ j.succ a b
    · obtain ⟨a,b,hab⟩ := H
      have hEq : Q i j = fun u v => (R a b).Adj (P.vertices (u,a)) (P.vertices (v,b)) := by
        funext u v
        apply propext
        exact ⟨fun h => h a b hab,fun h c d hcd => by
          obtain ⟨rfl,rfl⟩ := S.constraint_unique hab hcd
          exact h⟩
      have hFilter (u : Fin k) : @Finset.filter _ (Q i j u) (Classical.decPred _) Y =
          Y.filter (fun v => (R a b).Adj (P.vertices (u,a)) (P.vertices (v,b))) := by
        ext v
        simp only [mem_filter,hEq]
      simp only [hFilter]
      obtain ⟨_,he,_,_⟩ := hab
      exact card_bad_index_rows_of_rectangle (R a b) (X a) (X b) (C i) Y
        (fun u => P.vertices (u,a)) (fun v => P.vertices (v,b))
        (fun _ _ _ _ h => congrArg Prod.fst (P.vertices.injective h))
        (fun _ _ _ _ h => congrArg Prod.fst (P.vertices.injective h))
        (fun u _ => P.mem u a) (fun v _ => P.mem v b) r η hr hY (hRect a b he)
    · have hAll (x : Fin k) : @Finset.filter _ (Q i j x) (Classical.decPred _) Y = Y := by
        ext v
        simp only [mem_filter]
        exact ⟨fun h => h.1,fun hv => ⟨hv,fun a b hab => (H ⟨a,b,hab⟩).elim⟩⟩
      simp only [hAll]
      have hNot : ¬ (Y.card:ℝ) < η*(Y.card:ℝ) := not_lt_of_ge (by
        calc η*(Y.card:ℝ) ≤ 1*(Y.card:ℝ) := mul_le_mul_of_nonneg_right hη₁ (by positivity)
             _ = _ := one_mul _)
      simp [hNot]
  obtain ⟨f,hInj,hC,hQ⟩ := exists_injective_greedy_embedding C Q r η L hη hInit hRoom hProgress hBad
  let old : Fin h ↪ Fin k := ⟨f,hInj⟩
  refine ⟨P.augmentByShift root hRoot hFree old shift ?_⟩
  intro t a b hab
  let x := t + shift a
  let y := t + shift b
  have hForce : shiftedTileConstraint E shift x y a b := ⟨t,.inl hab,rfl,rfl⟩
  change (R a b).Adj (P.augmentationVertex root old x a) (P.augmentationVertex root old y b)
  clear_value x y
  revert hForce
  refine Fin.cases ?_ (fun i => ?_) x
  · refine Fin.cases ?_ (fun j => ?_) y
    · intro H
      exact (S.constraint_distinct H rfl).elim
    · intro H
      exact (mem_filter.mp (hC j)).2 a b H
  · refine Fin.cases ?_ (fun j => ?_) y
    · intro H
      exact (hSym _ _ _ _).mpr ((mem_filter.mp (hC i)).2 b a H.symm)
    · intro H
      rcases lt_or_gt_of_ne (fun h => S.constraint_distinct H (congrArg Fin.succ h)) with h | h
      · exact hQ i j h a b H
      · exact (hSym _ _ _ _).mpr (hQ j i h b a H.symm)

end OverfullWork.DirectedRobustExpansion
