module

public import OverfullWork.OsthusStadenSpecialH1Profiles

@[expose] public section


/-! Eligible physical p-cell halves for the H2 allocations. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

/-- Keep the adapted red phase, including for cells that had no original
red arcs, and intersect with the corresponding base half. -/
noncomputable def balancingHalfCell {V I J : Type*} [Fintype V] [Fintype I]
    {profiles : J → Finset V} {f g : V → Option I}
    {s p mBase m : ℕ} [NeZero s] [NeZero p] {ε τ : ℝ}
    (base : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p mBase ε ε ε)
    (adapted : ∀ i, PrimaryNestedRefinement profiles (cluster g i) s p m τ τ τ)
    (erase : RefinedVertex I s p → V) (u : RefinedVertex I s p) (half : Bool) : Finset V :=
  primaryHalfCell base u half ∩ (primaryHalfCell adapted u half).erase (erase u)

theorem balancingHalfCell_subsets {V I J : Type*} [Fintype V] [Fintype I]
    {profiles : J → Finset V} {f g : V → Option I}
    {s p mBase m : ℕ} [NeZero s] [NeZero p] {ε τ : ℝ}
    (base : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p mBase ε ε ε)
    (adapted : ∀ i, PrimaryNestedRefinement profiles (cluster g i) s p m τ τ τ)
    (erase : RefinedVertex I s p → V) (u : RefinedVertex I s p) (half : Bool) :
    balancingHalfCell base adapted erase u half ⊆ primaryPCells base u ∧
    balancingHalfCell base adapted erase u half ⊆ (primaryPCells adapted u).erase (erase u) := by
  constructor
  · exact inter_subset_left.trans (primaryHalfCell_subset base u half)
  · intro x hx
    obtain ⟨hne,hh⟩ := mem_erase.mp (mem_inter.mp hx).2
    exact mem_erase.mpr ⟨hne,primaryHalfCell_subset adapted u half hh⟩

/-- Equation (22) and the bridge deletion leave enough vertices in each
base-adapted half intersection. The loss is oriented from adapted to base. -/
theorem balancingHalfCell_size_lower {V I J : Type*} [Fintype V] [Fintype I]
    {profiles : J → Finset V} {f g : V → Option I}
    {s p mBase m : ℕ} [NeZero s] [NeZero p] {ε τ : ℝ}
    (base : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p mBase ε ε ε)
    (adapted : ∀ i, PrimaryNestedRefinement profiles (cluster g i) s p m τ τ τ)
    (erase : RefinedVertex I s p → V) (u : RefinedVertex I s p) (half : Bool) (loss : ℕ)
    (hLoss : (primaryHalfCell adapted u half \ primaryHalfCell base u half).card ≤ loss) :
    m ≤ (balancingHalfCell base adapted erase u half).card+loss+1 := by
  let A := primaryHalfCell adapted u half
  let B := primaryHalfCell base u half
  have hPart : (A \ B).card+(A ∩ B).card = A.card := card_sdiff_add_card_inter _ _
  have hLoss' : (A \ B).card ≤ loss := hLoss
  have hCard : A.card = m := primaryHalfCell_card _ _ _
  have hErase : balancingHalfCell base adapted erase u half = (A ∩ B).erase (erase u) := by
    ext x
    simp only [balancingHalfCell,A,B,mem_inter,mem_erase]
    tauto
  have hOne := pred_card_le_card_erase (s := A ∩ B) (a := erase u)
  rw [hErase]
  omega

/-- After the bridge trim, a removed vertex has no ordinary cell
label, and all other labels still describe the same p-cells. -/
noncomputable def trimPCellLabel {V U : Type*}
    (label : V → Option U) (erase : U → V) (x : V) : Option U :=
  (label x).bind (fun u => if x = erase u then none else some u)

theorem trimPCellLabel_eq_some {V U : Type*}
    (label : V → Option U) (cell : U → Finset V) (erase : U → V)
    (hLabel : ∀ x u, label x = some u ↔ x ∈ cell u) (x : V) (u : U) :
    trimPCellLabel label erase x = some u ↔ x ∈ (cell u).erase (erase u) := by
  unfold trimPCellLabel
  rw [mem_erase,←hLabel]
  cases h : label x with
  | none => simp
  | some v =>
    by_cases hx : x = erase v
    · constructor
      · simp [hx]
      · rintro ⟨hne,he⟩
        obtain rfl := Option.some.inj he
        exact (hne hx).elim
    · simp only [Option.bind_some,hx,if_false,Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨hx,rfl⟩
      · exact And.right

end OverfullWork.DirectedRobustExpansion
