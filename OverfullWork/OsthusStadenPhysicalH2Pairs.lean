module

public import OverfullWork.OsthusStadenBridgesFromPrimarySlices

@[expose] public section


/-! Choose a thin physical copy for each ordered base p-cell pair. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical

/-- The physical lift has the same density and regularity between the
two cells as the original indexed copy. -/
theorem lift_centred_regular_pair {V W : Type*} [Fintype V] [Fintype W]
    (a b : W ↪ V) (D : Digraph W) (ε d : ℝ) (hD : IsCentredRegular D ε d) :
    let H := liftDirectedPair a b D
    IsUniform H ε (univ.map a) (univ.map b) ∧
      |density H (univ.map a) (univ.map b)-d| ≤ ε := by
  intro H
  have hPull : pullDirectedPair a b H = D := by
    ext x y
    exact liftDirectedPair_adj a b D x y
  have hDensity (A B : Finset W) : density H (A.map a) (B.map b) = density D A B := by
    rw [←density_pullDirectedPair,hPull]
  have hMap (e : W ↪ V) (S : Finset V) (hS : S ⊆ univ.map e) : ∃ A : Finset W, A.map e = S := by
    refine ⟨univ.filter (fun x => e x ∈ S),?_⟩
    ext v
    constructor
    · rintro h
      obtain ⟨x,hx,rfl⟩ := mem_map.mp h
      exact (mem_filter.mp hx).2
    · intro h
      obtain ⟨x,_,rfl⟩ := mem_map.mp (hS h)
      exact mem_map.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
  refine ⟨?_,?_⟩
  · intro A hA B hB hSizeA hSizeB
    obtain ⟨A,rfl⟩ := hMap a A hA
    obtain ⟨B,rfl⟩ := hMap b B hB
    rw [hDensity,hDensity]
    simp only [card_map] at hSizeA hSizeB
    exact hD.1 A (subset_univ _) B (subset_univ _) hSizeA hSizeB
  · rw [hDensity]
    exact hD.2

set_option maxHeartbeats 900000 in
/-- For H2, choose one labelled copy on each supported primary pair
and read it on the base p-cells. All these arcs are in the same
physical reserve, even when a copy serves several p-cell pairs. -/
theorem exists_primary_thin_pairs_on_base_cells
    {V I U : Type*} [Fintype V] [Fintype I]
    {H : Digraph V} {f : V → Option I} {M : I → I → ℕ} {m₀ b : ℕ} {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc) (q : Fin 5)
    (Q : Digraph I) (project : U → I) (cell : U → Finset V) (ε d : ℝ)
    (hCopy : ∀ i j, Q.Adj i j → 0 < M i j)
    (hCell : ∀ u, cell u ⊆ cluster B.partition (project u))
    (hLarge : ∀ u, (B.size:ℝ)*η ≤ ((cell u).card:ℝ))
    (hScale : ∀ u, (B.size:ℝ)*η ≤ ((cell u).card:ℝ)*ε)
    (hTolerance : 2*η ≤ ε) (hDensity : d ≤ γ*β-2*η) :
    ∃ pair : U → U → Digraph V,
      (∀ u v, pair u v ≤ primaryThinDigraphs B q) ∧
      ∀ u v, Q.Adj (project u) (project v) →
        IsUniform (pair u v) ε (cell u) (cell v) ∧ d ≤ density (pair u v) (cell u) (cell v) := by
  have hPair (u v : U) : ∃ D : Digraph V, D ≤ primaryThinDigraphs B q ∧
      (Q.Adj (project u) (project v) → IsUniform D ε (cell u) (cell v) ∧ d ≤ density D (cell u) (cell v)) := by
    by_cases h : Q.Adj (project u) (project v)
    · let e : ReducedCopy M := ⟨(project u,project v),⟨0,hCopy _ _ h⟩⟩
      let a' := (B.kept (project u)).trans (B.base (project u))
      let b' := (B.kept (project v)).trans (B.base (project v))
      let F := liftDirectedPair a' b' (B.thin q e)
      refine ⟨F,?_,fun _ => ?_⟩
      · exact fun x y h => ⟨e,h⟩
      · obtain ⟨hReg,hFull⟩ := lift_centred_regular_pair a' b' (B.thin q e) η (γ*β) (B.thin_regular q e)
        rw [show univ.map a' = cluster B.partition (project u) from B.retained_cells _,
          show univ.map b' = cluster B.partition (project v) from B.retained_cells _] at hReg hFull
        have hSize (w : U) : (cluster B.partition (project w)).card = B.size := by
          rw [←B.retained_cells _,card_map,card_univ,Fintype.card_fin]
        have hl (w : U) : ((cluster B.partition (project w)).card:ℝ)*η ≤ ((cell w).card:ℝ) := by
          rw [hSize]
          exact hLarge w
        have hsc (w : U) : ((cluster B.partition (project w)).card:ℝ)*η ≤ ((cell w).card:ℝ)*ε := by
          rw [hSize]
          exact hScale w
        have hLow : γ*β-η ≤ density F (cluster B.partition (project u)) (cluster B.partition (project v)) := by
          linarith only [(abs_le.mp hFull).1]
        have hd := density_on_subcells F hReg hLow (hCell u) (hCell v) (hl u) (hl v)
        exact ⟨uniform_on_subcells F hReg (hCell u) (hCell v) (hl u) (hl v) (hsc u) (hsc v) hTolerance,
          by linarith only [hd,hDensity]⟩
    · exact ⟨⊥,bot_le,fun h' => (h h').elim⟩
  choose D hSub hReg using hPair
  exact ⟨D,hSub,hReg⟩

end OverfullWork.DirectedRobustExpansion
