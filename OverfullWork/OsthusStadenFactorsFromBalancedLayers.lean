module

public import OverfullWork.OsthusStadenDenseFactorBudget

@[expose] public section


/-! Apply the same factor-extraction margins to all the balanced layers. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u v

/-- The simultaneous version of §5.10. The factors and H3 stay within
their given physical layers, so layers remain edge-disjoint. -/
theorem exists_factors_and_h3_of_balanced_physical_layers
    (fraction ε δ : ℝ) (hp : 0 < fraction) (hp₁ : fraction ≤ 1)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hSmall : ε ≤ δ/4) :
    ∃ N : ℕ, ∀ {U : Type u} [Fintype U] {V : Type v} [Fintype V] {J : Type*}
      {G : Digraph V} {H ordinaryArcs : J → Digraph V} {redArcs : J → Finset (V × V)}
      {ordinary : J → Finset V} {cell : J → U → Finset V} {label : J → V → Option U}
      {factor : J → Equiv.Perm U} {κ : ℕ} {cap d : ℝ}
      (B : OsthusStadenBalancedLayerProperties G H ordinaryArcs redArcs ordinary cell label factor κ cap ε d)
      (n cutoff minDemand : ℕ),
      N ≤ n →
      (∀ j, univ.biUnion (cell j) = ordinary j) →
      (∀ j u v, u ≠ v → Disjoint (cell j u) (cell j v)) →
      (∀ j u, (cell j u).card = n) →
      (∀ j u x, label j x = some u ↔ x ∈ cell j u) →
      cap ≤ ((κ-minDemand:ℕ):ℝ) →
      OsthusStadenDenseFactorMargins n κ cutoff minDemand δ ((1-fraction)*d) →
      ∃ P : ∀ j, OsthusStadenPhysicalFactors (H j) (ordinary j) (cell j) (factor j) (redArcs j) n κ δ (fraction*d),
        ∀ j k, j ≠ k → ∀ f g x y,
          (P j).coord x = (P k).coord y →
          (P j).coord ((P j).factors f x) ≠ (P k).coord ((P k).factors g y) := by
  obtain ⟨N,hN⟩ := exists_factors_and_h3_of_balanced_physical_layer.{u,v} fraction ε δ hp hp₁ hε hδ hδ₁ hSmall
  refine ⟨N,?_⟩
  intro U _ V _ J G H ordinaryArcs redArcs ordinary cell label factor κ cap d B n cutoff minDemand hSize
    hCover hDis hCard hLabel hCap margin
  have hOne (j : J) : Nonempty (OsthusStadenPhysicalFactors (H j) (ordinary j) (cell j) (factor j) (redArcs j) n κ δ (fraction*d)) := by
    apply hN (ordinaryArcs j) (H j) (factor j) (ordinary j) (cell j) (label j) (redArcs j) n κ cutoff minDemand d
      hSize (le_sup_left.trans_eq (B.decomposition j).symm) (le_sup_right.trans_eq (B.decomposition j).symm)
      (hCover j) (hDis j) (hCard j) (hLabel j) (B.superregular j) (B.disjoint_parts j) (B.balance j)
      (B.exceptional_degrees j) ?_ margin
    intro x hx
    exact ⟨by exact_mod_cast (B.ordinary_load j false x hx).trans hCap,
      by exact_mod_cast (B.ordinary_load j true x hx).trans hCap⟩
  let P (j : J) := Classical.choice (hOne j)
  refine ⟨P,?_⟩
  intro j k hjk f g x y hxy h
  have hJ := (P j).factor_arcs f x
  have hK := (P k).factor_arcs g y
  exact disjoint_iff_inf_le.mp (B.disjoint_layers j k hjk) ⟨hJ,by rwa [hxy,h]⟩

end OverfullWork.DirectedRobustExpansion
