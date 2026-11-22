module

public import OverfullWork.KuhnOsthusExceptionalFactorSequence

@[expose] public section


/-! The initial exceptional arcs can stay in the ambient graph until
Lemma 11.1. They are never used in the three reserves. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- An original factor pack uses all outgoing slots of its reserve
at each exceptional vertex when their degrees agree. Because every
interval avoids arcs internal to the exceptional set, deleting the
reserve leaves the entire initial digraph on the exceptional set. -/
theorem WoundFactorPacking.reserve_preserves_internal_arcs {V : Type*} [Fintype V]
    {l j K m r : ℕ} {σ : ℝ} {G : Digraph V} {Z : Finset V}
    {X : Fin (l*j) → Finset V} {hj : 0 < j}
    (P : WoundFactorPacking G Z X hj K m r σ) (R : Digraph V)
    (hKeep : (⨆ i, ⨆ a, (P.factors i a).digraph) ≤ R)
    (hSlots : ∀ x ∈ Z, outDegree R x = K*l*r) :
    ∀ x ∈ Z, ∀ y ∈ Z, ¬ R.Adj x y ∧ ((G \ R).Adj x y ↔ G.Adj x y) := by
  intro x hx y hy
  let F : Digraph V := ⨆ i, ⨆ a, (P.factors i a).digraph
  have hDegree : outDegree R x = outDegree F x := by
    rw [hSlots x hx]
    simpa only [F,if_pos hx] using (P.degrees x).2.symm
  have hSubset : (univ.filter (F.Adj x)) ⊆ (univ.filter (R.Adj x)) := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _,hKeep (mem_filter.mp hv).2⟩
  have hEqual : (univ.filter (F.Adj x)) = (univ.filter (R.Adj x)) :=
    eq_of_subset_of_card_le hSubset hDegree.le
  have hNo : ¬ R.Adj x y := by
    intro h
    have hY : y ∈ univ.filter (R.Adj x) := mem_filter.mpr ⟨mem_univ _,h⟩
    rw [←hEqual] at hY
    obtain ⟨i,hi⟩ := Digraph.iSup_adj.mp (mem_filter.mp hY).2
    obtain ⟨a,ha⟩ := Digraph.iSup_adj.mp hi
    exact (P.factors i a).no_internal ha hx hy
  exact ⟨hNo,⟨fun h => h.1,fun h => ⟨h,hNo⟩⟩⟩

/-- The three reserves of the exceptional-factor sequence leave
exactly the original arcs inside the exceptional set for Lemma 11.1. -/
theorem kuhn_osthus_internal_arcs_after_three_reserves {V : Type*} [Fintype V]
    {l f j₈ j₉ j₁₀ p m₈ m₉ m₁₀ r₀ r₃ s : ℕ} {σ₈ σ₉ σ₁₀ : ℝ} {Z : Finset V}
    {X₈ : Fin (l*j₈) → Finset V} {X₉ : Fin (f*j₉) → Finset V} {X₁₀ : Fin (7*j₁₀) → Finset V}
    {hj₈ : 0 < j₈} {hj₉ : 0 < j₉} {hj₁₀ : 0 < j₁₀}
    (G PG CA PC : Digraph V) (E₈ : WoundFactorPacking G Z X₈ hj₈ 50 m₈ r₀ σ₈)
    (E₉ : WoundFactorPacking (G \ PG) Z X₉ hj₉ p m₉ r₃ σ₉)
    (E₁₀ : WoundFactorPacking (G \ (PG ⊔ CA)) Z X₁₀ hj₁₀ 1 m₁₀ s σ₁₀)
    (hKeep₈ : (⨆ i, ⨆ a, (E₈.factors i a).digraph) ≤ PG)
    (hKeep₉ : (⨆ i, ⨆ a, (E₉.factors i a).digraph) ≤ CA)
    (hKeep₁₀ : (⨆ i, ⨆ a, (E₁₀.factors i a).digraph) ≤ PC)
    (hSlots₈ : ∀ x ∈ Z, outDegree PG x = 50*l*r₀)
    (hSlots₉ : ∀ x ∈ Z, outDegree CA x = p*f*r₃)
    (hSlots₁₀ : ∀ x ∈ Z, outDegree PC x = 7*s) :
    ∀ x ∈ Z, ∀ y ∈ Z, (G \ (PG ⊔ (CA ⊔ PC))).Adj x y ↔ G.Adj x y := by
  intro x hx y hy
  have h₈ := (E₈.reserve_preserves_internal_arcs PG hKeep₈ hSlots₈ x hx y hy).1
  have h₉ := (E₉.reserve_preserves_internal_arcs CA hKeep₉ hSlots₉ x hx y hy).1
  have h₁₀ := (E₁₀.reserve_preserves_internal_arcs PC hKeep₁₀
    (fun x hx => by simpa only [one_mul] using hSlots₁₀ x hx) x hx y hy).1
  simp [Digraph.sdiff_adj,Digraph.sup_adj,h₈,h₉,h₁₀]

end OverfullWork.DirectedRobustExpansion
