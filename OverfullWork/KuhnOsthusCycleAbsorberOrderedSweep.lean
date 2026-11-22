module

public import OverfullWork.KuhnOsthusMarkedTours
public import OverfullWork.KuhnOsthusCycleAbsorberSweep

@[expose] public section


/-! The cycle sweep of Kühn–Osthus Lemma 10.2 with the two ordered
rows of reserve marks from (CyA3). -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical
variable {V I : Type*} [Fintype V] [Finite I] {t : ℕ}

/-- The main factor becomes Hamiltonian, and the reserve is either
Hamiltonian or a bicycle with the designated repair marks separated.
The columns of the unused marks retain their cyclic order. -/
theorem c4_sweep_with_ordered_reserve (F : Fin t → Equiv.Perm V) {i j : Fin t}
    (hij : i ≠ j) (m : ℕ) (root left right : ℕ → V)
    (hSources : ∀ p < m, left p ≠ right p)
    (hDistinct : ∀ p q, p < q → q < m →
      left q ≠ left p ∧ left q ≠ right p ∧ right q ≠ left p ∧ right q ≠ right p)
    (hRoots : ∀ p < m,
      (F i).SameCycle (root p) (left p) ∧ (F i).SameCycle (root (p+1)) (right p))
    (hCover : ∀ z, ∃ p ≤ m, (F i).SameCycle (root p) z)
    (hCross : ∀ p < m, F i (left p) = F j (right p) ∧ F i (right p) = F j (left p))
    (hDis : ∀ a b, a ≠ b → ∀ z, F a z ≠ F b z)
    (mark : Bool × I ↪ V) (step : Equiv.Perm I) (col : ℕ → I) (final : I)
    (hFinal : ∀ c, step.SameCycle c final) (hUnused : ∀ p < m, col p ≠ final)
    (hMarks : ∀ p < m, left p = mark (false,col p) ∧ right p = mark (true,col p))
    (hOrder : OrderedReserve (F j) mark step) :
    ∃ G : Fin t → Equiv.Perm V,
      matchingUnion G = matchingUnion F ∧
      (∀ a b, a ≠ b → ∀ z, G a z ≠ G b z) ∧
      HasSpanningCycle (fun x y => G i x = y) ∧
      ((∀ v, (G j).SameCycle (mark (false,final)) v) ∨
        MarkedBicycle (G j) (mark (false,final)) (mark (true,final))) ∧
      OrderedReserve (G j) mark step ∧
      G j (mark (false,final)) = F j (mark (false,final)) ∧
      G j (mark (true,final)) = F j (mark (true,final)) ∧
      factorCycleTotal G % 2 = factorCycleTotal F % 2 ∧
      ∀ a z, (a ≠ i ∧ a ≠ j) ∨ (∀ p < m, z ≠ left p ∧ z ≠ right p) → G a z = F a z := by
  have hSwap p (hp : p < m) σ (H : OrderedReserve σ mark step) :
      OrderedReserve (switchSuccessors σ (left p) (right p)) mark step := by
    rw [(hMarks p hp).1,(hMarks p hp).2]
    exact H.switch (col p)
  obtain ⟨G,hUnion,hDisG,hHam,hTail,hParity,hProtect⟩ :=
    c4_sweep_merges_primary_with_invariant F hij m root left right hSources hDistinct hRoots
      hCover hCross hDis (fun σ => OrderedReserve σ mark step) hOrder hSwap
  refine ⟨G,hUnion,hDisG,hHam,hTail.hamilton_or_markedBicycle final hFinal,hTail,
    ?_,?_,hParity,hProtect⟩
  all_goals
    apply hProtect
    right
    intro p hp
    rw [(hMarks p hp).1,(hMarks p hp).2]
    constructor <;> intro h <;> exact hUnused p hp (congrArg Prod.snd (mark.injective h)).symm

end OverfullWork.DirectedRobustExpansion
