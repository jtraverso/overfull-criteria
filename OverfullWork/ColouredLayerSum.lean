module

public import OverfullWork.CanonicalPairTriangle
public import OverfullWork.OffDiagonalStubPairing

@[expose] public section


/-! # Exact sum of coloured regular multigraph layers

Each layer receives a separate palette. Multiplicities and vertex
degrees add exactly, including repeated copies of a central pair.
-/
namespace OverfullWork.ColouredLayerSum
open SimpleGraph Finset CanonicalPairTriangle
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def colouring {q k : ℕ} (L : Fin q → MultiGraph V)
    (C : ∀ j, (L j).EdgeColoring k) : (sumCopies univ L).EdgeColoring (q*k) := by
  let e : Fin (q*k) ≃ Fin q × Fin k := Fintype.equivOfCardEq (by simp)
  refine {
    col := fun t i => (C (e i).1).col t (e i).2
    sum_col := ?_
    proper := fun v i => (C (e i).1).proper v (e i).2
  }
  intro t
  change (∑ i, (C (e i).1).col t (e i).2) = ∑ j, (L j).mult t
  calc
    _ = ∑ z : Fin q × Fin k, (C z.1).col t z.2 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∑ j, ∑ i, (C j).col t i := Fintype.sum_prod_type _
    _ = _ := sum_congr rfl (fun j _ => (C j).sum_col t)

theorem regular {q k : ℕ} (L : Fin q → MultiGraph V)
    (hL : ∀ j, (L j).IsRegularOfDegree k) :
    (sumCopies univ L).IsRegularOfDegree (q*k) := by
  intro v
  rw [degree_sumCopies]
  calc
    _ = ∑ _j : Fin q, k := sum_congr rfl (fun j _ => hL j v)
    _ = q*k := by simp

theorem enumeration_fiber_sum {I : Type*} [Fintype I] [DecidableEq I]
    {q : ℕ} (c : I → ℕ) (f : Fin q ≃ (Σ i, Fin (c i))) (i : I) :
    (∑ j, if (f j).1 = i then 1 else 0) = c i := by
  calc
    _ = ∑ z : (Σ i, Fin (c i)), if z.1 = i then 1 else 0 :=
      Fintype.sum_equiv f _ _ (fun _ => rfl)
    _ = (univ.filter fun z : (Σ i, Fin (c i)) => z.1 = i).card := by rw [card_filter]
    _ = c i := OverfullWork.OffDiagonalStubPairing.stub_fiber_card c i

end OverfullWork.ColouredLayerSum
