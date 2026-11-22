module

public import OverfullWork.HeavyPairDenseCore
public import OverfullWork.DenseBatchPathPacking

@[expose] public section


/-! # Edge-disjoint Hamilton paths for all paired boundary copies

This performs the sequential ordinary-core path selection in CMS
Theorem 4.2, Case 1, under explicit dense slack. Repeated endpoints are
allowed. Both the boundary bijection and the entire edge-disjoint batch
are constructed; no path oracle is assumed.
-/
namespace OverfullWork.HeavyPairBoundary
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem singleton_round_hamiltonian {G : SimpleGraph V} {q : ℕ}
    {a b : Fin q → Fin 1 → V} (s : DenseBatchPathPacking.Packing G q 1 a b) (j : Fin q) :
    (s.paths j 0).IsHamiltonian := by
  apply (s.simple j 0).isHamiltonian_of_mem
  intro v
  obtain ⟨i,hi⟩ := s.spanning j v
  have hi0 : i = 0 := Subsingleton.elim _ _
  rw [hi0] at hi
  exact hi

/-- There are enough distinct heavy-bundle copies to close every path. -/
theorem pair_copies_suffice (M : MultiGraph V) (d B : ℕ)
    (hreg : M.IsRegularOfDegree d) (a b : V)
    (hslack : Fintype.card V + 6 * (d - M.mult s(a,b)) + 2 * B + 10 ≤ 2 * d) :
    d - M.mult s(a,b) ≤ M.mult s(a,b) := by
  have hm := M.mult_pair_le_degree a b
  rw [hreg a] at hm
  omega

theorem exists_boundary_path_packing (D A : MultiGraph V) (d B : ℕ)
    (a b : V) (hab : a ≠ b) (hStar : D.IsStarAt a)
    (hreg : (D.addCopies A).IsRegularOfDegree d)
    (hNo : ¬ (D.addCopies A).HasOverfullSubset d)
    (hBudget : A.twiceInternal (univ.erase a) ≤ B)
    (hn : 10 ≤ Fintype.card V)
    (hslack : Fintype.card V + 6 * (d - (D.addCopies A).mult s(a,b)) +
      2 * B + 10 ≤ 2 * d) :
    ∃ e : (Σ w : outside a b, Fin ((D.addCopies A).mult s(a,w.val))) ≃
        (Σ w : outside a b, Fin ((D.addCopies A).mult s(b,w.val))),
      ∃ f : Fin (d - (D.addCopies A).mult s(a,b)) ≃
        (Σ w : outside a b, Fin ((D.addCopies A).mult s(a,w.val))),
      Nonempty (DenseBatchPathPacking.Packing
        ((D.addCopies A).supportGraph.induce (outside a b : Set V))
        (d - (D.addCopies A).mult s(a,b)) 1
        (fun j _ => (f j).1) (fun j _ => (e (f j)).1)) := by
  classical
  obtain ⟨e, he, hcard⟩ := exists_boundary_pairing (D.addCopies A) d hreg hNo a b hab
  let f : Fin (d - (D.addCopies A).mult s(a,b)) ≃
      (Σ w : outside a b, Fin ((D.addCopies A).mult s(a,w.val))) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard.symm)
  let core := (D.addCopies A).supportGraph.induce (outside a b : Set V)
  have hc := card_outside a b hab
  have : Nonempty ↥(outside a b) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨w, hw⟩ := core.exists_minimal_degree_vertex
  have hd := core_degree_lower D A d B a b hab hStar hreg hBudget w
  change d ≤ core.degree w + (d - (D.addCopies A).mult s(a,b)) + B + 2 at hd
  have hmin : d ≤ core.minDegree + (d - (D.addCopies A).mult s(a,b)) + B + 2 := by
    omega
  refine ⟨e, f, ?_⟩
  apply DenseBatchPathPacking.exists_packing core _ 1 (by omega)
    (fun j _ => (f j).1) (fun j _ => (e (f j)).1)
  · intro j i k
    exact fun h => he (f j) (congrArg Subtype.val h)
  · intro j i k _
    exact Subsingleton.elim _ _
  · intro j i k _
    exact Subsingleton.elim _ _
  · change Fintype.card ↥(outside a b) + 6 * 1 + 2 +
      4 * (d - (D.addCopies A).mult s(a,b)) ≤ 2 * core.minDegree
    omega
  · change 3 * 1 + 5 ≤ Fintype.card ↥(outside a b)
    omega

end OverfullWork.HeavyPairBoundary
