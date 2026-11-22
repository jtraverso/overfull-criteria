module

public import OverfullWork.HeavyPairBoundary
public import OverfullWork.CompletionOffCentreBudget
public import OverfullWork.DenseHamiltonConnected

@[expose] public section


/-! # Dense Hamilton paths for the heavy-pair branch

Unlike the general CMS robust-expander argument, the actual sparse
off-centre addition gives an above-half degree bound on the ordinary
core. This module uses the already proved dense Hamilton-connectedness
theorem. The explicit slack must still be paid by the source parameters.
-/
namespace OverfullWork.HeavyPairBoundary
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem card_outside (a b : V) (hab : a ≠ b) :
    Fintype.card ↥(outside a b) + 2 = Fintype.card V := by
  rw [show Fintype.card ↥(outside a b) = (outside a b).card from Fintype.card_coe _]
  simp only [outside, card_compl, card_pair hab]
  have htwo : 2 ≤ Fintype.card V := by
    have h := card_le_univ ({a,b} : Finset V)
    simpa [hab] using h
  omega

theorem degree_le_core_add_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (w : outside a b) :
    G.degree w.val ≤ (G.induce (outside a b : Set V)).degree w + 2 := by
  let core := G.induce (outside a b : Set V)
  have hsub : G.neighborFinset w.val ⊆
      (core.neighborFinset w).map (Function.Embedding.subtype _) ∪ {a,b} := by
    intro x hx
    by_cases hxs : x ∈ outside a b
    · refine mem_union_left _ (mem_map.mpr ⟨⟨x,hxs⟩, ?_, rfl⟩)
      apply (mem_neighborFinset core w ⟨x,hxs⟩).mpr
      exact (mem_neighborFinset G w.val x).mp hx
    · exact mem_union_right _ (by
        have h : x = a ∨ x = b := by simpa only [mem_outside, not_and_or, not_not] using hxs
        simpa only [mem_insert, mem_singleton] using h)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_map, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hc
  have hp : ({a,b} : Finset V).card ≤ 2 := card_le_two
  exact hc.trans (Nat.add_le_add_left hp _)

theorem outside_bundle_le (M : MultiGraph V) (D : ℕ)
    (hreg : M.IsRegularOfDegree D) (a b : V) (hab : a ≠ b)
    (w : outside a b) : M.mult s(a,w.val) ≤ D - M.mult s(a,b) := by
  have hs := left_boundary_size M a b hab
  rw [hreg a] at hs
  have hw := single_le_sum (f := fun v : outside a b => M.mult s(a,v.val))
    (fun _ _ => Nat.zero_le _) (mem_univ w)
  omega

theorem core_degree_lower (D A : MultiGraph V) (d B : ℕ)
    (a b : V) (hab : a ≠ b) (hStar : D.IsStarAt a)
    (hreg : (D.addCopies A).IsRegularOfDegree d)
    (hBudget : A.twiceInternal (univ.erase a) ≤ B) (w : outside a b) :
    d ≤ ((D.addCopies A).supportGraph.induce (outside a b : Set V)).degree w +
      (d - (D.addCopies A).mult s(a,b)) + B + 2 := by
  have hwa := ((mem_outside a b w.val).mp w.property).1
  have hRow := CompletionOffCentreBudget.outside_row_le A B a w.val hwa hBudget
  have hn := CompletionOffCentreBudget.degree_le_support_bundle_add
    D A a w.val hwa hStar B hRow
  rw [hreg w.val] at hn
  have hb := outside_bundle_le (D.addCopies A) d hreg a b hab w
  have hc := degree_le_core_add_two (D.addCopies A).supportGraph a b w
  omega

/-- Construct a Hamilton path for any prescribed distinct ordinary ends.
All assumptions concern the original completion and numeric slack. -/
theorem exists_ordinary_hamilton_path (D A : MultiGraph V) (d B : ℕ)
    (a b : V) (hab : a ≠ b) (hStar : D.IsStarAt a)
    (hreg : (D.addCopies A).IsRegularOfDegree d)
    (hBudget : A.twiceInternal (univ.erase a) ≤ B)
    (hn : 7 ≤ Fintype.card V)
    (hslack : Fintype.card V + 2 * (d - (D.addCopies A).mult s(a,b)) +
      2 * B + 4 ≤ 2 * d)
    (u v : outside a b) (huv : u ≠ v) :
    ∃ p : ((D.addCopies A).supportGraph.induce (outside a b : Set V)).Walk u v,
      p.IsHamiltonian := by
  classical
  let core := (D.addCopies A).supportGraph.induce (outside a b : Set V)
  have hc := card_outside a b hab
  have : Nonempty ↥(outside a b) := ⟨u⟩
  obtain ⟨w,hw⟩ := core.exists_minimal_degree_vertex
  have hd := core_degree_lower D A d B a b hab hStar hreg hBudget w
  change d ≤ core.degree w + (d - (D.addCopies A).mult s(a,b)) + B + 2 at hd
  have hmin : d ≤ core.minDegree + (d - (D.addCopies A).mult s(a,b)) + B + 2 := by
    omega
  apply DenseHamilton.exists_hamiltonian_path core ?_ ?_ huv
  · change 5 ≤ Fintype.card ↥(outside a b)
    omega
  · change Fintype.card ↥(outside a b) + 2 ≤ 2 * core.minDegree
    omega

/-- The actual boundary pairing and actual paths coexist. Paths from
different pairs may share edges; sequential deletion is the next step. -/
theorem exists_pairing_with_paths (D A : MultiGraph V) (d B : ℕ)
    (a b : V) (hab : a ≠ b) (hStar : D.IsStarAt a)
    (hreg : (D.addCopies A).IsRegularOfDegree d)
    (hNo : ¬ (D.addCopies A).HasOverfullSubset d)
    (hBudget : A.twiceInternal (univ.erase a) ≤ B)
    (hn : 7 ≤ Fintype.card V)
    (hslack : Fintype.card V + 2 * (d - (D.addCopies A).mult s(a,b)) +
      2 * B + 4 ≤ 2 * d) :
    ∃ e : (Σ w : outside a b, Fin ((D.addCopies A).mult s(a,w.val))) ≃
        (Σ w : outside a b, Fin ((D.addCopies A).mult s(b,w.val))),
      ∀ z, ∃ p : ((D.addCopies A).supportGraph.induce (outside a b : Set V)).Walk
        z.1 (e z).1, p.IsHamiltonian := by
  obtain ⟨e,he,_⟩ := exists_boundary_pairing (D.addCopies A) d hreg hNo a b hab
  refine ⟨e, fun z => ?_⟩
  exact exists_ordinary_hamilton_path D A d B a b hab hStar hreg hBudget hn hslack
    z.1 (e z).1 (fun h => he z (congrArg Subtype.val h))

end OverfullWork.HeavyPairBoundary
