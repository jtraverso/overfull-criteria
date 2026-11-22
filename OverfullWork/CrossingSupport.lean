module

public import OverfullWork.InitialForbiddenBudget

@[expose] public section


/-! # Colored crossing support and the initial deletion-degree budget

Keep only currently colored crossing bundles when deleting from the
robust support. Initially every such edge meets one of the two anchors;
outside the anchors its simple degree is therefore at most two.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def crossingSupport (M : MultiGraph V) (A : Finset V) : SimpleGraph V where
  Adj x y := 0 < M.mult s(x,y) ∧ ¬(x ∈ A ↔ y ∈ A)
  symm := ⟨by intro x y h;rw [Sym2.eq_swap] at h;exact ⟨h.1,fun hh => h.2 hh.symm⟩⟩
  loopless := ⟨fun _ h => h.2 Iff.rfl⟩

theorem crossingSupport_degree_le_cover (M : MultiGraph V) (A E : Finset V)
    (hCover : ∀ x y, (M.crossingSupport A).Adj x y → x ∈ E ∨ y ∈ E)
    (v : V) (hv : v ∉ E) : (M.crossingSupport A).degree v ≤ E.card := by
  rw [←card_neighborFinset_eq_degree]
  apply card_le_card
  intro u hu
  have he := (mem_neighborFinset (M.crossingSupport A) v u).mp hu
  exact (hCover v u he).resolve_left hv

theorem PartialColouring.available_crossing_of_support_sdiff {M : MultiGraph V} {k : ℕ}
    (P : M.PartialColouring k) (A : Finset V) (x y : V)
    (hCross : ¬(x ∈ A ↔ y ∈ A))
    (hEdge : (M.supportGraph\P.graph.crossingSupport A).Adj x y) :
    0 < P.available.mult s(x,y) := by
  have hn : ¬0 < P.graph.mult s(x,y) := fun hh => hEdge.2 ⟨hh,hCross⟩
  have hz : P.graph.mult s(x,y)=0 := by omega
  change 0 < M.mult s(x,y)-P.graph.mult s(x,y)
  rw [hz,Nat.sub_zero]
  exact hEdge.1

end SimpleGraph.MultiGraph

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}

theorem Candidate.CaseTwoMiddleCopies.initial_crossing_support_degree
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q R : p.completed.PartialColouring r.seedPalette} {n₁ t₁ n₂ t₂ : ℕ}
    (hFirst : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n₁ t₁)
    (hSecond : MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q R n₂ t₂)
    (v : Fin (p.pairIndex+1) × Bool) (hva : v ≠ p.centre) (hvb : v ≠ b) :
    (R.graph.crossingSupport s.part).degree v ≤ 2 := by
  have hCover : ∀ x y, (R.graph.crossingSupport s.part).Adj x y →
      x ∈ ({p.centre,b}:Finset (Fin (p.pairIndex+1) × Bool)) ∨ y ∈ ({p.centre,b}:Finset _) := by
    intro x y hxy
    by_contra! hn
    have hxa : x ≠ p.centre := by intro he;exact hn.1 (by simp [he])
    have hya : y ≠ p.centre := by intro he;exact hn.2 (by simp [he])
    have hxb : x ≠ b := by intro he;exact hn.1 (by simp [he])
    have hyb : y ≠ b := by intro he;exact hn.2 (by simp [he])
    have hz := r.initial_runs_away_crossing_zero C hFirst hSecond x y hxa hya hxb hyb hxy.2
    have hp : 0 < R.graph.mult s(x,y) := hxy.1
    omega
  have hh := R.graph.crossingSupport_degree_le_cover s.part {p.centre,b} hCover v (by simp [hva,hvb])
  have hCard : ({p.centre,b}:Finset (Fin (p.pairIndex+1) × Bool)).card ≤ 2 := by
    exact (card_insert_le _ _).trans (by simp)
  exact hh.trans hCard

theorem Candidate.CaseTwoMiddleCopies.initial_crossing_degree_outside_forbidden
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q R : p.completed.PartialColouring r.seedPalette} {n₁ t₁ n₂ t₂ : ℕ}
    (hFirst : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n₁ t₁)
    (hSecond : MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q R n₂ t₂)
    (i : Fin r.seedPalette) (E : Finset (Fin (p.pairIndex+1) × Bool))
    (ha : p.centre ∈ E) (hb : b ∈ E) (h : ℕ) (v : Fin (p.pairIndex+1) × Bool)
    (hv : v ∉ (R.colouring.colourGraph i).residueForbidden (R.colouring.colourGraph_degree_le_one i)
      (R.available.internalPart s.part) s.part E h) : (R.graph.crossingSupport s.part).degree v ≤ 2 := by
  have hf := (R.colouring.colourGraph i).outside_matchingForbidden_facts
    (R.colouring.colourGraph_degree_le_one i) s.part ((R.available.internalPart s.part).highVertices h ∪ E) v hv
  have hvE : v ∉ E := fun he => hf.2.2.1 (mem_union_right _ he)
  exact r.initial_crossing_support_degree C hFirst hSecond v
    (by intro he;exact hvE (he ▸ ha)) (by intro he;exact hvE (he ▸ hb))

end OverfullWork.NormalizedCanonicalCandidate
