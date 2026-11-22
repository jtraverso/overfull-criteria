module

public import OverfullWork.ActualFirstAnchorStart

@[expose] public section


/-! Pay occupied vertices after adding the actual small anchor matching. -/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 24000000

theorem AnchorPrescription.graph_mono {P : M.PartialColouring k} {i : Fin k}
    {A : Finset V} {a b : V} (s : AnchorPrescription P i A a b) (e : Sym2 V) :
    P.graph.mult e ≤ s.result.graph.mult e := by
  change P.graph.mult e ≤ P.graph.mult e+s.graph.mult e
  omega

theorem AnchorPrescription.occupied_growth {P : M.PartialColouring k} {i : Fin k}
    {A : Finset V} {a b : V} (s : AnchorPrescription P i A a b) (D : Finset V) :
    (D\s.result.colouring.missingSet D i).card ≤ (D\P.colouring.missingSet D i).card+4 := by
  let X := (D\s.result.colouring.missingSet D i)\(D\P.colouring.missingSet D i)
  have hNew : ∀ v ∈ X, 1 ≤ s.graph.degree v := by
    intro v hv
    obtain ⟨hvAfter,hvOld⟩ := mem_sdiff.mp hv
    obtain ⟨hvD,hvNot⟩ := mem_sdiff.mp hvAfter
    have hvBefore : v ∈ P.colouring.missingSet D i := by
      by_contra hh
      exact hvOld (mem_sdiff.mpr ⟨hvD,hh⟩)
    have hBefore : (P.colouring.colourGraph i).degree v=0 := (mem_filter.mp hvBefore).2
    have hAfter : ¬(s.result.colouring.colourGraph i).degree v=0 := by
      intro hh
      exact hvNot (mem_filter.mpr ⟨hvD,hh⟩)
    have hSelected : (s.result.colouring.colourGraph i).degree v=
        (P.colouring.colourGraph i).degree v+s.graph.degree v := by
      change ((P.addMatching i s.graph s.capacity s.compatible).colouring.colourGraph i).degree v=_
      rw [P.addMatching_selected,degree_addCopies]
    omega
  have hCard : X.card ≤ 2*s.graph.edgeCount := by
    calc
      _ = ∑ _v ∈ X, 1 := by simp
      _ ≤ ∑ v ∈ X, s.graph.degree v := sum_le_sum hNew
      _ ≤ ∑ v, s.graph.degree v := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ = _ := s.graph.sum_degrees_eq_twice_edgeCount
  have hSplit := card_le_card_sdiff_add_card
    (s := D\s.result.colouring.missingSet D i) (t := D\P.colouring.missingSet D i)
  have hSmall := s.small
  change _ ≤ X.card+_ at hSplit
  omega

theorem AnchorPrescription.missing_ne_anchors {P : M.PartialColouring k} {i : Fin k}
    {A : Finset V} {a b : V} (s : AnchorPrescription P i A a b) (D : Finset V)
    (v : V) (hv : v ∈ s.result.colouring.missingSet D i) : v ≠ a ∧ v ≠ b := by
  have hz := (mem_filter.mp hv).2
  have hSat := s.anchors_filled
  constructor <;> intro hh <;> subst v <;> omega

end SimpleGraph.MultiGraph.PartialColouring
