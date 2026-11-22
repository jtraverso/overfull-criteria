module

public import OverfullWork.CMSCaseTwoResiduePalette
public import OverfullWork.MonotonePrescribedExtension
public import OverfullWork.CanonicalPostPrescriptionBounds

@[expose] public section


/-! Extend a new residue colour using the robust Hall argument of
CMS Step 4. Only the two anchor edges have to be prescribed first. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph PrunedCore MultiGraph.PartialColouring
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V}
variable {a b : V} {d m L r t k f : ℕ} {η : ℝ}
variable {s : CaseTwoPartition M a b d m L r t η}

set_option maxHeartbeats 1600000 in
theorem CaseTwoPartition.exists_fresh_colour_extension
    (s : CaseTwoPartition M a b d m L r t η)
    (Q₀ : M.PartialColouring k) (S : M.PartialColouring (k+f)) (i : Fin (k+f))
    (z : AnchorPrescription S i s.part a b) (occ del : ℕ) (loss : ℝ)
    (hMono : ∀ e, Q₀.graph.mult e ≤ S.graph.mult e)
    (hSeed : ∀ v, Q₀.graph.degree v = k)
    (hOrdinary : ∀ v, v ≠ a → v ≠ b → (Q₀.graph.crossingSupport s.part).degree v ≤ del)
    (hSupport : ∀ v, v ≠ a → v ≠ b → (d:ℝ)/2-loss ≤ M.supportGraph.degree v)
    (hBalance : (S.colouring.colourGraph i).edgesWithin s.part =
      (S.colouring.colourGraph i).edgesWithin s.partᶜ)
    (hOccA : (s.part \ S.colouring.missingSet s.part i).card ≤ occ)
    (hOccB : (s.partᶜ \ S.colouring.missingSet s.partᶜ i).card ≤ occ)
    (hVertex : occ+4 ≤ r) (hDeleted : del+f < r)
    (hMin : (t:ℝ)+(loss+η*(m:ℝ))/2+((occ+4+del+f:ℕ):ℝ) ≤ (d:ℝ)/4) :
    ∃ Q : M.PartialColouring (k+f),
      (∀ v, (Q.colouring.colourGraph i).degree v = 1) ∧
      (∀ j, j ≠ i → Q.colouring.colourGraph j = S.colouring.colourGraph j) ∧
      (∀ e, S.graph.mult e ≤ Q.graph.mult e) ∧
      (∀ v, Q.graph.degree v+(S.colouring.colourGraph i).degree v = S.graph.degree v+1) ∧
      ∀ x y, (x ∈ s.part ↔ y ∈ s.part) → Q.graph.mult s(x,y) = S.graph.mult s(x,y) := by
  have hOcc (D : Finset V) (hSide : D = s.part ∨ D = s.partᶜ) :
      (D \ z.result.colouring.missingSet D i).card ≤ occ+4 := by
    apply (z.occupied_growth D).trans
    rcases hSide with rfl | rfl
    · exact Nat.add_le_add_right hOccA _
    · exact Nat.add_le_add_right hOccB _
  have hDel (v : V) (hv : v ∈ z.result.colouring.missingSet univ i) :
      (z.result.graph.crossingSupport s.part).degree v ≤ del+f := by
    obtain ⟨ha,hb⟩ := z.missing_ne_anchors univ v hv
    have hh := Q₀.crossing_degree_after_fresh_palette z.result s.part v
      (fun e => (hMono e).trans (z.graph_mono e)) (hSeed v)
    exact hh.trans (Nat.add_le_add_right (hOrdinary v ha hb) _)
  have hFree (v : V) (hv : v ∈ z.result.colouring.missingSet univ i)
      (D : Finset V) (hSide : (v ∈ s.part ∧ D = s.partᶜ) ∨ (v ∉ s.part ∧ D = s.part)) :
      t ≤ neighboursIn (M.supportGraph \ z.result.graph.crossingSupport s.part)
        (z.result.colouring.missingSet D i) v := by
    obtain ⟨ha,hb⟩ := z.missing_ne_anchors univ v hv
    have hD : D = s.part ∨ D = s.partᶜ := hSide.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
    have hLower := HallNeighbourLoss.opposite_degree_after_deletions M.supportGraph
      (z.result.graph.crossingSupport s.part) s.part D (z.result.colouring.missingSet D i) v
      ((d:ℝ)/2-loss) (η*(m:ℝ)) hSide (filter_subset _ _) (hSupport v ha hb) (s.simple_discrepancy v)
    have hDelR : ((z.result.graph.crossingSupport s.part).degree v:ℝ) ≤ (del:ℝ)+(f:ℝ) := by
      exact_mod_cast hDel v hv
    have hOccR : ((D \ z.result.colouring.missingSet D i).card:ℝ) ≤ (occ:ℝ)+4 := by
      exact_mod_cast hOcc D hD
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast at hMin
    linarith only [hLower,hOccR,hDelR,hMin]
  apply z.exists_monotone_full_colour_extension r t s.robust
    (s.card_part.trans s.card_compl.symm) hBalance ((hOcc _ (Or.inr rfl)).trans hVertex)
  · intro v hv
    exact (hDel v (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩)).trans_lt hDeleted
  · intro v hv
    exact hFree v (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩)
      s.partᶜ (Or.inl ⟨(mem_filter.mp hv).1,rfl⟩)
  · intro v hv
    exact hFree v (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩)
      s.part (Or.inr ⟨mem_compl.mp (mem_filter.mp hv).1,rfl⟩)

end OverfullWork.CMSBalancedCut
