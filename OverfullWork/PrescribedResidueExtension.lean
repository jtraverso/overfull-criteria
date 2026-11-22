module

public import OverfullWork.AnchorPrescriptions

@[expose] public section


/-! # Extend a residue color after its actual anchor prescription

Compute the two remaining missing sets, apply the robust free matching,
and add its actual copies. The same constructed result fills the color,
preserves other colors and every internal bundle, and pays one degree
per vertex minus the already occupied selected-color degree.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.BipartiteRobustMargin OverfullWork.PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 32000000

def AnchorPrescription.result {P : M.PartialColouring k} {i : Fin k} {A : Finset V} {a b : V}
    (s : AnchorPrescription P i A a b) : M.PartialColouring k :=
  P.addMatching i s.graph s.capacity s.compatible

theorem AnchorPrescription.anchors_filled {P : M.PartialColouring k} {i : Fin k} {A : Finset V} {a b : V}
    (s : AnchorPrescription P i A a b) :
    (s.result.colouring.colourGraph i).degree a=1 ∧ (s.result.colouring.colourGraph i).degree b=1 := by
  constructor
  · change ((P.addMatching i s.graph s.capacity s.compatible).colouring.colourGraph i).degree a=1
    rw [P.addMatching_selected,degree_addCopies]
    exact s.first
  · change ((P.addMatching i s.graph s.capacity s.compatible).colouring.colourGraph i).degree b=1
    rw [P.addMatching_selected,degree_addCopies]
    exact s.second

theorem AnchorPrescription.missing_balance_after {P : M.PartialColouring k} {i : Fin k}
    {A : Finset V} {a b : V} (s : AnchorPrescription P i A a b)
    (hParts : A.card=Aᶜ.card)
    (hBalance : (P.colouring.colourGraph i).edgesWithin A=(P.colouring.colourGraph i).edgesWithin Aᶜ) :
    (s.result.colouring.missingSet A i).card=(s.result.colouring.missingSet Aᶜ i).card := by
  have hZero : ∀ S : Finset V, (S=A ∨ S=Aᶜ) → s.graph.edgesWithin S=0 := by
    intro S hSide
    unfold MultiGraph.edgesWithin MultiGraph.edgeCount
    apply sum_eq_zero
    intro e _
    change (if e.toFinset ⊆ S then s.graph.mult e else 0)=0
    split_ifs with he
    · induction e using Sym2.inductionOn with
      | hf x y =>
        have hx := he (by simp : x ∈ s(x,y).toFinset)
        have hy := he (by simp : y ∈ s(x,y).toFinset)
        apply s.crossing x y
        rcases hSide with rfl|rfl
        · tauto
        · have hxn := mem_compl.mp hx
          have hyn := mem_compl.mp hy
          tauto
    · rfl
  have hSelected : s.result.colouring.colourGraph i=(P.colouring.colourGraph i).addCopies s.graph :=
    P.addMatching_selected i s.graph s.capacity s.compatible
  have hA := s.result.colouring.missing_internal_cut_identity A i
  have hB := s.result.colouring.missing_internal_cut_identity Aᶜ i
  rw [hSelected,edgesWithin_addCopies,hZero A (Or.inl rfl),Nat.add_zero] at hA
  rw [hSelected,edgesWithin_addCopies,hZero Aᶜ (Or.inr rfl),Nat.add_zero] at hB
  rw [cutSize_compl,←hBalance,←hParts] at hB
  omega

theorem AnchorPrescription.exists_full_colour_extension {P : M.PartialColouring k} {i : Fin k}
    {A : Finset V} {a b : V} (s : AnchorPrescription P i A a b) (r cutoff : ℕ)
    (hRobust : IsBipartiteRobustAt M.supportGraph A r cutoff)
    (hParts : A.card=Aᶜ.card)
    (hBalance : (P.colouring.colourGraph i).edgesWithin A=(P.colouring.colourGraph i).edgesWithin Aᶜ)
    (hVertexLoss : (Aᶜ\s.result.colouring.missingSet Aᶜ i).card ≤ r)
    (hEdgeLoss : ∀ v ∈ s.result.colouring.missingSet Aᶜ i, (s.result.graph.crossingSupport A).degree v < r)
    (hMinLeft : ∀ v ∈ s.result.colouring.missingSet A i,
      cutoff ≤ neighboursIn (M.supportGraph\s.result.graph.crossingSupport A) (s.result.colouring.missingSet Aᶜ i) v)
    (hMinRight : ∀ v ∈ s.result.colouring.missingSet Aᶜ i,
      cutoff ≤ neighboursIn (M.supportGraph\s.result.graph.crossingSupport A) (s.result.colouring.missingSet A i) v) :
    ∃ Q : M.PartialColouring k,
      (∀ v, (Q.colouring.colourGraph i).degree v=1) ∧
      (∀ j, j ≠ i → Q.colouring.colourGraph j=P.colouring.colourGraph j) ∧
      (∀ v, Q.graph.degree v+(P.colouring.colourGraph i).degree v=P.graph.degree v+1) ∧
      ∀ x y, (x ∈ A ↔ y ∈ A) → Q.graph.mult s(x,y)=P.graph.mult s(x,y) := by
  let R := s.result
  let U := R.colouring.missingSet A i
  let B := R.colouring.missingSet Aᶜ i
  have hEqual := s.missing_balance_after hParts hBalance
  obtain ⟨J,hJ,hDegree,hCross⟩ := R.exists_robust_free_matching A U B r cutoff hRobust
    (filter_subset _ _) (filter_subset _ _) hEqual hVertexLoss hEdgeLoss hMinLeft hMinRight
  have hFull : ∀ v, (R.colouring.colourGraph i).degree v+J.degree v=1 := by
    intro v
    have hMember : v ∈ U ∨ v ∈ B ↔ (R.colouring.colourGraph i).degree v=0 := by
      simp only [U,B,EdgeColoring.missingSet,mem_filter,mem_compl]
      tauto
    rw [hDegree v]
    have hOne := R.colouring.colourGraph_degree_le_one i v
    by_cases hv : (R.colouring.colourGraph i).degree v=0
    · rw [if_pos (hMember.mpr hv),hv]
    · rw [if_neg (fun hm => hv (hMember.mp hm))]
      omega
  have hProper : ∀ v, (R.colouring.colourGraph i).degree v+J.degree v ≤ 1 := fun v => (hFull v).le
  let Q := R.addMatching i J hJ hProper
  refine ⟨Q,?_,?_,?_,?_⟩
  · intro v
    rw [R.addMatching_selected,degree_addCopies]
    exact hFull v
  · intro j hj
    exact (R.addMatching_other i J hJ hProper j hj).trans (P.addMatching_other i s.graph s.capacity s.compatible j hj)
  · intro v
    have hFullV := hFull v
    have hSelected : (R.colouring.colourGraph i).degree v=(P.colouring.colourGraph i).degree v+s.graph.degree v := by
      change ((P.addMatching i s.graph s.capacity s.compatible).colouring.colourGraph i).degree v=_
      rw [P.addMatching_selected,degree_addCopies]
    change ((P.graph.addCopies s.graph).addCopies J).degree v+(P.colouring.colourGraph i).degree v=P.graph.degree v+1
    rw [degree_addCopies,degree_addCopies]
    omega
  · intro x y hSame
    change P.graph.mult s(x,y)+s.graph.mult s(x,y)+J.mult s(x,y)=P.graph.mult s(x,y)
    rw [s.crossing x y hSame,hCross x y hSame]
    omega

end SimpleGraph.MultiGraph.PartialColouring
