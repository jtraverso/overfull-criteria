module

public import OverfullWork.CMSLayoutPacking
public import OverfullWork.CanonicalPairTriangle
public import OverfullWork.FactorizationAssembly

@[expose] public section


/-! Multiplicity view of the disjoint, occurrence-indexed configurations. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset SimpleGraph
open scoped Classical
variable {V I J : Type*}

/-- The multigraph of prescribed copies, counted with multiplicity. -/
noncomputable def Layout.fixedMultigraph (L : Layout V I) : MultiGraph V where
  mult e := (L.fixed.filter (fun i => s(L.source i,L.target i) = e)).card
  loopless e he := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have h := (mem_filter.mp hi).2
    exact (L.ends i).2.2 (Sym2.mk_isDiag_iff.mp (h.symm ▸ he))

/-- The actual submultigraph of a round: host paths together with all
of its prescribed fixed copies. -/
noncomputable def CMSPacking.multigraph {I : J → Type*} {G : SimpleGraph V}
    {L : ∀ j, Layout V (I j)} (P : CMSPacking I G L) (j : J) : MultiGraph V :=
  (MultiGraph.ofSimpleGraph (hostEdges G (P.configuration j).used)).addCopies (L j).fixedMultigraph

/-- The sum of all configurations uses exactly one copy of each consumed
host edge and every fixed copy once. -/
theorem CMSPacking.sum_multigraph [Fintype J] {I : J → Type*} {G : SimpleGraph V}
    {L : ∀ j, Layout V (I j)} (P : CMSPacking I G L) :
    CanonicalPairTriangle.sumCopies univ P.multigraph =
      (MultiGraph.ofSimpleGraph (hostEdges G P.used)).addCopies
        (CanonicalPairTriangle.sumCopies univ (fun j => (L j).fixedMultigraph)) := by
  apply MultiGraph.ext_mult
  intro e
  have hCover : e ∈ (hostEdges G P.used).edgeSet ↔
      ∃ j, e ∈ (hostEdges G (P.configuration j).used).edgeSet := by
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [mem_edgeSet,hostEdges,CMSPacking.used,Digraph.iSup_adj]
      constructor
      · rintro ⟨hG,⟨j,h⟩ | ⟨j,h⟩⟩
        · exact ⟨j,hG,Or.inl h⟩
        · exact ⟨j,hG,Or.inr h⟩
      · rintro ⟨j,hG,h | h⟩
        · exact ⟨hG,Or.inl ⟨j,h⟩⟩
        · exact ⟨hG,Or.inr ⟨j,h⟩⟩
  have h₁ : (∑ j : J, if e ∈ (hostEdges G (P.configuration j).used).edgeSet then 1 else 0) =
      (if e ∈ (hostEdges G P.used).edgeSet then 1 else 0 : ℕ) := by
    by_cases he : e ∈ (hostEdges G P.used).edgeSet
    · obtain ⟨j,hj⟩ := hCover.mp he
      rw [if_pos he,sum_eq_single j]
      · exact if_pos hj
      · intro i _ hij
        apply if_neg
        intro hi
        exact Set.disjoint_left.mp (P.copies_pairwise hij)
          (show Sum.inl e ∈ P.copies i from hi) (show Sum.inl e ∈ P.copies j from hj)
      · simp
    · simp only [if_neg he]
      apply sum_eq_zero
      intro j _
      exact if_neg (fun h => he (hCover.mpr ⟨j,h⟩))
  simp only [CanonicalPairTriangle.sumCopies,CMSPacking.multigraph,MultiGraph.addCopies,
    MultiGraph.ofSimpleGraph,sum_add_distrib]
  rw [h₁]

/-- The configurations are submultigraphs of the host plus the fixed
copies, in the sense that their total multiplicity is bounded at every
unordered pair. -/
theorem CMSPacking.multigraph_capacity [Fintype J] {I : J → Type*} {G : SimpleGraph V}
    [DecidableRel G.Adj] {L : ∀ j, Layout V (I j)} (P : CMSPacking I G L) (e : Sym2 V) :
    (CanonicalPairTriangle.sumCopies univ P.multigraph).mult e ≤
      ((MultiGraph.ofSimpleGraph G).addCopies
        (CanonicalPairTriangle.sumCopies univ (fun j => (L j).fixedMultigraph))).mult e := by
  rw [P.sum_multigraph]
  simp only [MultiGraph.addCopies,MultiGraph.ofSimpleGraph]
  apply Nat.add_le_add_right
  by_cases he : e ∈ (hostEdges G P.used).edgeSet
  · have hG : e ∈ G.edgeSet := by
      induction e using Sym2.inductionOn with
      | hf x y =>
        simp only [mem_edgeSet] at he ⊢
        exact he.1
    simp [he,hG]
  · simp [he]

end OverfullWork.DirectedSpanningConfiguration
