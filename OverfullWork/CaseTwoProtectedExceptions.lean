module

public import OverfullWork.InitialForbiddenRatio

@[expose] public section


/-! # Protect both partners and heavy opposite-side neighbors

CMS Step 4 requires that the second stage introduce no internal residue
at a heavy neighbor of the centre. Include that set as well as the
initial partner/anchor exceptions; its total size is at most 6T+2.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b : Fin (p.pairIndex+1) × Bool}

noncomputable def Candidate.CaseTwoPartition.completionExceptions (s : p.CaseTwoPartition P T η b) :
    Finset (Fin (p.pairIndex+1) × Bool) :=
  s.initialExceptions ∪ RegularHeavyCutRepair.heavySet p.completed p.centre b ((p.pairIndex+1)/T)

theorem Candidate.CaseTwoPartition.completionExceptions_card (s : p.CaseTwoPartition P T η b)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T) : s.completionExceptions.card ≤ 6*T+2 := by
  have hHeavy := RegularHeavyCutRepair.heavySet_card_at_scale p.completed p.centre b G.maxDegree
    (p.pairIndex+1) T p.completion.regular hD hT
  have hOld := s.initialExceptions_card hD hT
  have hUnion := card_union_le s.initialExceptions
    (RegularHeavyCutRepair.heavySet p.completed p.centre b ((p.pairIndex+1)/T))
  change (s.initialExceptions ∪ _).card ≤ _
  omega

end OverfullWork.NormalizedCanonicalCandidate
