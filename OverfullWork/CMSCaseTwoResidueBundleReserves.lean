module

public import OverfullWork.CMSCaseTwoResidueAnchorChoices
public import OverfullWork.CMSCaseTwoInitialRouteBudgets

@[expose] public section


/-! Quantify the centre copies still available during completion
of the fresh residue colours in CMS Step 4. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph MultiGraph.PartialColouring
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V}
variable {a b w : V} {d m L r t k f : ℕ} {η ξ : ℝ}
variable {s : CaseTwoPartition M a b d m L r t η}

theorem CaseTwoMiddleCopies.InitialCrossingRows.after_good_run
    {copies : CaseTwoMiddleCopies s w} {R Q : M.PartialColouring k}
    (rows : copies.InitialCrossingRows R ξ) {E : Finset V} {h ell n u : ℕ}
    (run : GoodRouteRun s.part E h ell R Q n u)
    (ha : a ∈ E) (hb : b ∈ E) (hSatA : R.graph.degree a = k) (hSatB : R.graph.degree b = k) :
    copies.InitialCrossingRows Q ξ := by
  refine ⟨?_,?_⟩
  · intro v hv
    rw [run.protected_saturated_bundle a ha hSatA v]
    exact rows.centre v hv
  · rw [run.protected_saturated_crossing_degree b hb hSatB]
    exact rows.second

theorem CaseTwoMiddleCopies.InitialCrossingRows.available_centre_lower
    {copies : CaseTwoMiddleCopies s w} {Q : M.PartialColouring k}
    (rows : copies.InitialCrossingRows Q ξ) (S : M.PartialColouring (k+f))
    (hMono : ∀ e, Q.graph.mult e ≤ S.graph.mult e) (hSat : Q.graph.degree a = k)
    (v : V) (hv : v ∈ s.partᶜ) :
    M.mult s(a,v) ≤ 2*S.available.mult s(a,v)+
      (M.mult s(b,w)-M.degreeInto s.part a)+1+2*(⌈ξ⌉₊+f) := by
  have hPalette := S.colouring.degree_le_palette a
  have hGrow := MultiGraph.bundle_growth_le_degree_growth Q.graph S.graph a v f
    (fun z => hMono s(a,z)) (by omega)
  have hBound := copies.bundle_upper v
  have hWeight : s.crossWeight v = M.mult s(a,v) := if_pos hv
  rw [hWeight] at hBound
  have hRow := (rows.centre v hv).2
  have hSub := S.le s(a,v)
  change M.mult s(a,v) ≤ 2*(M.mult s(a,v)-S.graph.mult s(a,v))+_+1+2*(⌈ξ⌉₊+f)
  omega

theorem CaseTwoMiddleCopies.InitialCrossingRows.available_second_upper
    {copies : CaseTwoMiddleCopies s w} {Q : M.PartialColouring k}
    (rows : copies.InitialCrossingRows Q ξ) (S : M.PartialColouring (k+f))
    (hMono : ∀ e, Q.graph.mult e ≤ S.graph.mult e) :
    2*S.available.mult s(a,b) ≤ M.mult s(a,b)+
      2*((M.mult s(b,w)-M.degreeInto s.part a)+s.heavyVertices.card+1) := by
  have hb : b ∈ s.heavyVertices := mem_insert_self _ _
  have hBound := copies.paired_lower b hb
  have hWeight : s.crossWeight b = M.mult s(a,b) := if_pos (mem_compl.mpr s.second_not_mem)
  have hPartner : s.partnerWeight b = 0 := by
    apply dif_neg
    intro hh
    exact (RegularHeavyCutRepair.heavySet_mem M a b b L).mp hh |>.1 rfl
  rw [hWeight,hPartner,add_zero] at hBound
  have hDef : copies.balancing.deficit b ≤
      (M.mult s(b,w)-M.degreeInto s.part a)+s.heavyVertices.card+1 :=
    (single_le_sum (f := copies.balancing.deficit) (fun _ _ => Nat.zero_le _) (mem_univ _)).trans
      copies.deficit_budget
  have hRow := (rows.centre b (mem_compl.mpr s.second_not_mem)).1
  have hLe := hMono s(a,b)
  have hSub := S.le s(a,b)
  change 2*(M.mult s(a,b)-S.graph.mult s(a,b)) ≤ _
  omega

end OverfullWork.CMSBalancedCut
