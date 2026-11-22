module

public import OverfullWork.InducedEdgeExchange

@[expose] public section


/-! # Claim 4.5, case (1,1): a surviving edge forces a large cut

This follows the published argument before the final vertex exchange.
The complement is an independent set plus one core vertex. If that
vertex has a neighbour in the independent part, weak VAL forces at
least Delta cut edges. Criticality and residual no-overfullness are not
assumed. The restored Algorithm 2 degree-sum condition supplies weak VAL.
-/
namespace OverfullWork.PaperOneCoreCut
open SimpleGraph Finset OddCutDeficit MatchingOddDeficiency InducedEdgeExchange
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem cut_insert_independent_lower (H : SimpleGraph V) [DecidableRel H.Adj]
    (Z : Finset V) (v : V) (hv : v∉Z) (hInd : H.IsIndepSet (Z:Set V))
    (hEdge : ∃w∈Z,H.Adj v w)
    (hVal : ∀w∈Z,H.Adj v w → H.maxDegree+2≤H.degree v+H.degree w) :
    H.maxDegree≤cutEdges H (insert v Z) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel H.Adj)
    (fun a b=>Classical.propDecidable (H.Adj a b)))
  let A:=Plantholt.nbIn H Z v
  let a:=A.card
  have hASub:A⊆Z:=by intro w hw;exact (mem_filter.mp hw).2
  have hAPos:1≤a:=by
    apply card_pos.mpr
    obtain ⟨w,hw,hvw⟩:=hEdge
    exact ⟨w,mem_filter.mpr ⟨(mem_neighborFinset H v w).mpr hvw,hw⟩⟩
  have hInternal:internalEdges H (insert v Z)=a:=by
    rw [internal_edges_insert H Z v hv,internal_zero_of_independent H Z hInd,Nat.zero_add]
  have hCut:=internal_cut_identity H (insert v Z)
  rw [hInternal,sum_insert hv] at hCut
  have hSum:(∑w∈A,H.degree w)≤∑w∈Z,H.degree w:=
    sum_le_sum_of_subset_of_nonneg hASub (fun _ _ _=>Nat.zero_le _)
  have hValSum:a*(H.maxDegree+2)≤a*H.degree v+(∑w∈A,H.degree w):=by
    calc
      _ = ∑_w∈A,(H.maxDegree+2) := by simp [a]
      _ ≤ ∑w∈A,(H.degree v+H.degree w) := by
        apply sum_le_sum
        intro w hw
        exact hVal w (hASub hw) ((mem_neighborFinset H v w).mp (mem_filter.mp hw).1)
      _ = _ := by rw [sum_add_distrib];simp [a]
  have hD:=H.degree_le_maxDegree v
  have hGap:H.degree v+(H.maxDegree-H.degree v)=H.maxDegree:=Nat.add_sub_of_le hD
  have hMul:H.maxDegree-H.degree v≤a*(H.maxDegree-H.degree v):=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (H.maxDegree-H.degree v) hAPos
  have hDist:a*H.degree v+a*(H.maxDegree-H.degree v)=a*H.maxDegree:=by
    rw [←Nat.mul_add,hGap]
  nlinarith only [hCut,hSum,hValSum,hGap,hMul,hDist]

/-- The first published (1,1) subcase. No-overfullness of the entire
residue is not an input: the actual cut lower bound is proved directly. -/
theorem one_core_omission_cut_lower (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (hInd : H.IsIndepSet (↑(Xᶜ):Set V))
    (hVal : ∀w∈Xᶜ,∀u,H.Adj w u → H.maxDegree+2≤H.degree w+H.degree u)
    (v y : V) (hv : v∈X) (hy : y∈Xᶜ)
    (hEdge : ∃w∈Xᶜ.erase y,H.Adj v w) :
    H.maxDegree≤cutEdges H (insert y (X.erase v)) := by
  let S:=insert y (X.erase v)
  let Z:=Xᶜ.erase y
  have hvNot:v∉Z:=by simp only [Z,mem_erase,mem_compl];tauto
  have hZInd:H.IsIndepSet (Z:Set V):=by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab hAdj
    exact hInd (mem_erase.mp ha).2 (mem_erase.mp hb).2 hab hAdj
  have hWeak:∀w∈Z,H.Adj v w → H.maxDegree+2≤H.degree v+H.degree w:=by
    intro w hw hAdj
    have hh:=hVal w (mem_erase.mp hw).2 v hAdj.symm
    omega
  have hComplement:Sᶜ=insert v Z:=by
    ext w
    have hyX:y∉X:=mem_compl.mp hy
    by_cases hwv:w=v <;> by_cases hwy:w=y <;> simp_all [S,Z]
  rw [←NearTightOddSetGeometry.cutEdges_compl H S,hComplement]
  exact cut_insert_independent_lower H Z v hvNot hZInd hEdge hWeak

theorem one_core_omission_nonoverfull_of_edge (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (hOdd : Odd X.card) (hInd : H.IsIndepSet (↑(Xᶜ):Set V))
    (hVal : ∀w∈Xᶜ,∀u,H.Adj w u → H.maxDegree+2≤H.degree w+H.degree u)
    (v y : V) (hv : v∈X) (hy : y∈Xᶜ)
    (hEdge : ∃w∈Xᶜ.erase y,H.Adj v w) :
    internalEdges H (insert y (X.erase v))≤H.maxDegree*((insert y (X.erase v)).card/2) := by
  have hCut:=one_core_omission_cut_lower H X hInd hVal v y hv hy hEdge
  have hyNot:y∉X.erase v:=fun h=>(mem_compl.mp hy) (mem_erase.mp h).2
  have hCard:(insert y (X.erase v)).card=X.card:=by
    rw [card_insert_of_notMem hyNot,card_erase_of_mem hv]
    have hp:0<X.card:=card_pos.mpr ⟨v,hv⟩
    omega
  have hS:Odd (insert y (X.erase v)).card:=by rwa [hCard]
  apply (odd_internal_bound_iff_cut_deficit H H.maxDegree H.degree_le_maxDegree _ hS).mpr
  omega

/-- In the zero-edge branch, a one-unit degree comparison suffices.
The last unit is recovered by odd-set parity (Lemma 3.11). -/
theorem one_core_omission_nonoverfull_of_degree (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (hOdd : Odd X.card) (hInd : H.IsIndepSet (↑(Xᶜ):Set V))
    (v y : V) (hv : v∈X) (hy : y∈Xᶜ)
    (hNoEdge : ∀w∈Xᶜ.erase y,¬H.Adj v w)
    (hDegree : H.degree y≤H.degree v+1) :
    internalEdges H (insert y (X.erase v))≤H.maxDegree*((insert y (X.erase v)).card/2) := by
  let S:=insert y (X.erase v)
  have hvOff:v∈Sᶜ:=by
    have hne:v≠y:=fun he=>(mem_compl.mp hy) (he ▸ hv)
    simp only [S,mem_compl,mem_insert,mem_erase]
    tauto
  have hComp:Sᶜ=insert v (Xᶜ.erase y):=by
    ext w
    have hyX:y∉X:=mem_compl.mp hy
    by_cases hwv:w=v <;> by_cases hwy:w=y <;> simp_all [S]
  have hIndComp:H.IsIndepSet (↑(Sᶜ):Set V):=by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab hAdj
    rw [hComp] at ha hb
    rcases mem_insert.mp ha with he|ha
    · subst a
      rcases mem_insert.mp hb with he|hb
      · exact hab he.symm
      · exact hNoEdge b hb hAdj
    · rcases mem_insert.mp hb with he|hb
      · subst b
        exact hNoEdge a ha hAdj.symm
      · exact hInd (mem_erase.mp ha).2 (mem_erase.mp hb).2 hab hAdj
  have hCut:H.degree v≤cutEdges H S:=by
    rw [cut_eq_complementary_degree_sum H S hIndComp]
    exact single_le_sum (f:=fun w=>H.degree w) (fun _ _=>Nat.zero_le _) hvOff
  have hDef:H.maxDegree-H.degree y≤deficitMass H H.maxDegree S:=by
    exact single_le_sum (f:=fun w=>H.maxDegree-H.degree w)
      (fun _ _=>Nat.zero_le _) (mem_insert_self y (X.erase v))
  have hyD:=H.degree_le_maxDegree y
  have hyNot:y∉X.erase v:=fun hh=>(mem_compl.mp hy) (mem_erase.mp hh).2
  have hCard:S.card=X.card:=by
    dsimp only [S]
    rw [card_insert_of_notMem hyNot,card_erase_of_mem hv]
    have hp:0<X.card:=card_pos.mpr ⟨v,hv⟩
    omega
  have hSOdd:Odd S.card:=by rwa [hCard]
  apply (odd_internal_bound_iff_cut_deficit H H.maxDegree H.degree_le_maxDegree S hSOdd).mpr
  exact odd_budget_of_one_below H S hSOdd (by omega)

/-- A numerical degree-order interface for the complete (1,1) case.
It is intentionally a hypothesis: cleanup degree ordering must be proved
for the state being used, rather than inferred from the original graph. -/
theorem one_core_omission_nonoverfull (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (hOdd : Odd X.card) (hInd : H.IsIndepSet (↑(Xᶜ):Set V))
    (hVal : ∀w∈Xᶜ,∀u,H.Adj w u → H.maxDegree+2≤H.degree w+H.degree u)
    (v y : V) (hv : v∈X) (hy : y∈Xᶜ)
    (hDegree : H.degree y≤H.degree v+1) :
    internalEdges H (insert y (X.erase v))≤H.maxDegree*((insert y (X.erase v)).card/2) := by
  by_cases hEdge:∃w∈Xᶜ.erase y,H.Adj v w
  · exact one_core_omission_nonoverfull_of_edge H X hOdd hInd hVal v y hv hy hEdge
  · apply one_core_omission_nonoverfull_of_degree H X hOdd hInd v y hv hy _ hDegree
    intro w hw hAdj
    exact hEdge ⟨w,hw,hAdj⟩

end OverfullWork.PaperOneCoreCut
