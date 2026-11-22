module

public import OverfullWork.PaperOneCoreCut

@[expose] public section


/-! # The complete (1,1) case for a critical-source matching round

Before cleanup, source VAL loses at most two degree units. A nonmaximum
omitted vertex gives a cut of size at least Delta-1. If it is maximum,
only the two selected complementary vertices can have degree one; the
cut loses at most two, and the included complementary vertex contributes
one unit of deficit. Odd-set parity finishes both cases. Bounds transfer
to the actual cleanup by edge deletion at fixed maximum degree.

This is a local use of VAL and the deficiency/parity arguments in CMS
Claim 4.5. It does not assert that later class-two states are critical.
-/
namespace OverfullWork.PaperOneCoreRoundPreservation
open SimpleGraph Finset OddCutDeficit MatchingOddDeficiency InducedEdgeExchange
open NormalizedAlmostStoppingRun LargeCentreMatchingStep PaperTopDegreeMatching PaperOneCoreCut
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem cut_insert_independent_one_below (H : SimpleGraph V) [DecidableRel H.Adj]
    (Z : Finset V) (v : V) (hv : v∉Z) (hInd : H.IsIndepSet (Z:Set V))
    (hEdge : ∃w∈Z,H.Adj v w) (hNonmax : H.degree v<H.maxDegree)
    (hVal : ∀w∈Z,H.Adj v w → H.maxDegree+1≤H.degree v+H.degree w) :
    H.maxDegree≤cutEdges H (insert v Z)+1 := by
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
  have hValSum:a*(H.maxDegree+1)≤a*H.degree v+(∑w∈A,H.degree w):=by
    calc
      _ = ∑_w∈A,(H.maxDegree+1) := by simp [a]
      _ ≤ ∑w∈A,(H.degree v+H.degree w) := by
        apply sum_le_sum
        intro w hw
        exact hVal w (hASub hw) ((mem_neighborFinset H v w).mp (mem_filter.mp hw).1)
      _ = _ := by rw [sum_add_distrib];simp [a]
  have hGap:H.degree v+1+(H.maxDegree-H.degree v-1)=H.maxDegree:=by omega
  have hMul:H.maxDegree-H.degree v-1≤a*(H.maxDegree-H.degree v-1):=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (H.maxDegree-H.degree v-1) hAPos
  have hDist:a*H.degree v+a+a*(H.maxDegree-H.degree v-1)=a*H.maxDegree:=by
    nlinarith only [congrArg (fun t=>a*t) hGap]
  nlinarith only [hCut,hSum,hValSum,hGap,hMul,hDist]

theorem cut_insert_independent_two_exceptions (H : SimpleGraph V) [DecidableRel H.Adj]
    (Z : Finset V) (v p q : V) (hv : v∉Z) (hInd : H.IsIndepSet (Z:Set V))
    (hDegrees : ∀w∈Z,H.Adj v w → 2≤H.degree w+(if w=p ∨ w=q then 1 else 0)) :
    H.degree v≤cutEdges H (insert v Z)+2 := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel H.Adj)
    (fun a b=>Classical.propDecidable (H.Adj a b)))
  let A:=Plantholt.nbIn H Z v
  have hASub:A⊆Z:=by intro w hw;exact (mem_filter.mp hw).2
  have hInternal:internalEdges H (insert v Z)=A.card:=by
    rw [internal_edges_insert H Z v hv,internal_zero_of_independent H Z hInd,Nat.zero_add]
  have hCut:=internal_cut_identity H (insert v Z)
  rw [hInternal,sum_insert hv] at hCut
  have hSum:(∑w∈A,H.degree w)≤∑w∈Z,H.degree w:=
    sum_le_sum_of_subset_of_nonneg hASub (fun _ _ _=>Nat.zero_le _)
  have hAllowance:(∑w∈A,if w=p ∨ w=q then 1 else 0)≤2:=by
    have hPoint:∀w∈A,(if w=p ∨ w=q then 1 else 0)≤
        (if w=p then 1 else 0)+(if w=q then 1 else 0):=by
      intro w _
      by_cases hp:w=p <;> by_cases hq:w=q <;> simp [hp,hq]
    have hh:=sum_le_sum hPoint
    rw [sum_add_distrib] at hh
    have hP:(∑w∈A,if w=p then 1 else 0)≤1:=by
      simp only [sum_ite_eq']
      split_ifs <;>omega
    have hQ:(∑w∈A,if w=q then 1 else 0)≤1:=by
      simp only [sum_ite_eq']
      split_ifs <;>omega
    omega
  have hLower:2*A.card≤(∑w∈A,H.degree w)+(∑w∈A,if w=p ∨ w=q then 1 else 0):=by
    calc
      _ = ∑_w∈A,2 := by simp [Nat.mul_comm]
      _ ≤ ∑w∈A,(H.degree w+(if w=p ∨ w=q then 1 else 0)) := by
        apply sum_le_sum
        intro w hw
        exact hDegrees w (hASub hw) ((mem_neighborFinset H v w).mp (mem_filter.mp hw).1)
      _ = _ := sum_add_distrib
  omega

/-- A finite numerical interface, with no residual no-overfull premise. -/
theorem one_core_nonoverfull_from_source_bounds (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (hOdd : Odd X.card) (hInd : H.IsIndepSet (↑(Xᶜ):Set V))
    (v w p q : V) (hv : v∈X) (hw : w∈Xᶜ)
    (hNonmax : H.degree w<H.maxDegree) (hOrder : H.degree w≤H.degree v+1)
    (hVal : ∀u∈Xᶜ.erase w,H.Adj v u → H.maxDegree+1≤H.degree v+H.degree u)
    (hDegrees : ∀u∈Xᶜ.erase w,H.Adj v u → 2≤H.degree u+(if u=p ∨ u=q then 1 else 0)) :
    internalEdges H (insert w (X.erase v))≤H.maxDegree*((insert w (X.erase v)).card/2) := by
  by_cases hEdge:∃u∈Xᶜ.erase w,H.Adj v u
  swap
  · apply one_core_omission_nonoverfull_of_degree H X hOdd hInd v w hv hw _ hOrder
    intro u hu hAdj
    exact hEdge ⟨u,hu,hAdj⟩
  let S:=insert w (X.erase v)
  let Z:=Xᶜ.erase w
  have hvNot:v∉Z:=by simp only [Z,mem_erase,mem_compl];tauto
  have hZInd:H.IsIndepSet (Z:Set V):=by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab hAdj
    exact hInd (mem_erase.mp ha).2 (mem_erase.mp hb).2 hab hAdj
  have hComplement:Sᶜ=insert v Z:=by
    ext u
    have hwX:w∉X:=mem_compl.mp hw
    by_cases huv:u=v <;> by_cases huw:u=w <;> simp_all [S,Z]
  have hwNot:w∉X.erase v:=fun hh=>(mem_compl.mp hw) (mem_erase.mp hh).2
  have hCard:S.card=X.card:=by
    dsimp only [S]
    rw [card_insert_of_notMem hwNot,card_erase_of_mem hv]
    have hp:0<X.card:=card_pos.mpr ⟨v,hv⟩
    omega
  have hSOdd:Odd S.card:=by rwa [hCard]
  have hNear:H.maxDegree≤cutEdges H S+deficitMass H H.maxDegree S+1:=by
    by_cases hvMax:H.degree v=H.maxDegree
    · have hCut:=cut_insert_independent_two_exceptions H Z v p q hvNot hZInd hDegrees
      rw [←hComplement,NearTightOddSetGeometry.cutEdges_compl,hvMax] at hCut
      have hDef:H.maxDegree-H.degree w≤deficitMass H H.maxDegree S:=by
        exact single_le_sum (f:=fun u=>H.maxDegree-H.degree u)
          (fun _ _=>Nat.zero_le _) (mem_insert_self w (X.erase v))
      omega
    · have hvLess:H.degree v<H.maxDegree:=lt_of_le_of_ne (H.degree_le_maxDegree v) hvMax
      have hCut:=cut_insert_independent_one_below H Z v hvNot hZInd hEdge hvLess hVal
      rw [←hComplement,NearTightOddSetGeometry.cutEdges_compl] at hCut
      omega
  exact (odd_internal_bound_iff_cut_deficit H H.maxDegree H.degree_le_maxDegree S hSOdd).mpr
    (odd_budget_of_one_below H S hSOdd hNear)

/-- All (1,1) sets in the actual first round are non-overfull. Source
criticality supplies VAL and minimum degree two; the residual is not
assumed critical. The pair selection supplies complementary nonmaximum. -/
theorem one_core_round_nonoverfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hD : 4≤G.maxDegree) (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z)
    (v w : V) (hv : v∈c.set) (hw : w∈c.setᶜ) :
    internalEdges (G\r.matching) (insert w (c.set.erase v))≤
      (G\r.matching).maxDegree*((insert w (c.set.erase v)).card/2) := by
  let R:=G\r.matching
  have hSum:∀u,R.degree u+r.matching.degree u=G.degree u:=by
    intro u
    simpa only [R,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original u
  have hDrop:R.maxDegree=G.maxDegree-1:=by
    simpa only [R,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  have hNonmax:R.degree w<R.maxDegree:=by
    simpa only [R,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using
      residue_complement_nonmaximum G hc c hx hLarge hD hTop r w hw
  have hInd:R.IsIndepSet (↑(c.setᶜ):Set V):=by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab hAdj
    exact c.independent (mem_compl.mp ha) (mem_compl.mp hb) hab hAdj.1
  apply one_core_nonoverfull_from_source_bounds R c.set c.odd hInd v w y z hv hw hNonmax
  · have hOrder:=c.ordered w hw v hv
    have hV:=hSum v
    have hW:=hSum w
    have hOne:=r.degree_le_one v
    omega
  · intro u hu hAdj
    have hVAL:=Overfull.deg_add hc hAdj.1
    have hV:=hSum v
    have hU:=hSum u
    have hOneV:=r.degree_le_one v
    have hOneU:=r.degree_le_one u
    omega
  · intro u hu _
    have hTwo:=OddLowSmallCases.critical_two_le_degree G hc u
    have hU:=hSum u
    rw [r.complementary_degrees u (mem_erase.mp hu).2] at hU
    split_ifs at hU ⊢ <;>omega

theorem one_core_round_nonoverfull_after_cleanup (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hD : 4≤G.maxDegree) (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z)
    (hLe : H≤G\r.matching) (hMax : H.maxDegree=(G\r.matching).maxDegree)
    (v w : V) (hv : v∈c.set) (hw : w∈c.setᶜ) :
    internalEdges H (insert w (c.set.erase v))≤H.maxDegree*((insert w (c.set.erase v)).card/2) := by
  rw [hMax]
  exact (internal_edges_le_of_le (G\r.matching) H hLe _).trans
    (one_core_round_nonoverfull G hc c hx hLarge hD hTop r v w hv hw)

theorem one_omission_geometry (X S : Finset V) (hX : Odd X.card) (hS : Odd S.card)
    (hOne : (X\S).card=1) (hFew : (S∩Xᶜ).card≤2) :
    ∃v∈X,∃w∈Xᶜ,S=insert w (X.erase v) := by
  obtain ⟨v,hMissing⟩:=card_eq_one.mp hOne
  have hPartitionX:=card_sdiff_add_card_inter X S
  have hPartitionS:=card_sdiff_add_card_inter S X
  have hExtraEq:S\X=S∩Xᶜ:=by ext u;simp
  have hInter:(S∩X).card=(X∩S).card:=by rw [inter_comm]
  have hExtra:(S\X).card=1:=by
    rw [hExtraEq] at hPartitionS ⊢
    obtain ⟨a,ha⟩:=hX
    obtain ⟨b,hb⟩:=hS
    omega
  obtain ⟨w,hAdded⟩:=card_eq_one.mp hExtra
  have hv:v∈X\S:=by rw [hMissing];simp
  have hw:w∈S\X:=by rw [hAdded];simp
  refine ⟨v,(mem_sdiff.mp hv).1,w,mem_compl.mpr (mem_sdiff.mp hw).2,?_⟩
  ext u
  have hm:(u∈X ∧ u∉S)↔u=v:=by
    simpa only [mem_sdiff,mem_singleton] using iff_of_eq (congrArg (u∈·) hMissing)
  have ha:(u∈S ∧ u∉X)↔u=w:=by
    simpa only [mem_sdiff,mem_singleton] using iff_of_eq (congrArg (u∈·) hAdded)
  simp only [mem_insert,mem_erase]
  tauto

/-- Every odd set omitting exactly one core vertex is safe in the same
cleaned graph. Three or more Y vertices use the previously proved
budget case; otherwise parity reduces the set to the complete (1,1) case. -/
theorem one_omission_nonoverfull_after_cleanup (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hD : 4≤G.maxDegree) (hB : B≤G.maxDegree)
    (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z)
    (hLe : H≤G\r.matching) (hMax : H.maxDegree=(G\r.matching).maxDegree)
    (S : Finset V) (hOdd : Odd S.card) (hOne : (c.set\S).card=1) :
    internalEdges H S≤H.maxDegree*(S.card/2) := by
  by_cases hThree:3≤(S∩c.setᶜ).card
  · rw [hMax]
    apply (internal_edges_le_of_le (G\r.matching) H hLe S).trans
    have hBase:=PaperPairExtensionPreservation.three_complement_nonoverfull G c r
      hTop.left_mem hTop.right_mem hTop.ne hB S hOdd hThree
    have transport (d₁ d₂ : DecidableRel (G\r.matching).Adj) :
        (@internalEdges V _ _ (G\r.matching) d₁ S≤
          @SimpleGraph.maxDegree V (G\r.matching) _ d₁*(S.card/2)) →
        (@internalEdges V _ _ (G\r.matching) d₂ S≤
          @SimpleGraph.maxDegree V (G\r.matching) _ d₂*(S.card/2)):=by
      cases Subsingleton.elim d₁ d₂
      exact id
    exact transport _ _ hBase
  · obtain ⟨v,hv,w,hw,hSet⟩:=one_omission_geometry c.set S c.odd hOdd hOne (by omega)
    rw [hSet]
    exact one_core_round_nonoverfull_after_cleanup G H hc c hx hLarge hD hTop r hLe hMax v w hv hw

/-- Constructed matching and cleanup with the enlarged family of safe
sets. This is first-round preservation, not a repeated-operation theorem. -/
theorem exists_round_cleaned_with_one_omission_safe (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    (x : V) (hx : x∈c.set) (hLarge : G.degree x<(∑w∈c.setᶜ,G.degree w))
    (hxD : G.degree x<G.maxDegree) (hD : 4≤G.maxDegree) (hB : B≤G.maxDegree)
    (hNo : ¬G.HasOverfullSubgraph)
    (hMargin : Fintype.card V+2*B+c.setᶜ.card+3≤2*G.maxDegree) :
    ∃y z,IsTopPair G c.setᶜ y z ∧ ∃r : Round G c x y z,∃H : SimpleGraph V,
      MaximumNeighbourCleanup.DeletionRun c.setᶜ (G\r.matching) H ∧
      H≤G\r.matching ∧ H.maxDegree=G.maxDegree-1 ∧ ¬H.EdgeColorable H.maxDegree ∧
      H.induce (c.set:Set V)=(G\r.matching).induce (c.set:Set V) ∧
      (∀w∈c.setᶜ,H.degree w<H.maxDegree) ∧
      (∀w∈c.setᶜ,∀v,H.Adj w v → PrunedCore.neighboursIn H c.setᶜ v<H.degree w) ∧
      (∀w∈c.setᶜ,∀v,H.Adj w v → H.maxDegree+2≤H.degree w+H.degree v) ∧
      ∀S : Finset V,Odd S.card →
        (c.set⊆S ∨ 3≤(S∩c.setᶜ).card ∨ (c.set\S).card=1) →
        internalEdges H S≤H.maxDegree*(S.card/2) := by
  classical
  obtain ⟨y,z,hTop,r,H,hRun,hLe,hMax,hNC,hCore,hNonmax,hHall,hVal,hSafe⟩:=
    PaperPairExtensionPreservation.exists_top_round_cleaned_with_safe_sets G hc c
      x hx hLarge hxD hD hB hNo hMargin
  refine ⟨y,z,hTop,r,H,hRun,hLe,hMax,hNC,hCore,hNonmax,hHall,hVal,?_⟩
  intro S hOdd hCase
  rcases hCase with hCoreIn|hThree|hOne
  · exact hSafe S hOdd (Or.inl hCoreIn)
  · exact hSafe S hOdd (Or.inr hThree)
  · have hRMax:(G\r.matching).maxDegree=G.maxDegree-1:=by
      simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
        ←Nat.card_eq_fintype_card] using r.residual_maxDegree
    exact one_omission_nonoverfull_after_cleanup G H hc c hx hLarge hD hB hTop r hLe
      (hMax.trans hRMax.symm) S hOdd hOne

theorem remaining_overfull_omits_two (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V)
    (hSafe : ∀S : Finset V,Odd S.card →
      (X⊆S ∨ 3≤(S∩Xᶜ).card ∨ (X\S).card=1) →
      internalEdges H S≤H.maxDegree*(S.card/2))
    (hOF : H.HasOverfullSubgraph) :
    ∃S : Finset V,Odd S.card ∧ H.maxDegree*(S.card/2) < internalEdges H S ∧
      2≤(X\S).card ∧ (S∩Xᶜ).card≤2 ∧
      cutEdges H S+deficitMass H H.maxDegree S+2≤H.maxDegree := by
  obtain ⟨S,hOdd,hOver,hMissing,hFew,hBudget⟩:=
    PaperPairExtensionPreservation.remaining_overfull_configuration H X
      (fun S hOdd hCase=>hSafe S hOdd (hCase.imp_right Or.inl)) hOF
  have hNotZero:(X\S).card≠0:=by
    intro hz
    have hEmpty:=card_eq_zero.mp hz
    exact hMissing (sdiff_eq_empty_iff_subset.mp hEmpty)
  have hNotOne:(X\S).card≠1:=by
    intro hOne
    exact (not_lt_of_ge (hSafe S hOdd (Or.inr (Or.inr hOne)))) hOver
  exact ⟨S,hOdd,hOver,by omega,hFew,hBudget⟩

end OverfullWork.PaperOneCoreRoundPreservation
