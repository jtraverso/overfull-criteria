module

public import OverfullWork.JointCutNormalizationTools

@[expose] public section


/-! # Simultaneous degree ordering and maximum-neighbour cleanup

A finite minimum of the complementary degree sum is taken over actual
class-two subgraphs and independent cuts of the original size. Bad-edge
deletion preserves all admissibility requirements and strictly lowers
that sum. Once no bad edge exists, weak VAL makes every degree-inversion
swap independent; that swap lowers the same objective. Thus both desired
conditions hold together, without assuming criticality or readiness of
an arbitrary previously cleaned graph. The core may change during swaps.
-/
namespace OverfullWork.JointCutNormalization
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open MaximumNeighbourCleanup FixedCoreBudgetTransport JointCutNormalizationTools CleanedSourceVAL
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 10000000

structure Admissible (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (H : SimpleGraph V) [DecidableRel H.Adj] (Y : Finset V) (L : ℕ := 0) : Prop where
  le_original : H≤G
  maximum : H.maxDegree=G.maxDegree
  uncolourable : ¬H.EdgeColorable H.maxDegree
  complement_card : Y.card=Xᶜ.card
  independent : H.IsIndepSet (Y:Set V)
  nonmaximum : ∀w∈Y,H.degree w<H.maxDegree
  light_pairs : ∀u∈Y,∀v∈Y,u≠v → H.degree u+H.degree v+L<H.maxDegree+2
  budget : deficitMass H H.maxDegree Yᶜ+(∑v∈Y,H.degree v)≤
    deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)

theorem exists_joint_normalization_with_gap (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNC : ¬G.EdgeColorable G.maxDegree) (hNo : ¬G.HasOverfullSubgraph)
    (X : Finset V) (hOdd : Odd X.card) (B K L : ℕ) (hK : Xᶜ.card≤K)
    (hInd : G.IsIndepSet (↑(Xᶜ):Set V))
    (hNonmax : ∀w∈Xᶜ,G.degree w<G.maxDegree)
    (hPairs : ∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v+L<G.maxDegree+2)
    (hBudget : deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B) :
    ∃H : SimpleGraph V,H≤G ∧ H.maxDegree=G.maxDegree ∧ ¬H.EdgeColorable H.maxDegree ∧
      ¬H.HasOverfullSubgraph ∧ ∃c : Certificate H B K,
        c.setᶜ.card=Xᶜ.card ∧ IsReady H c.setᶜ ∧
        deficitMass H H.maxDegree c.set+(∑v∈c.setᶜ,H.degree v)≤
          deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v) ∧
        (∀u∈c.setᶜ,∀v∈c.setᶜ,u≠v → H.degree u+H.degree v+L<H.maxDegree+2) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b=>Classical.propDecidable (G.Adj a b)))
  have hInit:Admissible G X G Xᶜ L:=by
    refine ⟨le_rfl,rfl,hNC,rfl,hInd,hNonmax,hPairs,?_⟩
    simp only [compl_compl,le_refl]
  have hex:∃m:ℕ,∃H:SimpleGraph V,∃Y:Finset V,
      Admissible G X H Y L ∧ (∑v∈Y,H.degree v)=m:=
    ⟨∑v∈Xᶜ,G.degree v,G,Xᶜ,hInit,rfl⟩
  obtain ⟨H,Y,a,hCount⟩:=Nat.find_spec hex
  have hFinal:∀w∈Y,∀v,H.Adj w v →
      H.maxDegree+1≤H.degree w+PrunedCore.neighboursIn H (maximumVertices H) v:=by
    intro w hw v hEdge
    by_contra hn
    have hBad:H.degree w+PrunedCore.neighboursIn H (maximumVertices H) v≤H.maxDegree:=by omega
    let J:=H.deleteEdges {s(w,v)}
    let _ : DecidableRel J.Adj:=fun u v=>Classical.propDecidable (J.Adj u v)
    have hLe:J≤H:=deleteEdges_le _
    have hNCPalette:¬J.EdgeColorable H.maxDegree:=by
      intro hCol
      exact a.uncolourable ((MaximumNeighbourCleanup.colourable_iff_delete_bad_edge H
        (a.nonmaximum w hw) hBad).mpr hCol)
    have hMax:J.maxDegree=H.maxDegree:=Critical.maxDegree_eq_of_obstruction hLe hNCPalette
    have hNCJ:¬J.EdgeColorable J.maxDegree:=by rwa [hMax]
    have hIndJ:J.IsIndepSet (Y:Set V):=independent_of_le H J Y a.independent hLe
    have hNonmaxJ:∀u∈Y,J.degree u<J.maxDegree:=by
      intro u hu
      have hDeg:=J.degree_le_of_le hLe (v:=u)
      have hOld:=a.nonmaximum u hu
      omega
    have hPairsJ:∀u∈Y,∀v∈Y,u≠v → J.degree u+J.degree v+L<J.maxDegree+2:=by
      intro u hu v hv huv
      have hU:=J.degree_le_of_le hLe (v:=u)
      have hV:=J.degree_le_of_le hLe (v:=v)
      have hOld:=a.light_pairs u hu v hv huv
      omega
    have hCore:J.induce (↑(Yᶜ):Set V)=H.induce (↑(Yᶜ):Set V):=by
      have hSet:(↑(Yᶜ):Set V)=(↑Y:Set V)ᶜ:=by
        ext u
        simp only [mem_coe,mem_compl,Set.mem_compl_iff]
      rw [hSet]
      exact LowSetEdgePreprocessing.induce_compl_delete_bad_edge H Y (x:=v) hw
    have hBudgetEq:=budget_eq_of_fixed_core H J Yᶜ hCore hMax
      (by simpa only [compl_compl] using a.independent)
      (by simpa only [compl_compl] using hIndJ)
    simp only [compl_compl] at hBudgetEq
    have aJ:Admissible G X J Y L:=⟨hLe.trans a.le_original,hMax.trans a.maximum,hNCJ,
      a.complement_card,hIndJ,hNonmaxJ,hPairsJ,hBudgetEq.le.trans a.budget⟩
    have hStrict:(∑u∈Y,J.degree u)<∑u∈Y,H.degree u:=by
      simpa only [J,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        degree_sum_strictly_decreases_on_deletion H Y w v hw hEdge
    have hLt:(∑u∈Y,J.degree u)<Nat.find hex:=hStrict.trans_eq hCount
    exact Nat.find_min hex hLt ⟨J,Y,aJ,rfl⟩
  have hReady:IsReady H Y:=⟨a.nonmaximum,hFinal⟩
  have hLight (u : V) (hu : u ∈ Y) (v : V) (hv : v ∈ Y) (hne : u ≠ v) :
      H.degree u+H.degree v<H.maxDegree+2 := by
    have h := a.light_pairs u hu v hv hne
    omega
  have hOrdered:∀y∈Y,∀x∉Y,H.degree y≤H.degree x:=by
    intro y hy x hx
    by_contra hn
    have hInv:H.degree x<H.degree y:=by omega
    let Z:=insert x (Y.erase y)
    obtain ⟨hCard,hStrict⟩:=swap_card_and_sum H Y y x hy hx hInv
    have hIndZ:H.IsIndepSet (Z:Set V):=independent_swap H Y a.independent hLight
      (weak_VAL H Y hReady) y x hy hx hInv
    have hNonmaxZ:∀u∈Z,H.degree u<H.maxDegree:=by
      intro u hu
      rcases mem_insert.mp hu with he|hu
      · have hh:=a.nonmaximum y hy
        subst u
        omega
      · exact a.nonmaximum u (mem_erase.mp hu).2
    have hPairsZ : ∀ u ∈ Z,∀ v ∈ Z,u ≠ v → H.degree u+H.degree v+L<H.maxDegree+2 := by
      have hOriginal (u : V) (hu : u ∈ Y) (v : V) (hv : v ∈ Y) (hNe : u ≠ v) :
          H.degree u+H.degree v<H.maxDegree+2-L := by
        have h := a.light_pairs u hu v hv hNe
        omega
      intro u hu v hv huv
      have h := DegreeOrderedIndependentCut.pair_bound_insert_erase (fun v=>H.degree v)
        (H.maxDegree+2-L) Y hOriginal hy hInv u hu v hv huv
      omega
    have hBudgetZ:=budget_mono_of_equal_card_and_sum H Y Z hCard hStrict.le
    have aZ:Admissible G X H Z L:=⟨a.le_original,a.maximum,a.uncolourable,hCard.trans a.complement_card,
      hIndZ,hNonmaxZ,hPairsZ,hBudgetZ.trans a.budget⟩
    have hLt:(∑v∈Z,H.degree v)<Nat.find hex:=hStrict.trans_eq hCount
    exact Nat.find_min hex hLt ⟨H,Z,aZ,rfl⟩
  have hCoreCard:Yᶜ.card=X.card:=by
    have hY:=card_add_card_compl Y
    have hX:=card_add_card_compl X
    have hc:=a.complement_card
    omega
  let c : Certificate H B K:={
    set:=Yᶜ
    odd:=by rwa [hCoreCard]
    complement_small:=by simpa only [compl_compl] using a.complement_card.le.trans hK
    budget:=by
      have hb:=a.budget.trans hBudget
      simpa only [compl_compl,a.maximum] using hb
    ordered:=by
      intro y hy x hx
      exact hOrdered y (by simpa only [compl_compl] using hy) x (mem_compl.mp hx)
    light_pairs:=by simpa only [compl_compl] using hLight
    independent:=by simpa only [coe_compl,compl_compl] using a.independent }
  have hNoH:¬H.HasOverfullSubgraph:=Critical.no_overfull_of_copy (Copy.ofLE H G a.le_original) a.maximum hNo
  refine ⟨H,a.le_original,a.maximum,a.uncolourable,hNoH,c,?_,?_,?_,?_⟩
  · simpa only [c,compl_compl] using a.complement_card
  · simpa only [c,compl_compl] using hReady
  · simpa only [c,compl_compl] using a.budget
  · simpa only [c,compl_compl] using a.light_pairs

theorem exists_joint_normalization (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNC : ¬G.EdgeColorable G.maxDegree) (hNo : ¬G.HasOverfullSubgraph)
    (X : Finset V) (hOdd : Odd X.card) (B K : ℕ) (hK : Xᶜ.card≤K)
    (hInd : G.IsIndepSet (↑(Xᶜ):Set V))
    (hNonmax : ∀w∈Xᶜ,G.degree w<G.maxDegree)
    (hPairs : ∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2)
    (hBudget : deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B) :
    ∃H : SimpleGraph V,H≤G ∧ H.maxDegree=G.maxDegree ∧ ¬H.EdgeColorable H.maxDegree ∧
      ¬H.HasOverfullSubgraph ∧ ∃c : Certificate H B K,
        c.setᶜ.card=Xᶜ.card ∧ IsReady H c.setᶜ ∧
        deficitMass H H.maxDegree c.set+(∑v∈c.setᶜ,H.degree v)≤
          deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v) := by
  obtain ⟨H,hLe,hMax,hNC',hNo',c,hSize,hReady,hBudget',_⟩ :=
    exists_joint_normalization_with_gap G hNC hNo X hOdd B K 0 hK hInd hNonmax
      (by simpa only [Nat.add_zero] using hPairs) hBudget
  exact ⟨H,hLe,hMax,hNC',hNo',c,hSize,hReady,hBudget'⟩

end OverfullWork.JointCutNormalization
