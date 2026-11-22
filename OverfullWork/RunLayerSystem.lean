module

public import OverfullWork.LayerConnection
public import OverfullWork.DynamicAlternatingGrowth

@[expose] public section


/-! # Alternating layer system derived from a recorded recoloring run

The operator, matching, safe set and free edges all come from the current
partial coloring. Growth uses the preserved deletion budget; predecessor
counts hold for every advancing set, including the short terminal layer.
-/
namespace SimpleGraph.MultiGraph.PartialColouring.GoodRouteRun
open SimpleGraph Finset OverfullWork.PairedRoutes OverfullWork.BipartiteRobustMargin
open OverfullWork.PrunedCore OverfullWork.RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
variable {A E : Finset V} {h ell : ℕ} {P Q : M.PartialColouring k} {n t : ℕ}
set_option maxHeartbeats 24000000

noncomputable def layerSystem (run : GoodRouteRun A E h ell P Q n t)
    (m r cutoff B g q : ℕ) (hA : A.card=m) (hAc : Aᶜ.card=m)
    (hRobust : IsBipartiteRobustAt M.supportGraph A r cutoff)
    (hCap : ∀ v, (P.available.internalPart A).degree v ≤ h)
    (hInitial : ∀ v, v ∉ E → (P.graph.crossingSupport A).degree v ≤ 2)
    (hMissing : ∀ v, (P.colouring.missingPalette v).card ≤ B) (i : Fin k)
    (hGain : ((Q.colouring.colourGraph i).residueForbidden (Q.colouring.colourGraph_degree_le_one i)
      (Q.available.internalPart A) A E h).card+g ≤ r)
    (hPred : q ≤ r-(2+B+h)) :
    LayerSystem ((Q.colouring.colourGraph i).matchingPartner (Q.colouring.colourGraph_degree_le_one i))
      (Q.available.crossingSupport A)
      (univ\(Q.colouring.colourGraph i).residueForbidden (Q.colouring.colourGraph_degree_le_one i)
        (Q.available.internalPart A) A E h) A m cutoff g q := by
  let L := Q.colouring.colourGraph i
  let hL := Q.colouring.colourGraph_degree_le_one i
  let W := L.residueForbidden hL (Q.available.internalPart A) A E h
  let U := univ\W
  let τ := L.matchingPartner hL
  let F := Q.graph.crossingSupport A
  have hMate : ∀ x ∈ U, τ x ∈ U := by
    intro x hx
    have hh := L.residueForbidden_safe_partner hL (Q.available.internalPart A) A E h x (mem_sdiff.mp hx).2
    exact mem_sdiff.mpr ⟨mem_univ _,hh.1⟩
  have hSide : ∀ x ∈ U, (x ∈ A ↔ τ x ∈ A) := by
    intro x hx
    exact (L.residueForbidden_safe_partner hL (Q.available.internalPart A) A E h x (mem_sdiff.mp hx).2).2.2.1
  have hDU : ∀ D X : Finset V, X ⊆ D ∩ U → X ⊆ D\W := by
    intro D X hX x hx
    obtain ⟨hxD,hxU⟩ := mem_inter.mp (hX hx)
    exact mem_sdiff.mpr ⟨hxD,(mem_sdiff.mp hxU).2⟩
  refine {
    card_part := hA, card_compl := hAc,
    involutive := L.matchingPartner_apply_apply hL,
    closed := hMate, same_side := hSide,
    advance := fun D X => alternatingStep M.supportGraph F Dᶜ W τ r (2+B+h) X,
    subset := ?_, growth := ?_, predecessors := ?_
  }
  · intro D hD X hX z hz
    obtain ⟨hzN,hzW⟩ := mem_sdiff.mp hz
    exact mem_inter.mpr ⟨(mem_filter.mp hzN).1,mem_sdiff.mpr ⟨mem_univ _,hzW⟩⟩
  · intro D hD X hX hLow hHigh
    have hDCard : D.card=m := by rcases hD with rfl|rfl;exact hA;exact hAc
    have hh := run.dynamic_alternating_growth r cutoff B hRobust hCap hInitial hMissing i
      D hD X (hDU D X hX) hLow (by omega)
    have hgrow := hh.2.2.2.1
    change X.card+r ≤ (alternatingStep M.supportGraph F Dᶜ W τ r (2+B+h) X).card+W.card at hgrow
    change W.card+g ≤ r at hGain
    omega
  · intro D hD X hX z hz
    have hzN := (mem_filter.mp (mem_sdiff.mp hz).1).2
    have hMateD : ∀ x ∈ X, τ x ∈ D := by
      intro x hx
      have hxD := (mem_inter.mp (hX hx)).1
      have hxU := (mem_inter.mp (hX hx)).2
      rcases hD with rfl|rfl
      · exact (hSide x hxU).mp hxD
      · exact mem_compl.mpr (fun he => (mem_compl.mp hxD) ((hSide x hxU).mpr he))
    have hzD : z ∉ D := mem_compl.mp (mem_filter.mp (mem_sdiff.mp hz).1).1
    have hc := Q.free_predecessor_count D X τ hMateD z hzD
    have hc' : neighboursIn (M.supportGraph\F) (X.image τ) z ≤
        (X.filter (fun x => (Q.available.crossingSupport A).Adj (τ x) z)).card := by
      rcases hD with hD|hD
      · simpa only [hD] using hc
      · simpa only [hD,crossingSupport_compl] using hc
    exact hPred.trans (hzN.trans hc')

end SimpleGraph.MultiGraph.PartialColouring.GoodRouteRun
