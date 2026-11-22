module

public import OverfullWork.DynamicForbiddenBudget

@[expose] public section


/-! # Alternating growth after any recorded good run

The current matching and forbidden set come from the current coloring.
The deletion loss 2+B+h is derived from the initial anchor geometry,
initial missing budget and the preserved residue cap.
-/
namespace SimpleGraph.MultiGraph.PartialColouring.GoodRouteRun
open SimpleGraph Finset OverfullWork.BipartiteRobustMargin OverfullWork.PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
variable {A E : Finset V} {h ell : ℕ} {P Q : M.PartialColouring k} {n t : ℕ}
set_option maxHeartbeats 24000000

theorem dynamic_alternating_growth (run : GoodRouteRun A E h ell P Q n t)
    (r cutoff B : ℕ) (hRobust : IsBipartiteRobustAt M.supportGraph A r cutoff)
    (hCap : ∀ v, (P.available.internalPart A).degree v ≤ h)
    (hInitial : ∀ v, v ∉ E → (P.graph.crossingSupport A).degree v ≤ 2)
    (hMissing : ∀ v, (P.colouring.missingPalette v).card ≤ B) (i : Fin k) :
    let L := Q.colouring.colourGraph i
    let hL := Q.colouring.colourGraph_degree_le_one i
    let W := L.residueForbidden hL (Q.available.internalPart A) A E h
    let τ := L.matchingPartner hL
    let F := Q.graph.crossingSupport A
    ∀ D : Finset V, (D=A ∨ D=Aᶜ) → ∀ X : Finset V, X ⊆ D\W →
      cutoff ≤ X.card → X.card+cutoff ≤ D.card →
      (X.image τ).card=X.card ∧ X.image τ ⊆ D\W ∧
        alternatingStep M.supportGraph F Dᶜ W τ r (2+B+h) X ⊆ Dᶜ\W ∧
        X.card+r ≤ (alternatingStep M.supportGraph F Dᶜ W τ r (2+B+h) X).card+W.card ∧
        ∀ v ∈ alternatingStep M.supportGraph F Dᶜ W τ r (2+B+h) X,
          r-(2+B+h) ≤ (X.filter (fun x => (Q.available.crossingSupport A).Adj (τ x) v)).card := by
  let L := Q.colouring.colourGraph i
  let hL := Q.colouring.colourGraph_degree_le_one i
  let W := L.residueForbidden hL (Q.available.internalPart A) A E h
  let τ := L.matchingPartner hL
  let F := Q.graph.crossingSupport A
  dsimp only
  intro D hSide X hX hLow hHigh
  have hMate : ∀ v ∈ D\W, τ v ∈ D\W := by
    intro v hv
    have hSafe := L.residueForbidden_safe_partner hL (Q.available.internalPart A) A E h v (mem_sdiff.mp hv).2
    have hD : τ v ∈ D := by
      rcases hSide with hSide|hSide
      · rw [hSide] at hv ⊢
        exact hSafe.2.2.1.mp (mem_sdiff.mp hv).1
      · rw [hSide] at hv ⊢
        exact mem_compl.mpr (fun hm => (mem_compl.mp (mem_sdiff.mp hv).1) (hSafe.2.2.1.mpr hm))
    exact mem_sdiff.mpr ⟨hD,hSafe.1⟩
  have hF : ∀ v, v ∉ W → F.degree v ≤ 2+B+h := by
    intro v hv
    have hSafe := L.outside_matchingForbidden_facts hL A ((Q.available.internalPart A).highVertices h ∪ E) v hv
    have hvE : v ∉ E := fun he => hSafe.2.2.1 (mem_union_right _ he)
    exact run.initial_deleted_degree_budget B hCap hInitial hMissing v hvE
  have hExpand : ExpandsTo M.supportGraph D Dᶜ r cutoff := by
    rcases hSide with hSide|hSide
    · simpa only [hSide] using hRobust.1
    · simpa only [hSide,compl_compl] using hRobust.2
  have hGrow := OverfullWork.BipartiteRobustMargin.alternating_growth M.supportGraph F D Dᶜ W X τ
    r (2+B+h) cutoff hExpand hX hMate hF hLow hHigh
  refine ⟨hGrow.1,hGrow.2.1,hGrow.2.2.1,hGrow.2.2.2.1,?_⟩
  intro v hv
  have hNeighbours := hGrow.2.2.2.2 v hv
  have hvD : v ∉ D := mem_compl.mp (mem_sdiff.mp (hGrow.2.2.1 hv)).1
  have hCount := Q.free_predecessor_count D X τ (fun x hx => (mem_sdiff.mp (hMate x (hX hx))).1) v hvD
  have hCount' : neighboursIn (M.supportGraph\F) (X.image τ) v ≤
      (X.filter (fun x => (Q.available.crossingSupport A).Adj (τ x) v)).card := by
    rcases hSide with hSide|hSide
    · simpa only [hSide] using hCount
    · simpa only [hSide,crossingSupport_compl] using hCount
  exact hNeighbours.trans hCount'

end SimpleGraph.MultiGraph.PartialColouring.GoodRouteRun
