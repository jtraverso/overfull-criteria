module

public import OverfullWork.RunLayerSystem
public import OverfullWork.EndpointBootstrapMargins

@[expose] public section


/-! # A legal bounded exchange constructed from actual robust layers

No path or layer is an input oracle: the layer system is derived from
the current good run, and its seed sets are the actual safe free
neighbors of the missing endpoints.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.PairedRoutes OverfullWork.BipartiteRobustMargin
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 32000000

theorem route_input_of_layer_connection (P : M.PartialColouring k) (A E : Finset V) (h ell : ℕ)
    (i : Fin k) (a b : V) (hab : a ≠ b)
    (ha : (P.colouring.colourGraph i).degree a=0) (hb : (P.colouring.colourGraph i).degree b=0)
    (c : LayerConnection
      ((P.colouring.colourGraph i).matchingPartner (P.colouring.colourGraph_degree_le_one i))
      (P.available.crossingSupport A)
      (univ\(P.colouring.colourGraph i).residueForbidden (P.colouring.colourGraph_degree_le_one i)
        (P.available.internalPart A) A E h) a b ell) :
    ∃ s : RouteInput P i a b,
      (∀ e, s.removed.mult e ≤ ((P.colouring.colourGraph i).goodMatching (P.available.internalPart A) A h).mult e) ∧
      (∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) ∧
      (∀ x ∈ E, s.removed.degree x=0) ∧ s.removed.edgeCount ≤ ell := by
  obtain ⟨q,hq,hLen,hCert,hSafe⟩ := P.exists_layered_simple_path A E h i c.layers c.rounds
    c.safe c.predecessors a b hab ha hb c.start c.target c.target_mem c.finish
  obtain ⟨s,hGood,hCross,hProtected,hLength⟩ := P.route_input_of_certificate A E h i a b hab ha hb q hq hCert
  refine ⟨s,hGood,hCross,hProtected,?_⟩
  have hRemoved := s.removed_count
  have hRound := c.round_bound
  omega

namespace GoodRouteRun
variable {A E : Finset V} {h ell : ℕ} {P Q : M.PartialColouring k} {n t : ℕ}

theorem exists_exchange_from_bootstrap (run : GoodRouteRun A E h ell P Q n t)
    (m r cutoff B g q : ℕ) (hA : A.card=m) (hAc : Aᶜ.card=m)
    (hRobust : IsBipartiteRobustAt M.supportGraph A r cutoff)
    (hCap : ∀ v, (P.available.internalPart A).degree v ≤ h)
    (hInitial : ∀ v, v ∉ E → (P.graph.crossingSupport A).degree v ≤ 2)
    (hMissing : ∀ v, (P.colouring.missingPalette v).card ≤ B) (i : Fin k)
    (hGain : ((Q.colouring.colourGraph i).residueForbidden (Q.colouring.colourGraph_degree_le_one i)
      (Q.available.internalPart A) A E h).card+g ≤ r)
    (hPred : q ≤ r-(2+B+h)) (hg : 0 < g) (hWindow : 2*cutoff ≤ m)
    (hRounds : m/g+3 ≤ ell) (hReserve : 4+2*ell < q)
    (a b : V) (hab : a ≠ b) (ha : (Q.colouring.colourGraph i).degree a=0)
    (hb : (Q.colouring.colourGraph i).degree b=0)
    (hStart : cutoff < (Q.bootstrapSet A
      ((Q.colouring.colourGraph i).residueForbidden (Q.colouring.colourGraph_degree_le_one i)
        (Q.available.internalPart A) A E h) a).card)
    (hEnd : cutoff < (Q.bootstrapSet A
      ((Q.colouring.colourGraph i).residueForbidden (Q.colouring.colourGraph_degree_le_one i)
        (Q.available.internalPart A) A E h) b).card) :
    ∃ s : RouteInput Q i a b,
      (∀ e, s.removed.mult e ≤ ((Q.colouring.colourGraph i).goodMatching (Q.available.internalPart A) A h).mult e) ∧
      (∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) ∧
      (∀ x ∈ E, s.removed.degree x=0) ∧ s.removed.edgeCount ≤ ell := by
  let L := Q.colouring.colourGraph i
  let hL := Q.colouring.colourGraph_degree_le_one i
  let W := L.residueForbidden hL (Q.available.internalPart A) A E h
  let U := univ\W
  let τ := L.matchingPartner hL
  let F := Q.available.crossingSupport A
  let sys := run.layerSystem m r cutoff B g q hA hAc hRobust hCap hInitial hMissing i hGain hPred
  let Da := if a ∈ A then Aᶜ else A
  let Db := if b ∈ A then Aᶜ else A
  let Sa := Q.bootstrapSet A W a
  let Sb := Q.bootstrapSet A W b
  have hDa : Da=A ∨ Da=Aᶜ := by by_cases hh : a ∈ A <;> simp [Da,hh]
  have hDb : Db=A ∨ Db=Aᶜ := by by_cases hh : b ∈ A <;> simp [Db,hh]
  have haSide : (a ∈ A ∧ Da=Aᶜ) ∨ (a ∉ A ∧ Da=A) := by
    by_cases hh : a ∈ A <;> simp [Da,hh]
  have hbSide : (b ∈ A ∧ Db=Aᶜ) ∨ (b ∉ A ∧ Db=A) := by
    by_cases hh : b ∈ A <;> simp [Db,hh]
  have hSaLow : cutoff ≤ Sa.card := Nat.le_of_lt hStart
  obtain ⟨c⟩ := exists_layer_connection sys hg hWindow ell hRounds hReserve a b Da Db Sa Sb hDa hDb
    (Q.bootstrapSet_subset_opposite A W a Da haSide) (Q.bootstrapSet_subset_opposite A W b Db hbSide)
    hSaLow hEnd
    (fun x hx => (Q.bootstrapSet_member A W a x hx).1)
    (fun y hy => ((Q.bootstrapSet_member A W b y hy).1).symm)
  exact Q.route_input_of_layer_connection A E h ell i a b hab ha hb c

end GoodRouteRun
end SimpleGraph.MultiGraph.PartialColouring
