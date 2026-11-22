module

public import OverfullWork.AlternatingCertificateNormalization

@[expose] public section


/-! # Convert the actual simple alternating path to a legal copy update

The route input, copy capacities and matching properness are all proved
from the actual coloring and the path certificate. Removed copies are
good internal copies and avoid the exceptional vertices.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.PairedRoutes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 24000000

theorem route_input_of_certificate (P : M.PartialColouring k) (A E : Finset V) (h : ℕ) (i : Fin k)
    (a b : V) (hab : a ≠ b) (ha : (P.colouring.colourGraph i).degree a=0)
    (hb : (P.colouring.colourGraph i).degree b=0) (q : M.supportGraph.Walk a b) (hq : q.IsPath)
    (hc : AlternatingCertificate
      ((P.colouring.colourGraph i).matchingPartner (P.colouring.colourGraph_degree_le_one i))
      (P.available.crossingSupport A) ((P.colouring.colourGraph i).goodMatching (P.available.internalPart A) A h).supportGraph
      (univ\(P.colouring.colourGraph i).residueForbidden (P.colouring.colourGraph_degree_le_one i)
        (P.available.internalPart A) A E h) a b q.support) :
    ∃ s : RouteInput P i a b,
      (∀ e, s.removed.mult e ≤ ((P.colouring.colourGraph i).goodMatching (P.available.internalPart A) A h).mult e) ∧
      (∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) ∧
      (∀ x ∈ E, s.removed.degree x=0) ∧ q.length=2*s.rounds+3 := by
  let L := P.colouring.colourGraph i
  let hL := P.colouring.colourGraph_degree_le_one i
  let W := L.residueForbidden hL (P.available.internalPart A) A E h
  let U := univ\W
  let τ := L.matchingPartner hL
  let F := P.available.crossingSupport A
  let K := (L.goodMatching (P.available.internalPart A) A h).supportGraph
  have hτ : ∀ x, τ (τ x)=x := L.matchingPartner_apply_apply hL
  have hU : ∀ x ∈ U, τ x ∈ U := by
    intro x hx
    exact mem_sdiff.mpr ⟨mem_univ _,L.matchingForbidden_closed_complement hL A
      ((P.available.internalPart A).highVertices h ∪ E) x (mem_sdiff.mp hx).2⟩
  obtain ⟨z,n,r,hStart,hEnd,hSupport⟩ := hc.normalize hτ hU
  have hSimple : (a :: (r.vertices ++ [b])).Nodup := by
    rw [←hSupport]
    exact hq.support_nodup
  have hNe : ∀ x ∈ U, x ≠ τ x := by
    intro x hx
    have hs := L.residueForbidden_safe_partner hL (P.available.internalPart A) A E h x (mem_sdiff.mp hx).2
    exact hs.2.1.symm
  have hPairs : ∀ x ∈ U, L.mult s(x,τ x)=1 := by
    intro x hx
    have hs := L.outside_matchingForbidden_facts hL A ((P.available.internalPart A).highVertices h ∪ E) x (mem_sdiff.mp hx).2
    exact L.matchingPartner_adj hL x hs.1
  let s : RouteInput P i a b := {
    mate := τ, freeGraph := F, eligible := U, last := z, rounds := n, route := r,
    first_free := hStart, last_free := hEnd, pair_ne := hNe, pairs := hPairs,
    free := fun _ _ hxy => hxy.1, simple := hSimple, distinct := hab,
    first_missing := ha, last_missing := hb
  }
  refine ⟨s,?_,?_,?_,?_⟩
  · apply r.removed_le_of_pairs hNe s.route_nodup
    intro x hx
    have he := hc.1 x hx
    change 0 < (L.goodMatching (P.available.internalPart A) A h).mult s(x,τ x) at he
    exact he
  · intro x y hSame
    by_contra hn
    have hp : 0 < s.added.mult s(x,y) := by omega
    obtain ⟨u,v,huv,heq⟩ := r.added_positive_free a b hStart hEnd s(x,y) hp
    rcases Sym2.eq_iff.mp heq with ⟨hxu,hyv⟩|⟨hxv,hyu⟩
    · subst u;subst v;exact huv.2 hSame
    · subst u;subst v;exact huv.2 hSame.symm
  · intro x hx
    rw [s.removed_degree]
    apply List.count_eq_zero_of_not_mem
    intro hxR
    have hxU := r.vertices_safe hU x hxR
    have hf := L.outside_matchingForbidden_facts hL A ((P.available.internalPart A).highVertices h ∪ E)
      x (mem_sdiff.mp hxU).2
    exact hf.2.2.1 (mem_union_right _ hx)
  · have hl := congrArg List.length hSupport
    rw [Walk.length_support,List.length_cons,List.length_append,r.length_vertices] at hl
    simp only [List.length_cons,List.length_nil] at hl
    change q.length=2*n+3
    omega

end SimpleGraph.MultiGraph.PartialColouring
