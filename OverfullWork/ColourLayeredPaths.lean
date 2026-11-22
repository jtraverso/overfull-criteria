module

public import OverfullWork.LayeredAlternatingPaths

@[expose] public section


/-! # Layered simple paths for an actual partial coloring

The involution, good matching and free crossing graph are all derived
from the current color. Explicit predecessor reserves and the final
adjacency/counting alternatives remain visible: this theorem does not
assert that every stage of the full CMS process has paid them.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.PairedRoutes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 24000000

theorem exists_layered_simple_path (P : M.PartialColouring k) (A E : Finset V) (h : ℕ) (i : Fin k) :
    let L := P.colouring.colourGraph i
    let hL := P.colouring.colourGraph_degree_le_one i
    let W := L.residueForbidden hL (P.available.internalPart A) A E h
    let U := univ\W
    let τ := L.matchingPartner hL
    let F := P.available.crossingSupport A
    let K := (L.goodMatching (P.available.internalPart A) A h).supportGraph
    ∀ (S : ℕ → Finset V) (n : ℕ), (∀ j, j ≤ n → S j ⊆ U) →
      (∀ j, j < n → ∀ z ∈ S (j+1), 4+2*n < ((S j).filter (fun x => F.Adj (τ x) z)).card) →
      ∀ a b, a ≠ b → L.degree a=0 → L.degree b=0 →
      (∀ x ∈ S 0, F.Adj a x) → ∀ z ∈ S n,
      (F.Adj (τ z) b ∨ ∃ T : Finset V, T ⊆ U ∧ (∀ y ∈ T, F.Adj y b) ∧
        2 < (T.filter (fun y => F.Adj (τ y) (τ z))).card) →
      ∃ q : M.supportGraph.Walk a b, q.IsPath ∧ q.length ≤ 2*n+5 ∧ AlternatingCertificate τ F K U a b q.support ∧
        ∀ v ∈ q.support, v ≠ a → v ≠ b → v ∉ W := by
  let L := P.colouring.colourGraph i
  let hL := P.colouring.colourGraph_degree_le_one i
  let W := L.residueForbidden hL (P.available.internalPart A) A E h
  let U := univ\W
  let τ := L.matchingPartner hL
  let F := P.available.crossingSupport A
  let K := (L.goodMatching (P.available.internalPart A) A h).supportGraph
  dsimp only
  intro S n hLayers hSteps a b hab hMissingA hMissingB hStart z hz hFinish
  have hτ : ∀ v, τ (τ v)=v := L.matchingPartner_apply_apply hL
  have hU : ∀ v ∈ U, τ v ∈ U := by
    intro v hv
    exact mem_sdiff.mpr ⟨mem_univ _,L.matchingForbidden_closed_complement hL A
      ((P.available.internalPart A).highVertices h ∪ E) v (mem_sdiff.mp hv).2⟩
  have hNe : ∀ v ∈ U, τ v ≠ v := by
    intro v hv
    have hs := L.residueForbidden_safe_partner hL (P.available.internalPart A) A E h v (mem_sdiff.mp hv).2
    exact hs.2.1
  have hK : ∀ v ∈ U, K.Adj v (τ v) := by
    intro v hv
    have hs := L.residueForbidden_safe_partner hL (P.available.internalPart A) A E h v (mem_sdiff.mp hv).2
    change 0 < (L.goodMatching (P.available.internalPart A) A h).mult s(v,τ v)
    rw [hs.2.2.2.2.2.2.2]
    decide
  have ha : τ a=a := L.matchingPartner_fixed_of_zero hL a hMissingA
  have hb : τ b=b := L.matchingPartner_fixed_of_zero hL b hMissingB
  have hFK : F ⊔ K ≤ M.supportGraph := by
    apply sup_le
    · intro x y hxy
      have hh : P.available.mult s(x,y) ≤ M.mult s(x,y) := Nat.sub_le _ _
      change 0 < M.mult s(x,y)
      exact lt_of_lt_of_le hxy.1 hh
    · intro x y hxy
      have hGood := L.goodMatching_le (P.available.internalPart A) A h s(x,y)
      have hCol := P.colouring.col_le_mult s(x,y) i
      have hCap := P.le s(x,y)
      change 0 < (L.goodMatching (P.available.internalPart A) A h).mult s(x,y) at hxy
      change 0 < M.mult s(x,y)
      change L.mult s(x,y) ≤ P.graph.mult s(x,y) at hCol
      omega
  let f : (F ⊔ K) →g M.supportGraph := {toFun := id, map_rel' := fun hh => hFK hh}
  have lift : ∀ q : (F ⊔ K).Walk a b, q.IsPath → q.length ≤ 2*n+5 → AlternatingCertificate τ F K U a b q.support →
      (∀ v ∈ q.support, v ≠ a → v ≠ b → v ∉ W) →
      ∃ q : M.supportGraph.Walk a b, q.IsPath ∧ q.length ≤ 2*n+5 ∧ AlternatingCertificate τ F K U a b q.support ∧
        ∀ v ∈ q.support, v ≠ a → v ≠ b → v ∉ W := by
    intro q hq hLen hCertificate hSafe
    refine ⟨q.map f,hq.map (fun _ _ he => he),?_,?_,?_⟩
    · rw [Walk.length_map];exact hLen
    · have hs : (q.map f).support=q.support := by
        rw [Walk.support_map]
        change List.map id q.support=q.support
        exact List.map_id q.support
      rw [hs]
      exact hCertificate
    · intro v hv hva hvb
      rw [Walk.support_map,List.mem_map] at hv
      obtain ⟨x,hx,he⟩ := hv
      change x=v at he
      subst x
      exact hSafe v hx hva hvb
  rcases hFinish with hEnd|hTail
  · obtain ⟨r,hFirst,hr,hAvoid,hA,hPath,hLen⟩ := exists_direct_path τ hτ F K U hNe hK S n hLayers
      (fun j hj v hv => by
        have hh : 4+2*n < ((S j).filter (fun x => F.Adj (τ x) v)).card := hSteps j hj v hv
        omega) a b hab ha hb hStart z hz hEnd
    apply lift (r.close K hK a b hA hEnd) hPath (by omega)
      (r.close_certificate K hK a b hA hEnd)
    intro v hv hva hvb
    rw [r.support_close K hK a b hA hEnd] at hv
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hv
    rcases hv with hv|hv|hv
    · exact False.elim (hva hv)
    · exact (mem_sdiff.mp (r.vertices_safe hU v hv)).2
    · exact False.elim (hvb hv)
  · obtain ⟨T,hT,hLast,hTail⟩ := hTail
    obtain ⟨y,hyT,r,hFirst,hr,hAvoid,hA,hEnd,hPath,hLen⟩ := exists_extra_path τ hτ F K U hNe hK S n hLayers
      hSteps a b hab ha hb hStart z hz T hT hLast hTail
    apply lift (r.closeExtra K hK a b y (hT hyT) hA hEnd (hLast y hyT)) hPath (by omega)
      (r.closeExtra_certificate K hK a b y (hT hyT) hA hEnd (hLast y hyT))
    intro v hv hva hvb
    rw [r.support_closeExtra K hK a b y (hT hyT) hA hEnd (hLast y hyT)] at hv
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hv
    rcases hv with hv|hv|hv|hv|hv
    · exact False.elim (hva hv)
    · exact (mem_sdiff.mp (r.vertices_safe hU v hv)).2
    · subst v;exact (mem_sdiff.mp (hU y (hT hyT))).2
    · subst v;exact (mem_sdiff.mp (hT hyT)).2
    · exact False.elim (hvb hv)

end SimpleGraph.MultiGraph.PartialColouring
