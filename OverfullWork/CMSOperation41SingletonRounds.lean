module

public import OverfullWork.CMSOperation41SmallPrescriptions

@[expose] public section


/-! Concrete singleton choices for S2.1 and S2.2. The only projection
vertices that need a free appearance are the exceptional leaves. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2100000 in
theorem exists_capped_singleton_round_with_leaf_positions
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Z : Finset V)
    {w a b : V} (hw : w ∈ U) (hwa : G.Adj w a) (hwb : w ≠ b) (hab : a ≠ b)
    (omitEdge : Bool) (hActual : omitEdge = false → G.Adj w b)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hDegree : ∀ v ∈ ({a,b} : Finset V),v ∈ U → U.card+2+Z.card+k ≤ G.degree v) :
    ∃ R : TrimmingReplacementWords G U (Fin 1),
      R.gaps = (if omitEdge then {s(w,b)} else ∅) ∧
      (∀ v,v ∈ R.body 0 ↔ v ∈ U ∧ (v = w ∨ v = a ∨ v = b)) ∧
      (if a ∈ U then projectionLoad (range j) used (R.endpoint (0,false)).val < cap
        else (R.endpoint (0,false)).val = a) ∧
      (if b ∈ U then projectionLoad (range j) used (R.endpoint (0,true)).val < cap
        else (R.endpoint (0,true)).val = b) ∧
      (R.body 0).length = 1+(if a ∈ U then 1 else 0)+(if b ∈ U then 1 else 0) ∧
      (omitEdge = false → ∀ omitted,R.degreeCredit omitted w = 0) ∧
      R.prescribedGraph.Adj w a ∧
      (omitEdge = false → R.prescribedGraph.Adj w b) := by
  let A : Finset V := {a,b}
  let a' : A := ⟨a,mem_insert_self _ _⟩
  let b' : A := ⟨b,by simp [A]⟩
  have hSize : A.card = 2 := card_pair hab
  obtain ⟨P,hFresh⟩ := exists_projection_with_free_load_cap G A U Z (range j) used cap k budget
    hCap (fun i hi => hUsed i (mem_range.mp hi)) (by simpa only [card_range] using hTotal)
    (fun v hv => by
      obtain ⟨hA,hU⟩ := mem_inter.mp hv
      rw [hSize]
      exact hDegree v hA hU)
  obtain ⟨R,hA,hB,hG,hBody,hLength,hCredit,hFirst,hLast⟩ := exists_singleton_prescription_with_leaf_positions P a' b'
    (fun h => hab (congrArg Subtype.val h)) w hw hwa hwb omitEdge hActual
  refine ⟨R,hG,hBody,?_,?_,hLength,hCredit,hFirst,hLast⟩
  · rw [hA]
    split
    · exact hFresh a' ‹a ∈ U›
    · exact P.fixed a' ‹a ∉ U›
  · rw [hB]
    split
    · exact hFresh b' ‹b ∈ U›
    · exact P.fixed b' ‹b ∉ U›

theorem exists_capped_singleton_round_of_endpoint_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Z : Finset V)
    {w a b : V} (hw : w ∈ U) (hwa : G.Adj w a) (hwb : w ≠ b) (hab : a ≠ b)
    (omitEdge : Bool) (hActual : omitEdge = false → G.Adj w b)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hDegree : ∀ v ∈ ({a,b} : Finset V),v ∈ U → U.card+2+Z.card+k ≤ G.degree v) :
    ∃ R : TrimmingReplacementWords G U (Fin 1),
      R.gaps = (if omitEdge then {s(w,b)} else ∅) ∧
      (∀ v ∈ R.body 0,v = w ∨ v = a ∨ v = b) ∧
      (if a ∈ U then projectionLoad (range j) used (R.endpoint (0,false)).val < cap
        else (R.endpoint (0,false)).val = a) ∧
      (if b ∈ U then projectionLoad (range j) used (R.endpoint (0,true)).val < cap
        else (R.endpoint (0,true)).val = b) ∧
      (R.body 0).length = 1+(if a ∈ U then 1 else 0)+(if b ∈ U then 1 else 0) ∧
      (omitEdge = false → ∀ omitted,R.degreeCredit omitted w = 0) := by
  obtain ⟨R,hGap,hBody,hA,hB,hLen,hCredit,_,_⟩ :=
    exists_capped_singleton_round_with_leaf_positions G U Z hw hwa hwb hab omitEdge hActual
      used j cap k budget hCap hUsed hTotal hDegree
  exact ⟨R,hGap,fun v hv => ((hBody v).mp hv).2,hA,hB,hLen,hCredit⟩

theorem exists_capped_singleton_round (G : SimpleGraph V) [DecidableRel G.Adj] (U Z : Finset V)
    {w a b : V} (hw : w ∈ U) (hwa : G.Adj w a) (hwb : w ≠ b) (hab : a ≠ b)
    (omitEdge : Bool) (hActual : omitEdge = false → G.Adj w b)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hDegree : ∀ v ∈ U,v ≠ w → U.card+2+Z.card+k ≤ G.degree v) :
    ∃ R : TrimmingReplacementWords G U (Fin 1),
      R.gaps = (if omitEdge then {s(w,b)} else ∅) ∧
      (∀ v ∈ R.body 0,v = w ∨ v = a ∨ v = b) ∧
      (if a ∈ U then projectionLoad (range j) used (R.endpoint (0,false)).val < cap
        else (R.endpoint (0,false)).val = a) ∧
      (if b ∈ U then projectionLoad (range j) used (R.endpoint (0,true)).val < cap
        else (R.endpoint (0,true)).val = b) := by
  obtain ⟨R,hG,hBody,hA,hB,_,_⟩ :=
    exists_capped_singleton_round_of_endpoint_degrees G U Z hw hwa hwb hab omitEdge hActual
      used j cap k budget hCap hUsed hTotal (fun v hv hvU => by
        rcases (show v = a ∨ v = b by simpa using hv) with rfl|rfl
        · exact hDegree _ hvU hwa.ne.symm
        · exact hDegree _ hvU hwb.symm)
  exact ⟨R,hG,hBody,hA,hB⟩

set_option maxHeartbeats 1700000 in
theorem exists_capped_charged_singleton_round (G M₁ M₂ : SimpleGraph V) [DecidableRel G.Adj]
    (U Z : Finset V) {w x : V} (hw : w ∈ U) (hwx : w ≠ x) (hDis : Disjoint M₁ M₂)
    (hLe₁ : M₁ ≤ G) (hLe₂ : M₂ ≤ G) (h₁ : ∃ a,M₁.Adj w a) (h₂ : ∃ b,M₂.Adj w b)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hDegree : ∀ v ∈ U,v ≠ w → U.card+2+Z.card+k ≤ G.degree v) :
    ∃ a : V, a ≠ x ∧ (M₁.Adj w a ∨ M₂.Adj w a) ∧
      ∃ R : TrimmingReplacementWords G U (Fin 1),R.gaps = {s(w,x)} ∧
        (∀ v ∈ R.body 0,v = w ∨ v = a ∨ v = x) ∧
        (if a ∈ U then projectionLoad (range j) used (R.endpoint (0,false)).val < cap
          else (R.endpoint (0,false)).val = a) ∧
        (if x ∈ U then projectionLoad (range j) used (R.endpoint (0,true)).val < cap
          else (R.endpoint (0,true)).val = x) := by
  obtain ⟨a,hax,hAdj⟩ := singleton_matching_choice_avoids_charged_vertex hDis h₁ h₂
  have hwa := hAdj.elim (fun h => hLe₁ h) (fun h => hLe₂ h)
  obtain ⟨R,hGap,hBody,hA,hX⟩ := exists_capped_singleton_round G U Z hw hwa hwx hax true
    (by simp) used j cap k budget hCap hUsed hTotal hDegree
  exact ⟨a,hax,hAdj,R,hGap,hBody,hA,hX⟩

end OverfullWork.CMSTrimmingRound
