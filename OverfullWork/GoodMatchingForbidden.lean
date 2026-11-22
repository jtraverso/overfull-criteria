module

public import OverfullWork.MatchingForbidden
public import OverfullWork.ProtectedColourTools

@[expose] public section


/-! # Good internal matching and its forbidden vertices

The residue is the actual uncolored internal multigraph. A good copy
is currently colored, internal, and has both residue degrees below h.
Counts retain a crossing-matching term until it is explicitly paid.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

def highVertices (R : MultiGraph V) (h : ℕ) : Finset V := univ.filter (fun v => h ≤ R.degree v)

noncomputable def goodMatching (L R : MultiGraph V) (A : Finset V) (h : ℕ) : MultiGraph V :=
  (L.internalPart A).subtractCopies ((L.internalPart A).incidentOn (R.highVertices h))

noncomputable def residueForbidden (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (R : MultiGraph V) (A E : Finset V) (h : ℕ) : Finset V :=
  L.matchingForbidden hL A (R.highVertices h ∪ E)

theorem goodMatching_le (L R : MultiGraph V) (A : Finset V) (h : ℕ) (e : Sym2 V) :
    (L.goodMatching R A h).mult e ≤ L.mult e := by
  change (L.internalPart A).mult e-_ ≤ _
  exact (Nat.sub_le _ _).trans (L.internalPart_le A e)

theorem goodMatching_degree_le_one (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (R : MultiGraph V) (A : Finset V) (h : ℕ) (v : V) : (L.goodMatching R A h).degree v ≤ 1 :=
  (L.degree_le_of_mult_le _ (L.goodMatching_le R A h) v).trans (hL v)

theorem residueForbidden_safe_partner (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (R : MultiGraph V) (A E : Finset V) (h : ℕ) (v : V)
    (hv : v ∉ L.residueForbidden hL R A E h) :
    let u := L.matchingPartner hL v
    u ∉ L.residueForbidden hL R A E h ∧ u ≠ v ∧ (v ∈ A ↔ u ∈ A) ∧
      v ∉ E ∧ u ∉ E ∧ R.degree v < h ∧ R.degree u < h ∧
      (L.goodMatching R A h).mult s(v,u)=1 := by
  let u := L.matchingPartner hL v
  have hf := L.outside_matchingForbidden_facts hL A (R.highVertices h ∪ E) v hv
  have hPartner := L.matchingForbidden_closed_complement hL A (R.highVertices h ∪ E) v hv
  have hvHigh : v ∉ R.highVertices h := fun hh => hf.2.2.1 (mem_union_left _ hh)
  have huHigh : u ∉ R.highVertices h := fun hh => hf.2.2.2 (mem_union_left _ hh)
  have hvE : v ∉ E := fun hh => hf.2.2.1 (mem_union_right _ hh)
  have huE : u ∉ E := fun hh => hf.2.2.2 (mem_union_right _ hh)
  have hvLow : R.degree v < h := by
    have hn : ¬h ≤ R.degree v := fun hh => hvHigh (mem_filter.mpr ⟨mem_univ _,hh⟩)
    omega
  have huLow : R.degree u < h := by
    have hn : ¬h ≤ R.degree u := fun hh => huHigh (mem_filter.mpr ⟨mem_univ _,hh⟩)
    omega
  refine ⟨hPartner,L.matchingPartner_ne hL v hf.1,hf.2.1,hvE,huE,hvLow,huLow,?_⟩
  have he : L.mult s(v,u)=1 := L.matchingPartner_adj hL v hf.1
  have hNo : ¬∃ z ∈ R.highVertices h, z ∈ s(v,u) := by
    rintro ⟨z,hz,hze⟩
    rcases Sym2.mem_iff.mp hze with he|he
    · exact hvHigh (he ▸ hz)
    · exact huHigh (he ▸ hz)
  change (L.internalPart A).mult s(v,u)-
    (if ∃ z ∈ R.highVertices h, z ∈ s(v,u) then (L.internalPart A).mult s(v,u) else 0)=1
  rw [if_neg hNo,Nat.sub_zero,internalPart_mult,if_pos hf.2.1,he]

theorem residueForbidden_weighted_bound (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (R : MultiGraph V) (A E : Finset V) (h : ℕ) :
    h*(L.residueForbidden hL R A E h).card ≤
      h*((L.missingVertices univ).card+2*L.cutSize A+2*E.card)+4*R.edgeCount := by
  have hb := L.matchingForbidden_card_bound hL A (R.highVertices h ∪ E)
  have hu := card_union_le (R.highVertices h) E
  have hh := R.high_degree_card_bound h
  change h*(R.highVertices h).card ≤ 2*R.edgeCount at hh
  have hScaled := Nat.mul_le_mul_left h hb
  change h*(L.residueForbidden hL R A E h).card ≤ _ at hScaled
  have hUnion := Nat.mul_le_mul_left h hu
  nlinarith only [hScaled,hUnion,hh]

theorem residueForbidden_weighted_localized (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (R : MultiGraph V) (A E : Finset V) (h : ℕ)
    (hCross : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → 0 < L.mult s(x,y) → x ∈ E ∨ y ∈ E) :
    h*(L.residueForbidden hL R A E h).card ≤
      h*((L.missingVertices univ).card+2*E.card)+4*R.edgeCount := by
  have hb := L.matchingForbidden_card_localized hL A (R.highVertices h ∪ E)
    (fun x y hxy hpos => (hCross x y hxy hpos).imp (mem_union_right _) (mem_union_right _))
  have hu := card_union_le (R.highVertices h) E
  have hh := R.high_degree_card_bound h
  change h*(R.highVertices h).card ≤ 2*R.edgeCount at hh
  have hScaled := Nat.mul_le_mul_left h hb
  change h*(L.residueForbidden hL R A E h).card ≤ _ at hScaled
  have hUnion := Nat.mul_le_mul_left h hu
  nlinarith only [hScaled,hUnion,hh]

end SimpleGraph.MultiGraph
