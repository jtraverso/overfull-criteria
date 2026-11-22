module

public import OverfullWork.EligibleMatching
public import OverfullWork.CompletionAccounting

@[expose] public section


/-! # Forbidden vertices for an internal matching step

Exclude missing vertices, endpoints of crossing matching edges, and
the matching closure of the high-degree/exceptional set. The crossing
term is explicit in the general bound; when all crossing edges meet an
exceptional vertex it is absorbed by that vertex and its partner.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

noncomputable def matchingForbidden (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (A D : Finset V) : Finset V :=
  (L.missingVertices univ ∪ (L.crossingVertices hL A ∪ L.crossingVertices hL Aᶜ)) ∪
    (D ∪ D.image (L.matchingPartner hL))

theorem mem_matching_image (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (D : Finset V) (v : V) : v ∈ D.image (L.matchingPartner hL) ↔ L.matchingPartner hL v ∈ D := by
  constructor
  · intro hv
    obtain ⟨u,hu,he⟩ := mem_image.mp hv
    rw [←he,L.matchingPartner_apply_apply]
    exact hu
  · intro hv
    exact mem_image.mpr ⟨_,hv,L.matchingPartner_apply_apply hL v⟩

theorem outside_matchingForbidden_iff (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (A D : Finset V) (v : V) : v ∉ L.matchingForbidden hL A D ↔
    v ∈ L.eligibleVertices hL A D ∪ L.eligibleVertices hL Aᶜ D := by
  simp only [matchingForbidden,mem_union,L.mem_matching_image hL D v]
  have hd := hL v
  by_cases hz : L.degree v=0
  · have hn : L.degree v ≠ 1 := by omega
    simp [matchingForbidden,missingVertices,eligibleVertices,hz,hn]
  · have hd1 : L.degree v=1 := by omega
    by_cases hv : v ∈ A <;> by_cases hp : L.matchingPartner hL v ∈ A <;>
      simp [matchingForbidden,missingVertices,crossingVertices,eligibleVertices,
        mem_matching_image,hd1,hv,hp]

theorem matchingForbidden_closed_complement (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (A D : Finset V) (v : V) (hv : v ∉ L.matchingForbidden hL A D) :
    L.matchingPartner hL v ∉ L.matchingForbidden hL A D := by
  rw [outside_matchingForbidden_iff] at hv ⊢
  rcases mem_union.mp hv with hv|hv
  · exact mem_union_left _ (L.eligibleVertices_closed hL A D v hv)
  · exact mem_union_right _ (L.eligibleVertices_closed hL Aᶜ D v hv)

theorem outside_matchingForbidden_facts (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (A D : Finset V) (v : V) (hv : v ∉ L.matchingForbidden hL A D) :
    L.degree v=1 ∧ (v ∈ A ↔ L.matchingPartner hL v ∈ A) ∧
      v ∉ D ∧ L.matchingPartner hL v ∉ D := by
  rw [outside_matchingForbidden_iff] at hv
  rcases mem_union.mp hv with hv|hv
  · obtain ⟨hv,hdeg,hp,hD,hpD⟩ := mem_filter.mp hv
    exact ⟨hdeg,by tauto,hD,hpD⟩
  · obtain ⟨hv,hdeg,hp,hD,hpD⟩ := mem_filter.mp hv
    have hvA : v ∉ A := mem_compl.mp hv
    have hpA : L.matchingPartner hL v ∉ A := mem_compl.mp hp
    exact ⟨hdeg,by tauto,hD,hpD⟩

theorem matchingForbidden_card_bound (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (A D : Finset V) : (L.matchingForbidden hL A D).card ≤
      (L.missingVertices univ).card+2*L.cutSize A+2*D.card := by
  have h₀ := card_union_le (L.missingVertices univ ∪
    (L.crossingVertices hL A ∪ L.crossingVertices hL Aᶜ)) (D ∪ D.image (L.matchingPartner hL))
  have h₁ := card_union_le (L.missingVertices univ) (L.crossingVertices hL A ∪ L.crossingVertices hL Aᶜ)
  have h₂ := card_union_le (L.crossingVertices hL A) (L.crossingVertices hL Aᶜ)
  have h₃ := card_union_le D (D.image (L.matchingPartner hL))
  have hτ : (D.image (L.matchingPartner hL)).card=D.card :=
    card_image_of_injective _ (L.matchingPartner hL).injective
  have hA := L.crossingVertices_card_le_cut hL A
  have hAc := L.crossingVertices_card_le_cut hL Aᶜ
  rw [cutSize_compl] at hAc
  change (L.matchingForbidden hL A D).card ≤ _ at h₀
  omega

theorem matchingForbidden_card_localized (L : MultiGraph V) (hL : ∀ v, L.degree v ≤ 1)
    (A D : Finset V)
    (hCross : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → 0 < L.mult s(x,y) → x ∈ D ∨ y ∈ D) :
    (L.matchingForbidden hL A D).card ≤ (L.missingVertices univ).card+2*D.card := by
  have hc : L.crossingVertices hL A ∪ L.crossingVertices hL Aᶜ ⊆ D ∪ D.image (L.matchingPartner hL) := by
    intro v hv
    have hf : L.degree v=1 ∧ ¬(v ∈ A ↔ L.matchingPartner hL v ∈ A) := by
      rcases mem_union.mp hv with hv|hv
      · obtain ⟨hA,hdeg,hp⟩ := mem_filter.mp hv
        exact ⟨hdeg,by tauto⟩
      · obtain ⟨hA,hdeg,hp⟩ := mem_filter.mp hv
        have hvA : v ∉ A := mem_compl.mp hA
        have hpA : L.matchingPartner hL v ∈ A := by simpa only [mem_compl,not_not] using hp
        exact ⟨hdeg,by tauto⟩
    have he := L.matchingPartner_adj hL v hf.1
    rcases hCross v _ hf.2 (by omega) with hvD|hpD
    · exact mem_union_left _ hvD
    · exact mem_union_right _ ((L.mem_matching_image hL D v).mpr hpD)
  have hs : L.matchingForbidden hL A D ⊆ L.missingVertices univ ∪ (D ∪ D.image (L.matchingPartner hL)) := by
    intro v hv
    rcases mem_union.mp hv with hv|hv
    · rcases mem_union.mp hv with hv|hv
      · exact mem_union_left _ hv
      · exact mem_union_right _ (hc hv)
    · exact mem_union_right _ hv
  have h₀ := card_le_card hs
  have h₁ := card_union_le (L.missingVertices univ) (D ∪ D.image (L.matchingPartner hL))
  have h₂ := card_union_le D (D.image (L.matchingPartner hL))
  have hτ : (D.image (L.matchingPartner hL)).card=D.card :=
    card_image_of_injective _ (L.matchingPartner hL).injective
  omega

end SimpleGraph.MultiGraph
