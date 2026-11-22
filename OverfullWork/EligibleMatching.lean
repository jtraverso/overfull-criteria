module

public import OverfullWork.MatchingPartner
public import OverfullWork.MissingPairs

@[expose] public section


/-! # Quantifying which matching edges can be safely exchanged -/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def missingVertices (Q : MultiGraph V) (S : Finset V) : Finset V :=
  S.filter (fun v => Q.degree v=0)

noncomputable def crossingVertices (Q : MultiGraph V) (hdeg : ∀ v,Q.degree v≤1)
    (S : Finset V) : Finset V :=
  S.filter (fun v => Q.degree v=1 ∧ Q.matchingPartner hdeg v∉S)

noncomputable def eligibleVertices (Q : MultiGraph V) (hdeg : ∀ v,Q.degree v≤1)
    (S Z : Finset V) : Finset V :=
  S.filter (fun v => Q.degree v=1 ∧ Q.matchingPartner hdeg v∈S ∧
    v∉Z ∧ Q.matchingPartner hdeg v∉Z)

theorem crossingVertices_card_le_cut (Q : MultiGraph V) (hdeg : ∀ v,Q.degree v≤1)
    (S : Finset V) : (Q.crossingVertices hdeg S).card≤Q.cutSize S := by
  simp only [crossingVertices,card_eq_sum_ones,sum_filter,cutSize]
  apply sum_le_sum
  intro v _
  split_ifs with hv
  · have hmem : Q.matchingPartner hdeg v∈Sᶜ:=mem_compl.mpr hv.2
    have h:=single_le_sum (f:=fun w : V => Q.mult s(v,w))
      (fun _ _ => Nat.zero_le _) hmem
    rw [Q.matchingPartner_adj hdeg v hv.1] at h
    exact h
  · exact Nat.zero_le _

theorem eligibleVertices_subset (Q : MultiGraph V) (hdeg : ∀ v,Q.degree v≤1)
    (S Z : Finset V) : Q.eligibleVertices hdeg S Z⊆S := filter_subset _ _

theorem eligibleVertices_closed (Q : MultiGraph V) (hdeg : ∀ v,Q.degree v≤1)
    (S Z : Finset V) (v : V) (hv : v∈Q.eligibleVertices hdeg S Z) :
    Q.matchingPartner hdeg v∈Q.eligibleVertices hdeg S Z := by
  obtain ⟨hS,hvdeg,hpartner,hvZ,hpZ⟩:=mem_filter.mp hv
  have hm:=Q.matchingPartner_adj hdeg v hvdeg
  have hpos:=Q.mult_pair_le_degree (Q.matchingPartner hdeg v) v
  rw [Sym2.eq_swap] at hpos
  have hpd : Q.degree (Q.matchingPartner hdeg v)=1 := by
    have hb:=hdeg (Q.matchingPartner hdeg v)
    omega
  apply mem_filter.mpr
  rw [Q.matchingPartner_apply_apply]
  exact ⟨hpartner,hpd,hS,hpZ,hvZ⟩

theorem eligibleVertices_ne (Q : MultiGraph V) (hdeg : ∀ v,Q.degree v≤1)
    (S Z : Finset V) (v : V) (hv : v∈Q.eligibleVertices hdeg S Z) :
    Q.matchingPartner hdeg v≠v := Q.matchingPartner_ne hdeg v (mem_filter.mp hv).2.1

/-- The forbidden endpoints cost at most twice |Z|. The remaining
exceptions are exactly missing vertices and crossing matching edges. -/
theorem ineligible_card_bound (Q : MultiGraph V) (hdeg : ∀ v,Q.degree v≤1)
    (S Z : Finset V) :
    (S\Q.eligibleVertices hdeg S Z).card≤
      (Q.missingVertices S).card+Q.cutSize S+2*Z.card := by
  let τ:=Q.matchingPartner hdeg
  have hsub : S\Q.eligibleVertices hdeg S Z ⊆
      ((Q.missingVertices S∪Q.crossingVertices hdeg S)∪Z)∪Z.image τ := by
    intro v hv
    obtain ⟨hS,hnot⟩:=mem_sdiff.mp hv
    by_cases hdeg1 : Q.degree v=1
    · by_cases hp : τ v∈S
      · by_cases hz : v∈Z
        · exact mem_union_left _ (mem_union_right _ hz)
        · have hpz : τ v∈Z := by
            by_contra hn
            exact hnot (mem_filter.mpr ⟨hS,hdeg1,hp,hz,hn⟩)
          exact mem_union_right _ (mem_image.mpr ⟨τ v,hpz,Q.matchingPartner_apply_apply hdeg v⟩)
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _
          (mem_filter.mpr ⟨hS,hdeg1,hp⟩)))
    · have hz : Q.degree v=0 := by have h:=hdeg v; omega
      exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hS,hz⟩)))
  have h₀:=card_le_card hsub
  have h₁:=card_union_le ((Q.missingVertices S∪Q.crossingVertices hdeg S)∪Z) (Z.image τ)
  have h₂:=card_union_le (Q.missingVertices S∪Q.crossingVertices hdeg S) Z
  have h₃:=card_union_le (Q.missingVertices S) (Q.crossingVertices hdeg S)
  have hτ : (Z.image τ).card=Z.card:=card_image_of_injective _ τ.injective
  have hc:=Q.crossingVertices_card_le_cut hdeg S
  omega

end SimpleGraph.MultiGraph
