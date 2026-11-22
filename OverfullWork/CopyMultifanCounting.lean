module

public import OverfullWork.CopyMultifanMaximal

@[expose] public section


/-! # A bounded row permits the missing-copy extension

The maximal fan's missing colors are disjoint. Its first vertex misses
at least mu+1 colors, and every other vertex at least mu. Closure puts
all these colors on at most L*mu incident copies, a contradiction.
-/
namespace OverfullWork.CopyMultifan
open Finset ShannonColouring
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
variable {ends : I → V × V} {s : Finset I} {d μ : ℕ} {x : V} {e : I}
set_option maxHeartbeats 12000000

theorem bounded_row_extension (hloop : ∀ h, (ends h).1 ≠ (ends h).2)
    (hdeg : ∀ v, degree ends v ≤ d)
    (hRow : ∀ z, (univ.filter (fun h => Joins ends h x z)).card ≤ μ)
    (he : e ∉ s) (hx : Incident ends e x) (c : I → Fin (d+μ)) (hc : ProperOn ends s c) :
    ∃ c' : I → Fin (d+μ), ProperOn ends (insert e s) c' := by
  by_contra hNo
  obtain ⟨z,hj⟩ := exists_other hx
  obtain ⟨L,y,g,hF,hmax⟩ := exists_maximal (s := s) (c := c) hj
  have hRoot : ∀ b : I → Fin (d+μ), ProperOn ends s b → ∃ a, Misses ends s b x a := by
    intro b _
    have hh := card_misses_ge_of_incident hdeg he b hx
    have hpos : 0 < (univ.filter (Misses ends s b x)).card := by omega
    obtain ⟨a,ha⟩ := card_pos.mp hpos
    exact ⟨a,(mem_filter.mp ha).2⟩
  obtain ⟨_,hApart,_⟩ := elementary hloop he hNo hRoot L c hc hF
  let missing := fun i => univ.filter (Misses ends s c (y i))
  let U := (range L).biUnion missing
  have hdis : (range L : Set ℕ).PairwiseDisjoint missing := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro a hai haj
    exact hApart i (mem_range.mp hi) j (mem_range.mp hj) hij a
      (mem_filter.mp hai).2 (mem_filter.mp haj).2
  have hU : U.card = ∑ i ∈ range L, (missing i).card := card_biUnion hdis
  have hlow : L*μ+1 ≤ U.card := by
    have hl : ∀ i ∈ range L, μ+(if i=0 then 1 else 0) ≤ (missing i).card := by
      intro i hi
      by_cases hi0 : i=0
      · subst i
        have hje := hF.joins 0 hF.pos
        rw [hF.start] at hje
        have hinc : Incident ends e (y 0) := hje.incident_iff.mpr (Or.inr rfl)
        have hh := card_misses_ge_of_incident hdeg he c hinc
        simp only [ite_true]
        change _ ≤ (univ.filter (Misses ends s c (y 0))).card
        omega
      · have hh := card_misses_ge hdeg s c (y i)
        rw [if_neg hi0,add_zero]
        change μ ≤ (univ.filter (Misses ends s c (y i))).card
        omega
    have hh := sum_le_sum hl
    rw [sum_add_distrib] at hh
    have hone : (∑ i ∈ range L, if i=0 then 1 else 0)=1 := by simp [hF.pos]
    rw [hone] at hh
    simp only [sum_const,card_range,smul_eq_mul] at hh
    rwa [hU]
  let C := (range L).biUnion (fun i => s.filter (fun h => Joins ends h x (y i)))
  have hsub : U ⊆ C.image c := by
    intro a ha
    obtain ⟨i,hi,hai⟩ := mem_biUnion.mp ha
    have hm : Misses ends s c (y i) a := (mem_filter.mp hai).2
    obtain ⟨h,hh,j,hj,hjoin,hcol⟩ := hF.closed hloop he hc hNo hmax i (mem_range.mp hi) a hm
    apply mem_image.mpr
    exact ⟨h,mem_biUnion.mpr ⟨j,mem_range.mpr hj,mem_filter.mpr ⟨hh,hjoin⟩⟩,hcol⟩
  have hcap : C.card ≤ L*μ := by
    calc
      _ ≤ ∑ i ∈ range L, (s.filter (fun h => Joins ends h x (y i))).card := card_biUnion_le
      _ ≤ ∑ _i ∈ range L, μ := by
        apply sum_le_sum
        intro i _
        exact (card_le_card (filter_subset_filter _ (subset_univ s))).trans (hRow (y i))
      _ = L*μ := by simp
  have hupper : U.card ≤ L*μ := (card_le_card hsub).trans (card_image_le.trans hcap)
  omega

end OverfullWork.CopyMultifan
