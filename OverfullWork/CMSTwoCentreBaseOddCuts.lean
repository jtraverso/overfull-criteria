module

public import OverfullWork.CMSRegularizationOddCuts
public import OverfullWork.TwoIdentificationInternalCounts

@[expose] public section


/-! Odd cuts of the uncompleted quotient in CMS Subcase 2.4.
The ordered-pair balance handles complements of singletons. -/
namespace OverfullWork.TwoCentreOrdinaryCore

open Finset SimpleGraph RobustExpansion
open scoped Classical

variable {W : Type*} [Fintype W] [DecidableEq W]

theorem singleton_complement_internal_bound (M : MultiGraph (Sum Bool W)) (d : ℕ)
    (hD : ∀ v, M.degree v ≤ d) (v : Sum Bool W)
    (hBalance : 2*(d-M.degree v) ≤ ∑ w, (d-M.degree w)) :
    M.twiceInternal ({v}:Finset _)ᶜ ≤ d*((({v}:Finset (Sum Bool W))ᶜ).card-1) := by
  let T := ({v}:Finset (Sum Bool W))ᶜ
  have hCard : T.card+1 = Fintype.card (Sum Bool W) := by
    have h := card_add_card_compl ({v}:Finset (Sum Bool W))
    rw [card_singleton] at h
    change 1+T.card = _ at h
    omega
  have hN : 2 ≤ Fintype.card (Sum Bool W) := by rw [Fintype.card_sum,Fintype.card_bool]; omega
  have hT : 1 ≤ T.card := by omega
  have hComp : M.cutSize T = M.degree v := by
    dsimp only [T]
    rw [M.cutSize_compl,CanonicalAdmissibility.cut_singleton]
  have hSum := M.sum_degree_eq_internal_add_cut T
  rw [hComp] at hSum
  have hAll := sum_add_sum_compl ({v}:Finset (Sum Bool W)) M.degree
  rw [sum_singleton] at hAll
  change M.degree v+(∑ w ∈ T, M.degree w) = _ at hAll
  have hDef := M.total_deficit_of_bounded d hD
  rw [←hCard] at hDef
  have hFact : (T.card+1)*d = d*(T.card-1)+2*d := by
    have hh : T.card+1 = (T.card-1)+2 := by omega
    rw [hh]
    ring
  rw [hFact] at hDef
  have hBound := hD v
  change M.twiceInternal T ≤ d*(T.card-1)
  omega

set_option maxHeartbeats 2000000 in
theorem no_overfull_of_robust_two_centre_base (M : MultiGraph (Sum Bool W)) (d r t : ℕ)
    (hEven : Even (Fintype.card (Sum Bool W))) (hD : ∀ v, M.degree v ≤ d)
    (hRob : IsRobustAt M.supportGraph r t) (hRate : d ≤ r*r)
    (hOrd : ∀ x y : W, x ≠ y →
      d+2*t ≤ M.supportGraph.degree (Sum.inr x)+M.supportGraph.degree (Sum.inr y))
    (hSum : M.degree (Sum.inl false)+M.degree (Sum.inl true) ≤ d)
    (hMin : ∀ x : W, M.degree (Sum.inl false) ≤ M.degree (Sum.inr x))
    (hBalance : ∀ i : Bool, 2*(d-M.degree (Sum.inl i)) ≤ ∑ w, (d-M.degree w))
    (hAway : ∀ T : Finset W, Odd T.card → (ordinary M).twiceInternal T ≤ d*(T.card-1)) :
    ¬M.HasOverfullSubset d := by
  let a : Sum Bool W := Sum.inl false
  let b : Sum Bool W := Sum.inl true
  have hab : a ≠ b := by simp [a,b]
  have hPairCut (S : Finset (Sum Bool W)) (hS : S.card < t)
      (hTwo : 1 < (ordinaryVertices S).card) : d ≤ M.cutSize S := by
    obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp hTwo
    have hxS := (mem_filter.mp hx).2
    have hyS := (mem_filter.mp hy).2
    have hCut := CanonicalRegularization.support_pair_le_cut_add_internal M S
      (Sum.inr x) (Sum.inr y) hxS hyS (fun h => hxy (Sum.inr.inj h))
    have hBound := hOrd x y hxy
    omega
  have hSmall (S : Finset (Sum Bool W)) (hS : S.card < t) (hOdd : Odd S.card) :
      d ≤ M.cutSize S ∨ S.card = 1 ∨ ∃ x : W, S = {a,b,Sum.inr x} := by
    by_cases hTwo : 1 < (ordinaryVertices S).card
    · exact Or.inl (hPairCut S hS hTwo)
    right
    have hCard := card_split S
    change S.card = (ordinaryVertices S).card + (if a ∈ S then 1 else 0)+
      (if b ∈ S then 1 else 0) at hCard
    obtain ⟨k,hk⟩ := hOdd
    by_cases hA : a ∈ S <;> by_cases hB : b ∈ S <;>
      simp only [hA,hB,if_true,if_false] at hCard
    · by_cases hOne : S.card = 1
      · exact Or.inl hOne
      · right
        have hN : (ordinaryVertices S).card = 1 := by omega
        obtain ⟨x,hx⟩ := card_eq_one.mp hN
        have hxS : Sum.inr x ∈ S := (mem_filter.mp (show x ∈ ordinaryVertices S by rw [hx]; simp)).2
        refine ⟨x,(eq_of_subset_of_card_le (show {a,b,Sum.inr x} ⊆ S by
          exact insert_subset hA (insert_subset hB (singleton_subset_iff.mpr hxS))) ?_).symm⟩
        have hThree : S.card = 3 := by omega
        rw [hThree]
        simp [a,b]
    all_goals exact Or.inl (by omega)
  have hCutSafe (S : Finset (Sum Bool W)) (hOdd : Odd S.card) (hCut : d ≤ M.cutSize S) :
      M.twiceInternal S ≤ d*(S.card-1) := by
    obtain ⟨k,hk⟩ := hOdd
    have hFact : d*S.card = d*(S.card-1)+d := by
      have h := Nat.sub_add_cancel (by omega : 1 ≤ S.card)
      conv_lhs => rw [←h]
      ring
    have hBound : (∑ v ∈ S, M.degree v) ≤ d*S.card := by
      calc
        _ ≤ ∑ v ∈ S, d := sum_le_sum (fun v _ => hD v)
        _ = _ := by simp [Nat.mul_comm]
    have h := M.sum_degree_eq_internal_add_cut S
    omega
  apply (M.noOverfull_iff_odd_bounds d hD).mpr
  intro S hSOdd
  by_cases hSmallS : S.card < t
  · rcases hSmall S hSmallS hSOdd with hCut | hOne | ⟨x,hx⟩
    · exact hCutSafe S hSOdd hCut
    · obtain ⟨v,hv⟩ := card_eq_one.mp hOne
      rw [hv]
      simp [MultiGraph.twiceInternal,M.loopless _ (by simp : s(v,v).IsDiag)]
    · rw [hx,CriticalCentreTriples.triple_internal M a b (Sum.inr x) hab (by simp [a]) (by simp [b])]
      have hA := CanonicalTripleAddition.two_bundles_le_degree M a b (Sum.inr x) (by simp [b])
      have hB := M.mult_pair_le_degree b (Sum.inr x)
      change M.degree a+M.degree b ≤ d at hSum
      have hSize : ({a,b,Sum.inr x}:Finset (Sum Bool W)).card = 3 := by simp [a,b]
      rw [hSize]
      omega
  by_cases hSmallT : Sᶜ.card < t
  · have hTOdd := MultiGraph.odd_card_compl hEven hSOdd
    rcases hSmall Sᶜ hSmallT hTOdd with hCut | hOne | ⟨x,hx⟩
    · apply hCutSafe S hSOdd
      rwa [←M.cutSize_compl S]
    · obtain ⟨v,hv⟩ := card_eq_one.mp hOne
      have hV : S = ({v}:Finset (Sum Bool W))ᶜ := by rw [←hv,compl_compl]
      rw [hV]
      apply singleton_complement_internal_bound M d hD v
      cases v with
      | inl i => exact hBalance i
      | inr x =>
        have h := hBalance false
        have hx := hMin x
        omega
    · have hA : a ∉ S := by
        apply mem_compl.mp
        rw [hx]
        simp
      have hB : b ∉ S := by
        apply mem_compl.mp
        rw [hx]
        simp
      have hCard := card_split S
      change S.card = (ordinaryVertices S).card + (if a ∈ S then 1 else 0)+
        (if b ∈ S then 1 else 0) at hCard
      simp only [if_neg hA,if_neg hB,Nat.add_zero] at hCard
      rw [twiceInternal_away M S hA hB,hCard]
      exact hAway _ (hCard ▸ hSOdd)
  apply hCutSafe S hSOdd
  apply hRate.trans (CanonicalRegularization.robust_cut_lower M S r t hRob (by omega) ?_)
  have hCard := card_add_card_compl S
  omega

end OverfullWork.TwoCentreOrdinaryCore
