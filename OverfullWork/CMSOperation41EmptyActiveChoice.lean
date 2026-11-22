module

public import OverfullWork.CMSOperation41CriticalChoice

@[expose] public section


/-! The alternatives of S2.3 and S2.4 before constructing any
projected edges. The choice uses the corrected degree record and the
current active vertices of the virtual graph. -/
namespace OverfullWork.CMSTrimmingRound

open Finset
open scoped Classical

variable {V : Type*} [DecidableEq V]

inductive EmptyActiveChoice (active U : Finset V) (d floor : ℕ) (degree : V → ℕ) : Prop
  | even_core (h : Even (active \ U).card)
  | charged_pair (a b : V) (ha : a ∈ active \ U) (hb : b ∈ active \ U) (hne : a ≠ b)
      (hA : degree a < d) (hB : degree b < d)
  | omit (a : V) (ha : a ∈ active \ U) (hA : degree a+2 ≤ d)
      (hOther : ∀ v ∈ active \ U,v ≠ a → degree v = d) (hOdd : Odd (active \ U).card)
  | special (z : V) (hz : z ∈ U) (hHigh : floor+2 ≤ degree z)
      (hMass : (∑ v ∈ active \ U,(d-degree v)) ≤ 1) (hOdd : Odd (active \ U).card)
  | switch_active (T : Finset V) (hSub : T ⊆ U) (hEven : Even active.card ↔ T.card = 2)
      (hSmall : ∀ z ∈ U,degree z < floor+2)
      (hOdd : Odd (active \ U).card) (hMass : (∑ v ∈ active \ U,(d-degree v)) ≤ 1)
      (hMinimum : (Even U.card ∧ ∃ a ∈ U,T = {a} ∧ ∀ v ∈ U,degree a ≤ degree v) ∨
        (Odd U.card ∧ ∃ a ∈ U,∃ b ∈ U,a ≠ b ∧ T = {a,b} ∧
          (∀ v ∈ U,degree a ≤ degree v) ∧ ∀ v ∈ U,v ≠ a → degree b ≤ degree v))

theorem empty_active_operation_4_1_choice (active U : Finset V) (hU : U ⊆ active)
    (d floor budget : ℕ) (degree : V → ℕ) (hBudget : 1 ≤ budget)
    (hBound : ∀ v ∈ active,degree v ≤ d)
    (hNo : ¬HasAlmostOverfullRecord active d budget degree) :
    EmptyActiveChoice active U d floor degree := by
  let X := active \ U
  by_cases hEven : Even X.card
  · exact EmptyActiveChoice.even_core hEven
  have hOdd : Odd X.card := Nat.not_even_iff_odd.mp hEven
  let P := X.filter (fun v => degree v < d)
  by_cases hMany : 2 ≤ P.card
  · obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp hMany
    exact EmptyActiveChoice.charged_pair a b (mem_filter.mp ha).1 (mem_filter.mp hb).1
      hab (mem_filter.mp ha).2 (mem_filter.mp hb).2
  have hOne : ∀ x ∈ P,∀ y ∈ P,x = y := card_le_one.mp (by omega)
  by_cases hDeep : ∃ x ∈ X,degree x+2 ≤ d
  · obtain ⟨x,hx,hDeepX⟩ := hDeep
    refine EmptyActiveChoice.omit x hx hDeepX ?_ hOdd
    intro v hv hvx
    have hB := hBound v (mem_sdiff.mp hv).1
    have hxP : x ∈ P := mem_filter.mpr ⟨hx,by omega⟩
    by_contra hne
    have hvP : v ∈ P := mem_filter.mpr ⟨hv,by omega⟩
    exact hvx (hOne v hvP x hxP)
  have hMass : (∑ v ∈ X,(d-degree v)) ≤ 1 := by
    have hSum : (∑ v ∈ P,(d-degree v)) = ∑ v ∈ X,(d-degree v) := by
      apply sum_subset (filter_subset _ _)
      intro v hv hn
      have h := hBound v (mem_sdiff.mp hv).1
      have h' : ¬degree v < d := fun h => hn (mem_filter.mpr ⟨hv,h⟩)
      omega
    rw [←hSum]
    calc
      _ ≤ ∑ _v ∈ P,1 := sum_le_sum (fun v hv => by
        have h := (mem_filter.mp hv).1
        have hn : ¬degree v+2 ≤ d := fun hh => hDeep ⟨v,h,hh⟩
        omega)
      _ ≤ _ := by simpa using (show P.card ≤ 1 by omega)
  by_cases hSpecial : ∃ z ∈ U,floor+2 ≤ degree z
  · obtain ⟨z,hz,hHigh⟩ := hSpecial
    exact EmptyActiveChoice.special z hz hHigh hMass hOdd
  obtain ⟨T,hT,hParity,hSmall⟩ := exists_critical_active_vertices active U hU d budget degree
    hBudget hBound hOdd hMass hNo
  exact EmptyActiveChoice.switch_active T hT hParity
    (fun z hz => Nat.lt_of_not_ge (fun hh => hSpecial ⟨z,hz,hh⟩)) hOdd hMass hSmall

end OverfullWork.CMSTrimmingRound
