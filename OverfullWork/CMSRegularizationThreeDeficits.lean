module

public import OverfullWork.CMSRegularizationProfiles
public import OverfullWork.CanonicalTripleAddition

@[expose] public section


/-! The three-deficient-vertices alternative in CMS Claim 4.3. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph CanonicalTripleAddition
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cut_safe_when_additions_stay_inside (D M : MultiGraph V) (d : ℕ) (S : Finset V)
    (hReg : M.IsRegularOfDegree d) (hSub : ∀ e,D.mult e ≤ M.mult e)
    (hNo : ¬D.HasOverfullSubset d) (hEven : Even (Fintype.card V)) (hOdd : Odd S.card)
    (hOutside : ∀ v, v ∉ S → D.degree v = d) : d ≤ M.cutSize S := by
  have hComp := MultiGraph.odd_card_compl hEven hOdd
  have hSame : M.edgesWithin Sᶜ = D.edgesWithin Sᶜ := by
    apply congrArg MultiGraph.edgeCount
    apply MultiGraph.ext_mult
    intro e
    induction e using Sym2.inductionOn with
    | hf v w =>
      have hb := MultiGraph.degree_subtract_add M D hSub v
      by_cases hv : v ∈ Sᶜ
      · have hZ : (M.subtractCopies D).degree v = 0 := by
          rw [hOutside v (mem_compl.mp hv),hReg v] at hb
          omega
        have hh := (M.subtractCopies D).mult_pair_le_degree v w
        rw [hZ] at hh
        change M.mult s(v,w)-D.mult s(v,w) ≤ 0 at hh
        have hEq : M.mult s(v,w) = D.mult s(v,w) := by have hv' := hSub s(v,w); omega
        simp only [MultiGraph.restrict,hEq]
      · have hh : ¬s(v,w).toFinset ⊆ Sᶜ := fun h => hv (h (by simp))
        simp only [MultiGraph.restrict,if_neg hh]
  have hBound : M.edgesWithin Sᶜ ≤ d*(Sᶜ.card/2) := by
    rw [hSame]
    by_contra! hn
    exact hNo ⟨Sᶜ,hn⟩
  rw [←M.cutSize_compl S]
  by_contra! hCut
  have hh := (M.odd_overfull_iff_small_cut hReg Sᶜ hComp).mpr hCut
  have ho := M.twiceInternal_eq Sᶜ
  obtain ⟨j,hj⟩ := hComp
  have hRoom : Sᶜ.card-1 = 2*(Sᶜ.card/2) := by omega
  rw [hRoom] at hh
  nlinarith only [hh,hBound,ho]

theorem triple_cut_safe_of_spare_copy (M : MultiGraph V) (d : ℕ) (a b v w : V)
    (hReg : M.IsRegularOfDegree d) (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v)
    (hwb : w ≠ b) (hwv : w ≠ v) (hSpare : 0 < M.mult s(a,w))
    (hSimple : M.mult s(b,v) ≤ 1) :
    d ≤ M.cutSize {a,b,v} := by
  have hThree : (∑ x ∈ ({b,v,w}:Finset V), M.mult s(a,x)) ≤ M.degree a := by
    rw [MultiGraph.degree_eq_sum_mult]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have hB : b ∉ ({v,w}:Finset V) := by simp [hbv,hwb.symm]
  rw [sum_insert hB,sum_pair hwv.symm,hReg a] at hThree
  have hCut := CriticalCentreTriples.triple_cut_identity M a b v hab hav hbv
  rw [hReg a,hReg b,hReg v] at hCut
  omega

set_option maxHeartbeats 1700000 in
/-- If the only possible deficient vertices are the two anchors and
one third vertex, a simple second anchor leaves every triple safe. -/
theorem simple_second_triples_safe_of_three_deficits_away_from_first (D M : MultiGraph V) (d : ℕ) (a b w : V)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w) (hEven : Even (Fintype.card V))
    (hReg : M.IsRegularOfDegree d) (hSub : ∀ e, D.mult e ≤ M.mult e) (hNo : ¬D.HasOverfullSubset d)
    (hOrder : D.degree a ≤ D.degree b) (hW : D.degree w < d)
    (hOutside : ∀ v, v ∉ ({a,b,w}:Finset V) → D.degree v = d)
    (hSimple : ∀ v, v ≠ a → D.mult s(b,v) ≤ 1) :
    ∀ v, a ≠ v → b ≠ v → d ≤ M.cutSize {a,b,v} := by
  let A := M.subtractCopies D
  have hSum (v : V) : A.degree v + D.degree v = d := by
    have hh := MultiGraph.degree_subtract_add M D hSub v
    rwa [hReg v] at hh
  have hVanishing (v u : V) (hv : v ∉ ({a,b,w}:Finset V)) : A.mult s(v,u) = 0 := by
    have hd := hSum v
    rw [hOutside v hv] at hd
    have hh := A.mult_pair_le_degree v u
    omega
  have hLocal (v : V) : A.degree v = ∑ u ∈ ({a,b,w}:Finset V), A.mult s(v,u) := by
    rw [A.degree_eq_sum_mult]
    symm
    apply sum_subset (subset_univ _)
    intro x _ hx
    rw [Sym2.eq_swap]
    exact hVanishing x v hx
  have hLocalA := hLocal a
  have hLocalB := hLocal b
  have hLocalW := hLocal w
  have hA : a ∉ ({b,w}:Finset V) := by simp [hab,haw]
  have hLoop (v : V) : A.mult s(v,v) = 0 := A.loopless _ (by simp)
  rw [sum_insert hA,sum_pair hbw,hLoop a,zero_add] at hLocalA
  rw [sum_insert hA,sum_pair hbw,hLoop b,zero_add,Sym2.eq_swap (a := b) (b := a)] at hLocalB
  rw [sum_insert hA,sum_pair hbw,hLoop w,add_zero,Sym2.eq_swap (a := w) (b := a),
    Sym2.eq_swap (a := w) (b := b)] at hLocalW
  have hSpare : 0 < M.mult s(a,w) := by
    have ha := hSum a
    have hb := hSum b
    have hw := hSum w
    have hAvail : A.mult s(a,w) ≤ M.mult s(a,w) := Nat.sub_le _ _
    omega
  intro v hav hbv
  by_cases hv : v = w
  · subst v
    apply cut_safe_when_additions_stay_inside D M d {a,b,w} hReg hSub hNo hEven ?_ hOutside
    rw [show ({a,b,w}:Finset V).card = 3 by simp [hab,haw,hbw]]
    exact ⟨1,rfl⟩
  · have hN : v ∉ ({a,b,w}:Finset V) := by simp [hav.symm,hbv.symm,hv]
    have hZ := hVanishing v b hN
    have hEq : M.mult s(b,v) = D.mult s(b,v) := by
      rw [Sym2.eq_swap (a := v) (b := b)] at hZ
      change M.mult s(b,v)-D.mult s(b,v)=0 at hZ
      have hh := hSub s(b,v)
      omega
    exact triple_cut_safe_of_spare_copy M d a b v w hReg hab hav hbv hbw.symm (Ne.symm hv) hSpare
      (by rw [hEq]; exact hSimple v hav.symm)

theorem simple_second_triples_safe_of_three_deficits (D M : MultiGraph V) (d : ℕ) (a b w : V)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w) (hEven : Even (Fintype.card V))
    (hReg : M.IsRegularOfDegree d) (hSub : ∀ e, D.mult e ≤ M.mult e) (hNo : ¬D.HasOverfullSubset d)
    (hOrder : D.degree a ≤ D.degree b) (hW : D.degree w < d)
    (hOutside : ∀ v, v ∉ ({a,b,w}:Finset V) → D.degree v = d)
    (hSimple : ∀ v, D.mult s(b,v) ≤ 1) :
    ∀ v, a ≠ v → b ≠ v → d ≤ M.cutSize {a,b,v} := by
  exact simple_second_triples_safe_of_three_deficits_away_from_first D M d a b w hab haw hbw
    hEven hReg hSub hNo hOrder hW hOutside (fun v _ => hSimple v)

end OverfullWork.CanonicalRegularization
