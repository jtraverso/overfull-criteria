module

public import OverfullWork.WeightedEquitableRecolouring
public import OverfullWork.WeightedInternalRecolouring
public import OverfullWork.WeightedMissingBudget

@[expose] public section


/-! # Constructing a weighted seed for the centre-first phase -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- Recolour the opposite side with exact labelled class sizes. This
constructs the weighted missing-set estimate used by the centre prefix. -/
theorem exists_weighted_centre_seed (M : MultiGraph V) (A : Finset V) (x : V)
    (k D t S : ℕ) (hk : 0<k) (hD : D≤4*k) (hreg : M.IsRegularOfDegree D)
    (hweight : ∀ v∈Aᶜ,M.mult s(x,v)≤S)
    (C : (M.internalPart A).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin A=(C.colourGraph i).edgesWithin Aᶜ)
    (heq : ∀ i j,(C.colourGraph i).edgesWithin A≤(C.colourGraph j).edgesWithin A+1)
    (hv : ∀ v,(C.missingPalette v).card≤t)
    (hc : ∀ i,(C.missingSet A i).card≤t) :
    ∃ B : (M.internalPart A).EdgeColoring k,
      (∀ i,(B.colourGraph i).edgesWithin A=(B.colourGraph i).edgesWithin Aᶜ) ∧
      (∀ v,(B.missingPalette v).card≤t) ∧
      (∀ i,(B.missingSet A i).card≤t) ∧
      ∀ i,(∑ v∈B.missingSet Aᶜ i,M.mult s(x,v))≤4*t+2*S := by
  let w : V → ℕ:=fun v => if v∈Aᶜ then M.mult s(x,v) else 0
  have hw : ∀ v,w v≤S := by
    intro v
    dsimp [w]
    split_ifs with h
    · exact hweight v h
    · exact Nat.zero_le _
  obtain ⟨B,hMass,hLoad⟩:=(C.restrictColouring Aᶜ).exists_weighted_preserving_mass w S hw
    (C.equitable_restrict_compl_of_internal_balance A hbal heq)
  let C':=C.spliceComplement A B
  have hcounts:=C.spliceComplement_preserves_internal_counts A B hMass
  have hbal' : ∀ i,(C'.colourGraph i).edgesWithin A=(C'.colourGraph i).edgesWithin Aᶜ := by
    intro i
    change ((C.spliceComplement A B).colourGraph i).edgesWithin A=
      ((C.spliceComplement A B).colourGraph i).edgesWithin Aᶜ
    rw [(hcounts i).1,(hcounts i).2,hbal i]
  have hv' : ∀ v,(C'.missingPalette v).card≤t := by
    intro v
    rw [C'.missingPalette_card_invariant C v]
    exact hv v
  have hc' : ∀ i,(C'.missingSet A i).card≤t := by
    intro i
    have h1:=C'.internal_missing_count A i
    have h2:=C.internal_missing_count A i
    have hh:=(hcounts i).1
    change (C'.colourGraph i).edgesWithin A=(C.colourGraph i).edgesWithin A at hh
    have hi:=hc i
    omega
  have hLoadEq : ∀ i,C'.coveredWeight Aᶜ (fun v => M.mult s(x,v)) i=B.weightedLoad w i := by
    intro i
    change (∑ v∈Aᶜ,M.mult s(x,v)*((C.spliceComplement A B).colourGraph i).degree v)=_
    rw [C.spliceComplement_weighted_right A B]
    simp only [EdgeColoring.weightedLoad,w,ite_mul,zero_mul]
    rw [←sum_filter]
    simp only [filter_mem_eq_inter,univ_inter]
  have hsum : (∑ v∈Aᶜ,M.mult s(x,v))≤D := by
    have h:=M.degreeInto_add_compl A x
    rw [hreg x] at h
    change M.degreeInto Aᶜ x≤D
    omega
  have hmissing:=C'.missingWeight_le_of_balanced_load Aᶜ (fun v => M.mult s(x,v))
    t D (2*S) hk hD (fun v _ => hv' v) hsum
    (by intro i j;rw [hLoadEq i,hLoadEq j];exact hLoad i j)
  exact ⟨C',hbal',hv',hc',hmissing⟩

end SimpleGraph.MultiGraph
