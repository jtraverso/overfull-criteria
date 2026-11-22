module

public import OverfullWork.ScaledInternalCover
public import OverfullWork.WeightedEquitableRecolouring
public import OverfullWork.WeightedInternalRecolouring
public import OverfullWork.WeightedResidueBudget

@[expose] public section


/-! # Actual balanced sparse residue colouring with weighted centre loads -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Equitable alignment gives small classes in a sparse balanced residue. -/
theorem exists_equitable_scaled_residue_colouring (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t c : ℕ) (ht : 0<t) (hc : 0<c) (hbal : S.card=Sᶜ.card) (hreg : M.IsRegularOfDegree D)
    (hdeg : ∀ v,(M.internalPart S).degree v≤c*t)
    (hcentre : (M.internalPart S).degree x=0)
    (hcount : (M.internalPart S).edgeCount≤2*m*t) :
    ∃ C : (M.internalPart S).EdgeColoring (3*c*t),
      (∀ i,(C.colourGraph i).degree x=0) ∧
      (∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) ∧
      (∀ i j,(C.colourGraph i).edgesWithin S≤(C.colourGraph j).edgesWithin S+1) ∧
      ∀ i,(C.colourGraph i).edgesWithin S≤m/(3*c)+1 := by
  obtain ⟨A⟩:=(M.internalPart S).exists_edgeColoring_shannon (2*c*t) (fun v => (hdeg v).trans (by nlinarith))
  have hpalette : 3*(2*c*t)/2=3*c*t:=by
    rw [show 3*(2*c*t)=2*(3*c*t) by ring]
    omega
  rw [hpalette] at A
  have hA : Nonempty ((M.restrict S).EdgeColoring (3*c*t)) := by
    rw [←M.internalPart_restrict S]
    exact ⟨A.restrictColouring S⟩
  have hB : Nonempty ((M.restrict Sᶜ).EdgeColoring (3*c*t)) := by
    rw [←M.internalPart_restrict_compl S]
    exact ⟨A.restrictColouring Sᶜ⟩
  obtain ⟨C,hclasses,heq⟩:=M.exists_balanced_internal_colouring S D (3*c*t) hreg hbal hA hB
  have hsum : (∑ i,(C.colourGraph i).edgesWithin S)≤m*t := by
    rw [C.sum_edgesWithin,internalPart_edgesWithin]
    have hi:=M.internal_edge_counts_eq_of_regular S D hreg hbal
    rw [internalPart_edgeCount,←hi] at hcount
    nlinarith
  refine ⟨C,?_,hclasses,heq,?_⟩
  · intro i
    have h:=C.incidence_le_degree x i
    rw [hcentre] at h
    omega
  · intro i
    have hs : (3*c*t)*(C.colourGraph i).edgesWithin S≤
        (∑ j,(C.colourGraph j).edgesWithin S)+3*c*t := by
      have hh:=sum_le_sum (s:=univ) (fun j _ => heq i j)
      simpa only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,Nat.mul_one] using hh
    have hm : t*((3*c)*(C.colourGraph i).edgesWithin S)≤t*(m+3*c) := by nlinarith
    have hle:=Nat.le_of_mul_le_mul_left hm ht
    rw [←Nat.add_div_right m (show 0<3*c by omega)]
    apply (Nat.le_div_iff_mul_le (show 0<3*c by omega)).mpr
    nlinarith only [hle]


/-- Construct a balanced sparse residue colouring whose occupied weight
on the opposite side is bounded by floor(Doriginal/3)+2W. Weights need
only be bounded on that side and are kept fixed throughout recolouring. -/
theorem exists_weighted_residue_colouring (M : MultiGraph V) (S : Finset V) (x : V)
    (m Dr t c Doriginal W : ℕ) (ht : 0<t) (hc : 0<c)
    (hbal : S.card=Sᶜ.card) (hreg : M.IsRegularOfDegree Dr)
    (hdeg : ∀ v,(M.internalPart S).degree v≤c*t)
    (hcentre : (M.internalPart S).degree x=0)
    (hcount : (M.internalPart S).edgeCount≤2*m*t)
    (w : V → ℕ) (hw : ∀ v∈Sᶜ,w v≤W) (hsum : (∑ v∈Sᶜ,w v)≤Doriginal) :
    ∃ C : (M.internalPart S).EdgeColoring (3*c*t),
      (∀ i,(C.colourGraph i).degree x=0) ∧
      (∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) ∧
      (∀ i,(C.colourGraph i).edgesWithin S≤m/(3*c)+1) ∧
      ∀ i,(∑ v∈Sᶜ,w v*(C.colourGraph i).degree v)≤Doriginal/3+2*W := by
  obtain ⟨C,hCx,hCbal,hCeq,hCsmall⟩:=M.exists_equitable_scaled_residue_colouring
    S x m Dr t c ht hc hbal hreg hdeg hcentre hcount
  let wp : V → ℕ:=fun v => if v∈Sᶜ then w v else 0
  have hwp : ∀ v,wp v≤W := by
    intro v
    dsimp [wp]
    split_ifs with hv
    · exact hw v hv
    · exact Nat.zero_le _
  obtain ⟨B,hMass,hSpread⟩:=(C.restrictColouring Sᶜ).exists_weighted_preserving_mass wp W hwp
    (C.equitable_restrict_compl_of_internal_balance S hCbal hCeq)
  have hBdeg : ∀ v∈Sᶜ,((M.internalPart S).restrict Sᶜ).degree v≤c*t := by
    intro v hv
    apply le_trans ?_ (hdeg v)
    unfold degree
    apply sum_le_sum
    intro e he
    change (if e.toFinset⊆Sᶜ then (M.internalPart S).mult e else 0)≤(M.internalPart S).mult e
    split_ifs <;> omega
  have hLoadEq : ∀ i,B.coveredWeight Sᶜ w i=B.weightedLoad wp i := by
    intro i
    simp only [EdgeColoring.coveredWeight,EdgeColoring.weightedLoad,wp,ite_mul,zero_mul]
    rw [←sum_filter]
    simp only [filter_mem_eq_inter,univ_inter]
  have hloadB:=B.coveredWeight_le_third_floor_add Sᶜ w Doriginal W hc ht hBdeg hsum
    (by intro i j;rw [hLoadEq i,hLoadEq j];exact hSpread i j)
  have hloadBp : ∀ i,(∑ v∈Sᶜ,wp v*(B.colourGraph i).degree v)≤Doriginal/3+2*W := by
    intro i
    calc
      _ = ∑ v∈Sᶜ,w v*(B.colourGraph i).degree v := by
        apply sum_congr rfl
        intro v hv
        simp only [wp,if_pos hv]
      _ ≤ _:=hloadB i
  obtain ⟨C',hbal',heq',hv',hmissA,hmissB,hleft,hload'⟩:=
    exists_weighted_internal_recolouring S C B hMass hCbal hCeq wp (Doriginal/3+2*W) hloadBp
  refine ⟨C',?_,hbal',?_,?_⟩
  · intro i
    have hh:=C'.incidence_le_degree x i
    rw [hcentre] at hh
    omega
  · intro i
    have hi:=C.internal_missing_count S i
    have hi':=C'.internal_missing_count S i
    have hmiss:=hmissA i
    have hsmall:=hCsmall i
    omega
  · intro i
    calc
      _ = ∑ v∈Sᶜ,wp v*(C'.colourGraph i).degree v := by
        apply sum_congr rfl
        intro v hv
        simp only [wp,if_pos hv]
      _ ≤ _:=hload' i

end SimpleGraph.MultiGraph
