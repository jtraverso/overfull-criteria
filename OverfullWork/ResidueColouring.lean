module

public import OverfullWork.SparseInternalCompletion

@[expose] public section


namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem EdgeColoring.sum_edgesWithin {M : MultiGraph V} {k : ℕ} (C : M.EdgeColoring k) (S : Finset V) :
    (∑ i,(C.colourGraph i).edgesWithin S)=M.edgesWithin S := by
  unfold edgesWithin edgeCount
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  change (∑ i,if e.toFinset⊆S then C.col e i else 0)=(if e.toFinset⊆S then M.mult e else 0)
  by_cases he : e.toFinset⊆S
  · simp only [if_pos he,C.sum_col]
  · simp only [if_neg he,sum_const_zero]

theorem internalPart_edgeCount (M : MultiGraph V) (S : Finset V) :
    (M.internalPart S).edgeCount=M.edgesWithin S+M.edgesWithin Sᶜ := by
  rw [←restrict_add_restrict_compl,edgeCount_addCopies]
  rfl

theorem internalPart_edgesWithin (M : MultiGraph V) (S : Finset V) :
    (M.internalPart S).edgesWithin S=M.edgesWithin S :=
  congrArg edgeCount (M.internalPart_restrict S)

/-- Equitable alignment gives small classes in a sparse balanced residue. -/
theorem exists_small_residue_colouring (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t : ℕ) (ht : 0<t) (hbal : S.card=Sᶜ.card) (hreg : M.IsRegularOfDegree D)
    (hdeg : ∀ v,(M.internalPart S).degree v≤100*t)
    (hcentre : (M.internalPart S).degree x=0)
    (hcount : (M.internalPart S).edgeCount≤2*m*t) :
    ∃ C : (M.internalPart S).EdgeColoring (300*t),
      (∀ i,(C.colourGraph i).degree x=0) ∧
      (∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) ∧
      ∀ i,(C.colourGraph i).edgesWithin S≤m/300+1 := by
  obtain ⟨A⟩:=(M.internalPart S).exists_edgeColoring_shannon (200*t) (fun v => (hdeg v).trans (by omega))
  have hpalette : 3*(200*t)/2=300*t:=by omega
  rw [hpalette] at A
  have hA : Nonempty ((M.restrict S).EdgeColoring (300*t)) := by
    rw [←M.internalPart_restrict S]
    exact ⟨A.restrictColouring S⟩
  have hB : Nonempty ((M.restrict Sᶜ).EdgeColoring (300*t)) := by
    rw [←M.internalPart_restrict_compl S]
    exact ⟨A.restrictColouring Sᶜ⟩
  obtain ⟨C,hclasses,heq⟩:=M.exists_balanced_internal_colouring S D (300*t) hreg hbal hA hB
  have hsum : (∑ i,(C.colourGraph i).edgesWithin S)≤m*t := by
    rw [C.sum_edgesWithin,internalPart_edgesWithin]
    have hi:=M.internal_edge_counts_eq_of_regular S D hreg hbal
    rw [internalPart_edgeCount,←hi] at hcount
    nlinarith
  refine ⟨C,?_,hclasses,?_⟩
  · intro i
    have h:=C.incidence_le_degree x i
    rw [hcentre] at h
    omega
  · intro i
    have hs : (300*t)*(C.colourGraph i).edgesWithin S≤
        (∑ j,(C.colourGraph j).edgesWithin S)+300*t := by
      have hh:=sum_le_sum (s:=univ) (fun j _ => heq i j)
      simpa only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,Nat.mul_one] using hh
    have hm : t*(300*(C.colourGraph i).edgesWithin S)≤t*(m+300) := by nlinarith
    have hc:=Nat.le_of_mul_le_mul_left hm ht
    omega

end SimpleGraph.MultiGraph
