module

public import OverfullWork.GeneralSparseInternalCompletion

@[expose] public section


/-! # Splicing a mass-preserving weighted recolouring into one internal side

A replacement on the complementary side keeps its colour names and exact
per-colour masses. It therefore needs no new palette alignment, and all
original internal cardinality invariants survive.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

namespace EdgeColoring

/-- Restriction mass is the internal edge count of the original colour. -/
theorem colourMass_restrictColouring (C : M.EdgeColoring k) (S : Finset V) (i : Fin k) :
    (C.restrictColouring S).colourMass i=(C.colourGraph i).edgesWithin S := rfl

/-- The complementary restriction is equitable with its original
colour names, so a fixed-mass weighted recolouring can start directly. -/
theorem equitable_restrict_compl_of_internal_balance (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (heq : ∀ i j,(C.colourGraph i).edgesWithin S≤(C.colourGraph j).edgesWithin S+1) :
    (C.restrictColouring Sᶜ).IsEquitable := by
  intro i j
  rw [C.colourMass_restrictColouring Sᶜ i,C.colourMass_restrictColouring Sᶜ j,
    ←hbal i,←hbal j]
  exact heq i j

/-- Keep the original colours on S and splice the replacement on Sᶜ. -/
def spliceComplement (S : Finset V) (C : (M.internalPart S).EdgeColoring k)
    (B : ((M.internalPart S).restrict Sᶜ).EdgeColoring k) :
    (M.internalPart S).EdgeColoring k where
  col e i := if e.toFinset⊆S then C.col e i else B.col e i
  sum_col e := by
    by_cases heS : e.toFinset⊆S
    · simpa only [if_pos heS] using C.sum_col e
    · simp only [if_neg heS]
      rw [B.sum_col]
      change (if e.toFinset⊆Sᶜ then (M.internalPart S).mult e else 0)=(M.internalPart S).mult e
      by_cases heB : e.toFinset⊆Sᶜ
      · rw [if_pos heB]
      · have hz : (M.internalPart S).mult e=0:=by
          change (if e.toFinset⊆S ∨ e.toFinset⊆Sᶜ then M.mult e else 0)=0
          simp only [heS,heB,or_self,if_false]
        simp only [if_neg heB,hz]
  proper v i := by
    by_cases hv : v∈S
    · apply le_trans ?_ (C.proper v i)
      apply sum_le_sum
      intro e he
      by_cases heS : e.toFinset⊆S
      · simp only [if_pos heS]
        exact le_rfl
      · simp only [if_neg heS]
        have hvE : v∈e.toFinset:=by simpa using (mem_filter.mp he).2
        have hnB : ¬e.toFinset⊆Sᶜ:=fun hh => (mem_compl.mp (hh hvE)) hv
        rw [B.col_zero_outside_restrict Sᶜ e i hnB]
        exact Nat.zero_le _
    · have hh : (∑ e∈univ.filter (fun e : Sym2 V => v∈e),
          if e.toFinset⊆S then C.col e i else B.col e i)=
        ∑ e∈univ.filter (fun e : Sym2 V => v∈e),B.col e i := by
        apply sum_congr rfl
        intro e he
        have hvE : v∈e.toFinset:=by simpa using (mem_filter.mp he).2
        have hnS : ¬e.toFinset⊆S:=fun hs => hv (hs hvE)
        exact if_neg hnS
      rw [hh]
      exact B.proper v i

theorem spliceComplement_col_left (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k)
    (B : ((M.internalPart S).restrict Sᶜ).EdgeColoring k)
    (e : Sym2 V) (i : Fin k) (he : e.toFinset⊆S) :
    (C.spliceComplement S B).col e i=C.col e i := if_pos he

theorem spliceComplement_col_right (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k)
    (B : ((M.internalPart S).restrict Sᶜ).EdgeColoring k)
    (e : Sym2 V) (i : Fin k) (he : e.toFinset⊆Sᶜ) :
    (C.spliceComplement S B).col e i=B.col e i := by
  have hn : ¬e.toFinset⊆S := by
    intro hs
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hu : u∈s(u,v).toFinset:=by simp
      exact (mem_compl.mp (he hu)) (hs hu)
  exact if_neg hn

theorem spliceComplement_inside_left (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k)
    (B : ((M.internalPart S).restrict Sᶜ).EdgeColoring k) (i : Fin k) :
    ((C.spliceComplement S B).colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin S :=
  (C.spliceComplement S B).edgesWithin_eq_of_same_internal_colours C S i
    (fun e he => C.spliceComplement_col_left S B e i he)

theorem spliceComplement_inside_right (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k)
    (B : ((M.internalPart S).restrict Sᶜ).EdgeColoring k) (i : Fin k) :
    ((C.spliceComplement S B).colourGraph i).edgesWithin Sᶜ=(B.colourGraph i).edgesWithin Sᶜ :=
  (C.spliceComplement S B).edgesWithin_eq_of_same_internal_colours B Sᶜ i
    (fun e he => C.spliceComplement_col_right S B e i he)

theorem spliceComplement_degree_left (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k)
    (B : ((M.internalPart S).restrict Sᶜ).EdgeColoring k)
    (v : V) (hv : v∈S) (i : Fin k) :
    ((C.spliceComplement S B).colourGraph i).degree v=(C.colourGraph i).degree v := by
  unfold degree
  apply sum_congr rfl
  intro e he
  by_cases heS : e.toFinset⊆S
  · exact C.spliceComplement_col_left S B e i heS
  · have hvE : v∈e.toFinset:=by simpa using (mem_filter.mp he).2
    have hnB : ¬e.toFinset⊆Sᶜ:=fun hh => (mem_compl.mp (hh hvE)) hv
    have hC:=C.col_le_mult e i
    change C.col e i≤(if e.toFinset⊆S ∨ e.toFinset⊆Sᶜ then M.mult e else 0) at hC
    simp only [heS,hnB,or_self,if_false] at hC
    change (if e.toFinset⊆S then C.col e i else B.col e i)=C.col e i
    rw [if_neg heS,B.col_zero_outside_restrict Sᶜ e i hnB]
    omega

theorem spliceComplement_degree_right (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k)
    (B : ((M.internalPart S).restrict Sᶜ).EdgeColoring k)
    (v : V) (hv : v∈Sᶜ) (i : Fin k) :
    ((C.spliceComplement S B).colourGraph i).degree v=(B.colourGraph i).degree v := by
  unfold degree
  apply sum_congr rfl
  intro e he
  have hvE : v∈e.toFinset:=by simpa using (mem_filter.mp he).2
  have hnS : ¬e.toFinset⊆S:=fun hs => (mem_compl.mp hv) (hs hvE)
  exact if_neg hnS

theorem spliceComplement_weighted_right (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k)
    (B : ((M.internalPart S).restrict Sᶜ).EdgeColoring k)
    (w : V → ℕ) (i : Fin k) :
    (∑ v∈Sᶜ,w v*((C.spliceComplement S B).colourGraph i).degree v)=
      ∑ v∈Sᶜ,w v*(B.colourGraph i).degree v := by
  apply sum_congr rfl
  intro v hv
  rw [C.spliceComplement_degree_right S B v hv i]

/-- Exact masses retain both sides' original internal counts. -/
theorem spliceComplement_preserves_internal_counts (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k)
    (B : ((M.internalPart S).restrict Sᶜ).EdgeColoring k)
    (hMass : ∀ i,B.colourMass i=(C.restrictColouring Sᶜ).colourMass i) :
    ∀ i, ((C.spliceComplement S B).colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin S ∧
      ((C.spliceComplement S B).colourGraph i).edgesWithin Sᶜ=(C.colourGraph i).edgesWithin Sᶜ := by
  intro i
  refine ⟨C.spliceComplement_inside_left S B i,?_⟩
  rw [C.spliceComplement_inside_right S B i,←B.colourMass_eq_inside_restrict Sᶜ i,hMass i,
    C.colourMass_restrictColouring Sᶜ i]

end EdgeColoring

/-- Splice an actually supplied mass-preserving recolouring. The balanced
and equitable seed invariants are inherited without a new permutation. -/
theorem exists_weighted_internal_recolouring (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k)
    (B : ((M.internalPart S).restrict Sᶜ).EdgeColoring k)
    (hMass : ∀ i,B.colourMass i=(C.restrictColouring Sᶜ).colourMass i)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (heq : ∀ i j,(C.colourGraph i).edgesWithin S≤(C.colourGraph j).edgesWithin S+1)
    (w : V → ℕ) (L : ℕ) (hload : ∀ i,(∑ v∈Sᶜ,w v*(B.colourGraph i).degree v)≤L) :
    ∃ C' : (M.internalPart S).EdgeColoring k,
      (∀ i,(C'.colourGraph i).edgesWithin S=(C'.colourGraph i).edgesWithin Sᶜ) ∧
      (∀ i j,(C'.colourGraph i).edgesWithin S≤(C'.colourGraph j).edgesWithin S+1) ∧
      (∀ v,(C'.missingPalette v).card=(C.missingPalette v).card) ∧
      (∀ i,(C'.missingSet S i).card=(C.missingSet S i).card) ∧
      (∀ i,(C'.missingSet Sᶜ i).card=(C.missingSet Sᶜ i).card) ∧
      (∀ v∈S,∀ i,(C'.colourGraph i).degree v=(C.colourGraph i).degree v) ∧
      ∀ i,(∑ v∈Sᶜ,w v*(C'.colourGraph i).degree v)≤L := by
  let C':=C.spliceComplement S B
  have hcounts:=C.spliceComplement_preserves_internal_counts S B hMass
  refine ⟨C',?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    change ((C.spliceComplement S B).colourGraph i).edgesWithin S=
      ((C.spliceComplement S B).colourGraph i).edgesWithin Sᶜ
    rw [(hcounts i).1,(hcounts i).2]
    exact hbal i
  · intro i j
    change ((C.spliceComplement S B).colourGraph i).edgesWithin S≤
      ((C.spliceComplement S B).colourGraph j).edgesWithin S+1
    rw [(hcounts i).1,(hcounts j).1]
    exact heq i j
  · intro v
    exact C'.missingPalette_card_invariant C v
  · intro i
    have hc:=C.internal_missing_count S i
    have hc':=C'.internal_missing_count S i
    have hh:=(hcounts i).1
    change (C'.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin S at hh
    omega
  · intro i
    have hc:=C.internal_missing_count_compl S i
    have hc':=C'.internal_missing_count_compl S i
    have hh:=(hcounts i).2
    change (C'.colourGraph i).edgesWithin Sᶜ=(C.colourGraph i).edgesWithin Sᶜ at hh
    omega
  · intro v hv i
    exact C.spliceComplement_degree_left S B v hv i
  · intro i
    change (∑ v∈Sᶜ,w v*((C.spliceComplement S B).colourGraph i).degree v)≤L
    rw [C.spliceComplement_weighted_right S B w i]
    exact hload i

end SimpleGraph.MultiGraph
