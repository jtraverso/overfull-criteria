module

public import OverfullWork.ApproximateMulticolouring
public import OverfullWork.MissingPairs

@[expose] public section


/-! # Internally balanced seeds with a small deficiency at every vertex

This replaces the multiplicative Shannon loss by an additive error.
The internal colour classes remain partial matchings: regular completion
is a separate obligation.
-/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem internalPart_restrict (M : MultiGraph V) (S : Finset V) :
    (M.internalPart S).restrict S=M.restrict S := by
  apply restrict_eq_of_pair_cover
  intro u hu v hv
  exact M.internalPart_covers S u v (by simp [hu,hv])

theorem internalPart_restrict_compl (M : MultiGraph V) (S : Finset V) :
    (M.internalPart S).restrict Sᶜ=M.restrict Sᶜ := by
  apply restrict_eq_of_pair_cover
  intro u hu v hv
  exact M.internalPart_covers S u v (by simp [mem_compl.mp hu,mem_compl.mp hv])

theorem EdgeColoring.missingSet_card_le_of_vertex_deficiency
    {M : MultiGraph V} {k : ℕ} (C : M.EdgeColoring k) (S : Finset V) (m t : ℕ)
    (hS : S.card=m) (hkm : m≤2*k) (hk : 0<k)
    (hvertex : ∀ v∈S,(C.missingPalette v).card≤t)
    (hcount : ∀ i,(C.missingSet S i).card+2*(C.colourGraph i).edgesWithin S=m)
    (heq : ∀ i j,(C.colourGraph i).edgesWithin S≤(C.colourGraph j).edgesWithin S+1) :
    ∀ i,(C.missingSet S i).card≤2*t+2 := by
  have hsum : (∑ i,(C.missingSet S i).card)≤m*t := by
    have hid:=C.total_missing_identity S
    have hsumv : (∑ v∈S,M.degree v)+m*t≥k*m := by
      have hp : ∀ v∈S,k≤M.degree v+t := by
        intro v hv
        have h:=C.missingPalette_card_add_degree v
        have h':=hvertex v hv
        omega
      have h:=sum_le_sum hp
      simpa [sum_add_distrib,hS,Nat.mul_comm,Nat.nsmul_eq_mul] using h
    rw [hS] at hid
    omega
  have hex : ∃ j : Fin k,(C.missingSet S j).card≤2*t := by
    by_contra hn
    have hall : ∀ j : Fin k,2*t<(C.missingSet S j).card := by
      intro j
      by_contra hh
      exact hn ⟨j,by omega⟩
    have hnempty : (univ : Finset (Fin k)).Nonempty := ⟨⟨0,hk⟩,mem_univ _⟩
    have hstrict := sum_lt_sum_of_nonempty hnempty (fun j _ => hall j)
    have hmul : m*t≤2*k*t := Nat.mul_le_mul_right t hkm
    simp only [sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at hstrict
    nlinarith
  obtain ⟨j,hj⟩:=hex
  intro i
  have hi:=hcount i
  have hj':=hcount j
  have h:=heq j i
  omega

/-- Construct a balanced equitable internal colouring whose palette is
near half the ambient regular degree. Both kinds of missing-colour
bounds are conclusions, not hypotheses about a chosen colouring. -/
theorem exists_efficient_balanced_internal (M : MultiGraph V) (S : Finset V)
    (m D r : ℕ) (hr : 1≤r) (hcard : Fintype.card V=2*m)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hreg : M.IsRegularOfDegree D)
    (hmu : ∀ e,M.mult e≤2) (hdense : m≤D)
    (hdis : ∀ v, |(M.degreeInto S v:ℝ)-(M.degreeInto Sᶜ v:ℝ)|<2*(r:ℝ))
    (hsize : 15*(2*m:ℝ)*((D/2+r)/2+1:ℕ)^3<(2*r:ℝ)^6) :
    ∃ (k : ℕ) (C : (M.internalPart S).EdgeColoring k),
      k≤D/2+3*r+2 ∧ m≤2*k ∧
      (∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) ∧
      (∀ i j,(C.colourGraph i).edgesWithin S≤(C.colourGraph j).edgesWithin S+1) ∧
      (∀ v,(C.missingPalette v).card≤4*r+4) ∧
      (∀ i,(C.missingSet S i).card=(C.missingSet Sᶜ i).card) ∧
      ∀ i,(C.missingSet S i).card≤8*r+10 := by
  let d:=D/2+r
  let k:=2*(d/2+r+1)
  have hbounds : ∀ v, D<2*(M.internalPart S).degree v+2*r ∧
      (M.internalPart S).degree v≤d := by
    intro v
    have hs : (M.degreeInto S v:ℝ)+(M.degreeInto Sᶜ v:ℝ)=(D:ℝ) := by
      exact_mod_cast (M.degreeInto_add_compl S v).trans (hreg v)
    obtain ⟨hl,hu⟩:=abs_lt.mp (hdis v)
    have hA : D<2*M.degreeInto S v+2*r ∧ 2*M.degreeInto S v<D+2*r := by
      constructor
      · exact_mod_cast (show (D:ℝ)<2*(M.degreeInto S v:ℝ)+2*(r:ℝ) by linarith)
      · exact_mod_cast (show 2*(M.degreeInto S v:ℝ)<(D:ℝ)+2*(r:ℝ) by linarith)
    have hB : D<2*M.degreeInto Sᶜ v+2*r ∧ 2*M.degreeInto Sᶜ v<D+2*r := by
      constructor
      · exact_mod_cast (show (D:ℝ)<2*(M.degreeInto Sᶜ v:ℝ)+2*(r:ℝ) by linarith)
      · exact_mod_cast (show 2*(M.degreeInto Sᶜ v:ℝ)<(D:ℝ)+2*(r:ℝ) by linarith)
    rw [degree_internalPart]
    by_cases hv : v∈S
    · rw [if_pos hv]; dsimp [d]; omega
    · rw [if_neg hv]; dsimp [d]; omega
  have hmuI : ∀ e,(M.internalPart S).mult e≤2 :=
    fun e => (M.internalPart_le S e).trans (hmu e)
  have hsize' : 15*(Fintype.card V:ℝ)*(d/2+1:ℕ)^3<(2*r:ℝ)^6 := by
    simpa only [hcard,Nat.cast_mul,Nat.cast_ofNat,d] using hsize
  obtain ⟨A⟩ := (M.internalPart S).exists_edgeColoring_multiplicity_two_approx d r hmuI
    (fun v => (hbounds v).2) hsize'
  have hA : Nonempty ((M.restrict S).EdgeColoring k) := by
    rw [←M.internalPart_restrict S]
    exact ⟨A.restrictColouring S⟩
  have hB : Nonempty ((M.restrict Sᶜ).EdgeColoring k) := by
    rw [←M.internalPart_restrict_compl S]
    exact ⟨A.restrictColouring Sᶜ⟩
  obtain ⟨C,hbal,heq⟩:=M.exists_balanced_internal_colouring S D k hreg (hS.trans hSc.symm) hA hB
  have hkm : m≤2*k := by dsimp [k,d]; omega
  have hk : 0<k := by dsimp [k]; omega
  have hvertex : ∀ v,(C.missingPalette v).card≤4*r+4 := by
    intro v
    have h:=C.missingPalette_card_add_degree v
    have hd:=(hbounds v).1
    dsimp [k,d] at h
    omega
  refine ⟨k,C,by dsimp [k,d]; omega,hkm,hbal,heq,hvertex,?_,?_⟩
  · exact C.missingSet_card_eq_of_internal_balance S (hS.trans hSc.symm) hbal
  · have h:=C.missingSet_card_le_of_vertex_deficiency S m (4*r+4) hS hkm hk
      (fun v _ => hvertex v) (fun i => by simpa only [hS] using C.internal_missing_count S i) heq
    intro i
    have hi:=h i
    omega

end SimpleGraph.MultiGraph
