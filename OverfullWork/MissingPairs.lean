module

public import OverfullWork.AlignedSeed

@[expose] public section


/-! # Exact deficiency counts and pairing vertices missing the same colour -/

namespace SimpleGraph.MultiGraph.EdgeColoring

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

def missingSet (C : M.EdgeColoring k) (S : Finset V) (i : Fin k) : Finset V :=
  S.filter (fun v => (C.colourGraph i).degree v=0)

def missingPalette (C : M.EdgeColoring k) (v : V) : Finset (Fin k) :=
  univ.filter (fun i => (C.colourGraph i).degree v=0)

theorem missing_card_add_degree_sum (C : M.EdgeColoring k) (S : Finset V) (i : Fin k) :
    (C.missingSet S i).card+(∑ v∈S,(C.colourGraph i).degree v)=S.card := by
  rw [missingSet,card_eq_sum_ones,sum_filter,←sum_add_distrib,card_eq_sum_ones]
  apply sum_congr rfl
  intro v _
  have h:=C.colourGraph_degree_le_one i v
  split_ifs <;> omega

theorem sum_colour_degree (C : M.EdgeColoring k) (v : V) :
    (∑ i,(C.colourGraph i).degree v)=M.degree v := by
  simp only [degree,colourGraph]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  exact C.sum_col e

theorem missingPalette_card_add_degree (C : M.EdgeColoring k) (v : V) :
    (C.missingPalette v).card+M.degree v=k := by
  rw [←C.sum_colour_degree v,missingPalette,card_eq_sum_ones,sum_filter,←sum_add_distrib]
  calc
    _ = ∑ _i : Fin k, 1 := by
      apply sum_congr rfl
      intro i _
      have h:=C.colourGraph_degree_le_one i v
      split_ifs <;> omega
    _ = _ := by simp

theorem missingPalette_card_invariant (C B : M.EdgeColoring k) (v : V) :
    (C.missingPalette v).card=(B.missingPalette v).card := by
  have h₁:=C.missingPalette_card_add_degree v
  have h₂:=B.missingPalette_card_add_degree v
  omega

theorem total_missing_identity (C : M.EdgeColoring k) (S : Finset V) :
    (∑ i,(C.missingSet S i).card)+(∑ v∈S,M.degree v)=k*S.card := by
  have hsum := sum_congr (s₁:=univ) rfl (fun i _ => C.missing_card_add_degree_sum S i)
  rw [sum_add_distrib] at hsum
  have hdeg : (∑ i : Fin k, ∑ v∈S,(C.colourGraph i).degree v)=∑ v∈S,M.degree v := by
    rw [sum_comm]
    exact sum_congr rfl (fun v _ => C.sum_colour_degree v)
  rw [hdeg] at hsum
  simpa [Nat.nsmul_eq_mul] using hsum

theorem internal_colour_cut_zero (S : Finset V) (C : (M.internalPart S).EdgeColoring k) (i : Fin k) :
    (C.colourGraph i).cutSize S=0 := by
  unfold cutSize
  apply sum_eq_zero
  intro u hu
  apply sum_eq_zero
  intro v hv
  have hn : v∉S := mem_compl.mp hv
  have h:=C.col_le_mult s(u,v) i
  rw [internalPart_mult,if_neg (by simp [hu,hn])] at h
  change C.col s(u,v) i=0
  omega

theorem internal_missing_count (S : Finset V) (C : (M.internalPart S).EdgeColoring k) (i : Fin k) :
    (C.missingSet S i).card+2*(C.colourGraph i).edgesWithin S=S.card := by
  have h:=C.missing_card_add_degree_sum S i
  have hd:=(C.colourGraph i).sum_degree_eq_internal_add_cut S
  rw [twiceInternal_eq,C.internal_colour_cut_zero S i,Nat.add_zero] at hd
  omega

theorem internal_missing_count_compl (S : Finset V) (C : (M.internalPart S).EdgeColoring k) (i : Fin k) :
    (C.missingSet Sᶜ i).card+2*(C.colourGraph i).edgesWithin Sᶜ=Sᶜ.card := by
  have h:=C.missing_card_add_degree_sum Sᶜ i
  have hd:=(C.colourGraph i).sum_degree_eq_internal_add_cut Sᶜ
  rw [twiceInternal_eq,cutSize_compl,C.internal_colour_cut_zero S i,Nat.add_zero] at hd
  omega

theorem missingSet_card_eq_of_internal_balance (S : Finset V)
    (C : (M.internalPart S).EdgeColoring k) (hcard : S.card=Sᶜ.card)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) (i : Fin k) :
    (C.missingSet S i).card=(C.missingSet Sᶜ i).card := by
  have hA:=C.internal_missing_count S i
  have hB:=C.internal_missing_count_compl S i
  rw [hcard,hbal i] at hA
  omega

/-- The missing-common-colour pairs are constructed from the equal counts. -/
noncomputable def missingPairing (S : Finset V) (C : (M.internalPart S).EdgeColoring k)
    (hcard : S.card=Sᶜ.card)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) (i : Fin k) :
    C.missingSet S i ≃ C.missingSet Sᶜ i :=
  Finset.equivOfCardEq (C.missingSet_card_eq_of_internal_balance S hcard hbal i)

theorem missingPairing_distinct (S : Finset V) (C : (M.internalPart S).EdgeColoring k)
    (hcard : S.card=Sᶜ.card)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) (i : Fin k)
    (v : C.missingSet S i) : (v:V)≠((C.missingPairing S hcard hbal i v):V) := by
  intro he
  have h₁ : (v:V)∈S := (mem_filter.mp v.2).1
  have h₂ : ((C.missingPairing S hcard hbal i v):V)∉S :=
    mem_compl.mp (mem_filter.mp (C.missingPairing S hcard hbal i v).2).1
  exact h₂ (he ▸ h₁)

end SimpleGraph.MultiGraph.EdgeColoring

namespace OverfullWork.ShannonSeedBudget

/-- With the palette selected in InternalSeed, the number of colours
missing at the adjusted centre is necessarily linear in D. -/
theorem linear_centre_deficit (D : ℕ) (hD : 126≤D) :
    D≤3*(3*(4*D/7)/2-D/2) := by omega

theorem dense_centre_deficit (m D : ℕ) (hm : 24576≤m) (hdense : 12*m≤7*D) :
    4*m≤7*(3*(4*D/7)/2-D/2) := by
  have hD : 126≤D := by omega
  have h:=linear_centre_deficit D hD
  omega

end OverfullWork.ShannonSeedBudget
