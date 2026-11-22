module

public import OverfullWork.PaletteAlignment

@[expose] public section


/-! # Constructing an internally balanced colouring on an equipartition -/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M N : MultiGraph V} {k : ℕ}

theorem EdgeColoring.col_le_mult (C : M.EdgeColoring k) (e : Sym2 V) (i : Fin k) :
    C.col e i≤M.mult e := by
  rw [←C.sum_col e]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)

theorem EdgeColoring.incidence_le_degree (C : M.EdgeColoring k) (v : V) (i : Fin k) :
    (C.colourGraph i).degree v≤M.degree v := by
  unfold degree
  exact sum_le_sum (fun e _ => C.col_le_mult e i)

def EdgeColoring.restrictColouring (C : M.EdgeColoring k) (S : Finset V) :
    (M.restrict S).EdgeColoring k where
  col e i := if e.toFinset⊆S then C.col e i else 0
  sum_col e := by
    by_cases he : e.toFinset⊆S <;> simp only [he,ite_true,ite_false,sum_const_zero,C.sum_col,MultiGraph.restrict]
  proper v i := by
    exact (sum_le_sum (fun e _ => by split_ifs <;> omega)).trans (C.proper v i)

def EdgeColoring.addSamePalette (C : M.EdgeColoring k) (B : N.EdgeColoring k)
    (hdisj : ∀ v, M.degree v=0 ∨ N.degree v=0) : (M.addCopies N).EdgeColoring k where
  col e i := C.col e i+B.col e i
  sum_col e := by
    rw [sum_add_distrib,C.sum_col,B.sum_col]
    rfl
  proper v i := by
    rw [sum_add_distrib]
    have hC:=C.proper v i
    have hB:=B.proper v i
    have hCM:=C.incidence_le_degree v i
    have hBN:=B.incidence_le_degree v i
    change (∑ e ∈ univ.filter (fun e : Sym2 V => v∈e),C.col e i)≤M.degree v at hCM
    change (∑ e ∈ univ.filter (fun e : Sym2 V => v∈e),B.col e i)≤N.degree v at hBN
    rcases hdisj v with h|h
    · rw [h] at hCM; omega
    · rw [h] at hBN; omega

theorem restrict_add_restrict_compl (M : MultiGraph V) (S : Finset V) :
    (M.restrict S).addCopies (M.restrict Sᶜ)=M.internalPart S := by
  apply ext_mult
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    change (if s(u,v).toFinset⊆S then M.mult s(u,v) else 0)+
      (if s(u,v).toFinset⊆Sᶜ then M.mult s(u,v) else 0)=(M.internalPart S).mult s(u,v)
    rw [internalPart_mult]
    by_cases hu : u∈S <;> by_cases hv : v∈S <;>
      simp [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,hu,hv]

theorem restrict_vertex_disjoint (M : MultiGraph V) (S : Finset V) (v : V) :
    (M.restrict S).degree v=0 ∨ (M.restrict Sᶜ).degree v=0 := by
  by_cases hv : v∈S
  · right
    simp only [degree_restrict,mem_compl,not_true_eq_false,hv,if_false]
  · left
    simp only [degree_restrict,if_neg hv]

theorem EdgeColoring.col_zero_outside_restrict (S : Finset V) (C : (M.restrict S).EdgeColoring k)
    (e : Sym2 V) (i : Fin k) (he : ¬e.toFinset⊆S) : C.col e i=0 := by
  have h:=C.col_le_mult e i
  change C.col e i≤(if e.toFinset⊆S then M.mult e else 0) at h
  rw [if_neg he] at h
  omega

theorem EdgeColoring.colourMass_eq_inside_restrict (S : Finset V)
    (C : (M.restrict S).EdgeColoring k) (i : Fin k) :
    C.colourMass i=(C.colourGraph i).edgesWithin S := by
  unfold EdgeColoring.colourMass edgesWithin edgeCount
  apply sum_congr rfl
  intro e _
  change C.col e i=(if e.toFinset⊆S then C.col e i else 0)
  by_cases he : e.toFinset⊆S
  · rw [if_pos he]
  · rw [if_neg he,C.col_zero_outside_restrict S e i he]

theorem EdgeColoring.inside_compl_restrict_zero (S : Finset V)
    (C : (M.restrict S).EdgeColoring k) (i : Fin k) :
    (C.colourGraph i).edgesWithin Sᶜ=0 := by
  unfold edgesWithin edgeCount
  apply sum_eq_zero
  intro e _
  change (if e.toFinset⊆Sᶜ then C.col e i else 0)=0
  by_cases he : e.toFinset⊆Sᶜ
  · rw [if_pos he]
    have hn : ¬e.toFinset⊆S := by
      intro hh
      induction e using Sym2.inductionOn with
      | hf u v =>
        have h₁:=hh (by simp : u∈s(u,v).toFinset)
        have h₂:=he (by simp : u∈s(u,v).toFinset)
        exact (mem_compl.mp h₂) h₁
    exact C.col_zero_outside_restrict S e i hn
  · rw [if_neg he]

theorem EdgeColoring.inside_addSamePalette (C : M.EdgeColoring k) (B : N.EdgeColoring k)
    (hdisj : ∀ v, M.degree v=0 ∨ N.degree v=0) (S : Finset V) (i : Fin k) :
    ((C.addSamePalette B hdisj).colourGraph i).edgesWithin S=
      (C.colourGraph i).edgesWithin S+(B.colourGraph i).edgesWithin S := by
  unfold edgesWithin edgeCount
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  change (if e.toFinset⊆S then C.col e i+B.col e i else 0)=
    (if e.toFinset⊆S then C.col e i else 0)+(if e.toFinset⊆S then B.col e i else 0)
  split_ifs <;> omega

/-- The per-colour internal balance is constructed by recolouring each
side and aligning its palette, not assumed as an input invariant. -/
theorem exists_balanced_internal_colouring (M : MultiGraph V) (S : Finset V) (D k : ℕ)
    (hreg : M.IsRegularOfDegree D) (hbal : S.card=Sᶜ.card)
    (hA : Nonempty ((M.restrict S).EdgeColoring k))
    (hB : Nonempty ((M.restrict Sᶜ).EdgeColoring k)) :
    ∃ C : (M.internalPart S).EdgeColoring k,
      (∀ i, (C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) ∧
      ∀ i j, (C.colourGraph i).edgesWithin S≤(C.colourGraph j).edgesWithin S+1 := by
  obtain ⟨A⟩:=hA
  obtain ⟨B⟩:=hB
  have he : (M.restrict S).edgeCount=(M.restrict Sᶜ).edgeCount :=
    M.internal_edge_counts_eq_of_regular S D hreg hbal
  obtain ⟨A',B',hAeq,_,hclasses⟩:=A.exists_aligned_equitable_pair B he
  let C := A'.addSamePalette B' (M.restrict_vertex_disjoint S)
  have hC : ∃ C : ((M.restrict S).addCopies (M.restrict Sᶜ)).EdgeColoring k,
      (∀ i, (C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) ∧
      ∀ i j, (C.colourGraph i).edgesWithin S≤(C.colourGraph j).edgesWithin S+1 := by
    have hBzero (i : Fin k) : (B'.colourGraph i).edgesWithin S=0 := by
      simpa only [compl_compl] using B'.inside_compl_restrict_zero Sᶜ i
    refine ⟨C,?_,?_⟩
    · intro i
      rw [EdgeColoring.inside_addSamePalette,EdgeColoring.inside_addSamePalette]
      rw [←A'.colourMass_eq_inside_restrict S i,
        hBzero,A'.inside_compl_restrict_zero S i,
        ←B'.colourMass_eq_inside_restrict Sᶜ i]
      simpa only [Nat.zero_add,Nat.add_zero] using hclasses i
    · intro i j
      rw [EdgeColoring.inside_addSamePalette,EdgeColoring.inside_addSamePalette,
        hBzero,hBzero,←A'.colourMass_eq_inside_restrict S i,←A'.colourMass_eq_inside_restrict S j]
      simpa only [Nat.add_zero] using hAeq i j
  rwa [restrict_add_restrict_compl] at hC

end SimpleGraph.MultiGraph
