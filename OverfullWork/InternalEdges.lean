module

public import OverfullWork.CenterPartition
public import OverfullWork.FactorizationAssembly
public import OverfullWork.ShannonBridge

@[expose] public section


namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def internalPart (M : MultiGraph V) (L : Finset V) : MultiGraph V where
  mult e := if e.toFinset ⊆ L ∨ e.toFinset ⊆ Lᶜ then M.mult e else 0
  loopless e he := by split_ifs <;> simp_all [M.loopless e he]

theorem internalPart_mult (M : MultiGraph V) (L : Finset V) (u v : V) :
    (M.internalPart L).mult s(u,v) = if (u ∈ L ↔ v ∈ L) then M.mult s(u,v) else 0 := by
  simp only [internalPart, Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff,
    mem_compl]
  by_cases hu : u ∈ L <;> by_cases hv : v ∈ L <;> simp [hu,hv]

theorem internalPart_le (M : MultiGraph V) (L : Finset V) (e : Sym2 V) :
    (M.internalPart L).mult e ≤ M.mult e := by
  dsimp only [internalPart]
  split_ifs <;> omega

theorem internalPart_covers (M : MultiGraph V) (L : Finset V) (u v : V)
    (h : u ∈ L ↔ v ∈ L) : (M.internalPart L).mult s(u,v) = M.mult s(u,v) := by
  rw [internalPart_mult,if_pos h]

theorem degree_internalPart (M : MultiGraph V) (L : Finset V) (v : V) :
    (M.internalPart L).degree v = if v ∈ L then M.degreeInto L v else M.degreeInto Lᶜ v := by
  rw [degree_eq_sum_mult]
  simp_rw [internalPart_mult]
  by_cases h : v ∈ L
  · simp [h,degreeInto]
  · simp only [h,false_iff,if_false]
    change (∑ u, if u ∉ L then M.mult s(v,u) else 0) = ∑ u ∈ Lᶜ, M.mult s(v,u)
    have hc : Lᶜ = univ.filter (fun u => u ∉ L) := by ext; simp
    rw [hc,sum_filter]

theorem degree_addCopies (M N : MultiGraph V) (v : V) :
    (M.addCopies N).degree v = M.degree v + N.degree v := by
  simp only [degree,addCopies,sum_add_distrib]

theorem bounded_allocation_fin (n : ℕ) (a : Fin n → ℕ) (q : ℕ) (hq : q ≤ ∑ i, a i) :
    ∃ r : Fin n → ℕ, (∀ i, r i ≤ a i) ∧ (∑ i, r i) = q := by
  induction n generalizing q with
  | zero =>
    have hq0 : q = 0 := by simpa using hq
    exact ⟨a,fun _ => le_rfl,by simp [hq0]⟩
  | succ n ih =>
    have htail : q-a 0 ≤ ∑ i : Fin n, a i.succ := by rw [Fin.sum_univ_succ] at hq; omega
    obtain ⟨r,hr,hs⟩ := ih (fun i => a i.succ) (q-a 0) htail
    refine ⟨Fin.cons (min q (a 0)) r,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa using hr j
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
      rw [hs]
      omega

omit [DecidableEq V] in
theorem bounded_allocation (a : V → ℕ) (q : ℕ) (hq : q ≤ ∑ v, a v) :
    ∃ r : V → ℕ, (∀ v, r v ≤ a v) ∧ (∑ v, r v) = q := by
  let e := Fintype.equivFin V
  have hs : (∑ i, a (e.symm i)) = ∑ v, a v := e.symm.sum_comp a
  obtain ⟨r,hr,hq⟩ := bounded_allocation_fin (Fintype.card V) (fun i => a (e.symm i)) q (by
    rwa [hs])
  refine ⟨fun v => r (e v),fun v => by simpa using hr (e v),?_⟩
  rw [e.sum_comp,hq]

def starCopies (x : V) (r : V → ℕ) (hx : r x = 0) : MultiGraph V where
  mult := Sym2.lift ⟨(fun u v => if u=x then r v else if v=x then r u else 0),by
    intro u v
    by_cases hu : u=x <;> by_cases hv : v=x <;> simp [hu,hv]⟩
  loopless e he := by
    induction e using Sym2.inductionOn with
    | hf u v =>
      have h := Sym2.mk_isDiag_iff.mp he
      subst v
      change (if u=x then r u else if u=x then r u else 0) = 0
      by_cases hu : u=x <;> simp [hu,hx]

omit [Fintype V] in
theorem starCopies_mult (x : V) (r : V → ℕ) (hx : r x=0) (u v : V) :
    (starCopies x r hx).mult s(u,v) = if u=x then r v else if v=x then r u else 0 := rfl

theorem degree_starCopies_center (x : V) (r : V → ℕ) (hx : r x=0) :
    (starCopies x r hx).degree x = ∑ v, r v := by
  rw [degree_eq_sum_mult]
  simp only [starCopies_mult,ite_true]

theorem degree_starCopies_other (x : V) (r : V → ℕ) (hx : r x=0) (v : V) (hv : v≠x) :
    (starCopies x r hx).degree v = r v := by
  rw [degree_eq_sum_mult]
  simp only [starCopies_mult,if_neg hv]
  simp

end SimpleGraph.MultiGraph
