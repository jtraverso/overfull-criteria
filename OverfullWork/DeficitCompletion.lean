module

public import OverfullWork.ParallelBudget
public import OverfullWork.CapacityPacking

@[expose] public section


/-! # Regular one-point completion after bounded old-vertex edge additions -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def deficitPair (B : MultiGraph V) (D : ℕ) : Option V → Option V → ℕ
  | none,none => 0
  | none,some v => D-B.degree v
  | some v,none => D-B.degree v
  | some u,some v => B.mult s(u,v)

theorem deficitPair_symm (B : MultiGraph V) (D : ℕ) (u v : Option V) :
    deficitPair B D u v=deficitPair B D v u := by
  cases u <;> cases v <;> simp only [deficitPair,Sym2.eq_swap]

def deficitExtension (B : MultiGraph V) (D : ℕ) : MultiGraph (Option V) where
  mult:=Sym2.lift ⟨deficitPair B D,deficitPair_symm B D⟩
  loopless:=by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have h:=Sym2.mk_isDiag_iff.mp he
      subst v
      cases u with
      | none => rfl
      | some u => exact B.loopless s(u,u) (by simp)

theorem deficitExtension_mult (B : MultiGraph V) (D : ℕ) (u v : Option V) :
    (B.deficitExtension D).mult s(u,v)=deficitPair B D u v := rfl

theorem total_deficit_of_bounded (B : MultiGraph V) (D : ℕ) (hdeg : ∀ v,B.degree v≤D) :
    (∑ v : V,B.degree v)+(∑ v : V,(D-B.degree v))=Fintype.card V*D := by
  rw [←sum_add_distrib]
  have hh : ∀ v,B.degree v+(D-B.degree v)=D:=fun v => Nat.add_sub_of_le (hdeg v)
  simp only [hh,sum_const,card_univ,Nat.nsmul_eq_mul]

theorem deficitExtension_regular (B : MultiGraph V) (D : ℕ) (hdeg : ∀ v,B.degree v≤D)
    (hsum : (∑ v : V,(D-B.degree v))=D) : (B.deficitExtension D).IsRegularOfDegree D := by
  intro v
  rw [degree_eq_sum_mult]
  cases v with
  | none =>
    simp only [Fintype.sum_option,deficitExtension_mult,deficitPair,Nat.zero_add]
    exact hsum
  | some v =>
    simp only [Fintype.sum_option,deficitExtension_mult,deficitPair]
    rw [←B.degree_eq_sum_mult]
    exact Nat.sub_add_cancel (hdeg v)

theorem deficitExtension_multiplicity (B : MultiGraph V) (D : ℕ)
    (hmu : ∀ e,B.mult e≤2) (hdef : ∀ v,D-B.degree v≤2) :
    ∀ e,(B.deficitExtension D).mult e≤2 := by
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [deficitExtension_mult]
    cases u <;> cases v
    · exact Nat.zero_le _
    · exact hdef _
    · exact hdef _
    · exact hmu _

theorem deficitExtension_parallel_budget (B : MultiGraph V) (D : ℕ)
    (hdef : ∀ v,D-B.degree v≤2) (hbudget : ∀ v,B.parallelExcess v≤2) :
    (B.deficitExtension D).HasParallelBudget none 3 := by
  intro v hv
  cases v with
  | none => exact False.elim (hv rfl)
  | some v =>
    change (∑ w : Option V,((B.deficitExtension D).mult s(some v,w)-1))≤3
    simp only [Fintype.sum_option,deficitExtension_mult,deficitPair]
    have h1:=hdef v
    have h2:=hbudget v
    change (∑ w : V,(B.mult s(v,w)-1))≤2 at h2
    omega

end SimpleGraph.MultiGraph
