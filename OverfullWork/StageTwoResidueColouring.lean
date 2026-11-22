module

public import OverfullWork.StageOneResidueColouring

@[expose] public section


/-! # Equitably color and align the actual remaining residue sides

Use Shannon on the verified residual degrees and the already proved
palette-alignment construction. Each new color has equal mass on both
sides and an explicit average bound. Anchor-row exclusions survive.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem restrict_le_internal_part (M : MultiGraph V) (A : Finset V) (e : Sym2 V) :
    (M.restrict A).mult e ≤ (M.internalPart A).mult e ∧
    (M.restrict Aᶜ).mult e ≤ (M.internalPart A).mult e := by
  change (if e.toFinset ⊆ A then M.mult e else 0) ≤
      (if e.toFinset ⊆ A ∨ e.toFinset ⊆ Aᶜ then M.mult e else 0) ∧
    (if e.toFinset ⊆ Aᶜ then M.mult e else 0) ≤
      (if e.toFinset ⊆ A ∨ e.toFinset ⊆ Aᶜ then M.mult e else 0)
  split_ifs <;> simp_all

theorem EdgeColoring.mass_bound_of_equitable {N : MultiGraph V} {k : ℕ}
    (C : N.EdgeColoring k) (hEq : C.IsEquitable) (i : Fin k) :
    k*C.colourMass i ≤ N.edgeCount+k := by
  have hh := sum_le_sum (s := (univ : Finset (Fin k))) (fun j _ => hEq i j)
  rw [sum_add_distrib,C.sum_colourMass] at hh
  simpa only [sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,mul_one] using hh

structure StageTwoResidueColouring (M : MultiGraph V) (A E : Finset V)
    (first : StageOneResidueColouring M A E) (h : ℕ) where
  left : ((M.restrict A).subtractCopies first.left).EdgeColoring (3*h)
  right : ((M.restrict Aᶜ).subtractCopies ((M.restrict Aᶜ).incidentOn E)).EdgeColoring (3*h)
  left_equitable : left.IsEquitable
  right_equitable : right.IsEquitable
  balance : ∀ i, left.colourMass i=right.colourMass i
  mass_bound : ∀ i, (3*h)*left.colourMass i ≤ ((M.restrict A).subtractCopies first.left).edgeCount+3*h
  cleared : ∀ v ∈ E, ∀ i, (right.colourGraph i).degree v=0

theorem StageOneResidueColouring.exists_stage_two_colouring {M : MultiGraph V} {A E : Finset V}
    (first : StageOneResidueColouring M A E) (h : ℕ)
    (hCap : ∀ v, (M.internalPart A).degree v ≤ h) :
    Nonempty (StageTwoResidueColouring M A E first h) := by
  let L := (M.restrict A).subtractCopies first.left
  let R := (M.restrict Aᶜ).subtractCopies ((M.restrict Aᶜ).incidentOn E)
  have hL : ∀ v, L.degree v ≤ h := by
    intro v
    have hh := (M.internalPart A).degree_le_of_mult_le L
      (fun e => (Nat.sub_le _ _).trans (restrict_le_internal_part M A e).1) v
    exact hh.trans (hCap v)
  have hR : ∀ v, R.degree v ≤ h := by
    intro v
    have hh := (M.internalPart A).degree_le_of_mult_le R
      (fun e => (Nat.sub_le _ _).trans (restrict_le_internal_part M A e).2) v
    exact hh.trans (hCap v)
  have hPalette : 3*(2*h)/2=3*h := by omega
  obtain ⟨CL⟩ := L.exists_edgeColoring_shannon (2*h) (fun v => (hL v).trans (by omega))
  obtain ⟨CR⟩ := R.exists_edgeColoring_shannon (2*h) (fun v => (hR v).trans (by omega))
  rw [hPalette] at CL CR
  obtain ⟨CL',CR',hCL',hCR',hAlign⟩ := CL.exists_aligned_equitable_pair CR first.balance
  refine ⟨{
    left := CL', right := CR', left_equitable := hCL', right_equitable := hCR',
    balance := hAlign, mass_bound := CL'.mass_bound_of_equitable hCL', cleared := ?_
  }⟩
  intro v hv i
  have hh := CR'.incidence_le_degree v i
  have hZero := first.cleared v hv
  change R.degree v=0 at hZero
  omega

end SimpleGraph.MultiGraph
