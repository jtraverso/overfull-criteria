module

public import OverfullWork.StarBudgetOddCuts
public import OverfullWork.CriticalIdentificationEdges

@[expose] public section


/-! # Exclude centre triples that already contain a base edge

This local exclusion uses actual critical-edge inequalities, balanced
centre bundles and the degree-minimal centre of the small-centre branch.
The two-centre-bundle case pays only the sparse multiplicity cost 8Y.
-/
namespace OverfullWork.CriticalCentreTriples
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

omit [Fintype V] in
theorem triple_internal (M : MultiGraph V) (z a b : V)
    (hza : z≠a) (hzb : z≠b) (hab : a≠b) :
    M.twiceInternal {z,a,b}=2*(M.mult s(z,a)+M.mult s(z,b)+M.mult s(a,b)) := by
  have hLoop:∀v,M.mult s(v,v)=0:=fun v=>M.loopless _ (by simp)
  have haz:M.mult s(a,z)=M.mult s(z,a):=congrArg M.mult (Sym2.eq_swap)
  have hbz:M.mult s(b,z)=M.mult s(z,b):=congrArg M.mult (Sym2.eq_swap)
  have hba:M.mult s(b,a)=M.mult s(a,b):=congrArg M.mult (Sym2.eq_swap)
  simp [MultiGraph.twiceInternal,hza,hzb,hab,hLoop,haz,hbz,hba]
  ring

theorem triple_cut_identity (M : MultiGraph V) (z a b : V)
    (hza : z≠a) (hzb : z≠b) (hab : a≠b) :
    M.cutSize {z,a,b}+2*(M.mult s(z,a)+M.mult s(z,b)+M.mult s(a,b))=
      M.degree z+M.degree a+M.degree b := by
  have hh:=M.sum_degree_eq_internal_add_cut {z,a,b}
  rw [triple_internal M z a b hza hzb hab] at hh
  simp only [sum_insert,mem_insert,mem_singleton,hza,hzb,hab,or_self,
    not_false_eq_true,sum_singleton] at hh
  omega

theorem cut_of_base_edge (M : MultiGraph V) (Δ Y : ℕ) (z a b : V)
    (hza : z≠a) (hzb : z≠b) (hab : a≠b)
    (hstar : M.IsStarAt z) (hmult : ∀v,M.mult s(z,v)≤Y)
    (hMin : ∀v,M.degree z≤M.degree v)
    (hBalanced : ∀v,2*M.mult s(z,v)≤M.degree z)
    (hEdges : ∀u v,0<M.mult s(u,v) → Δ+2≤M.degree u+M.degree v)
    (hScale : 8*Y≤Δ+2)
    (hPositive : 0<M.mult s(z,a)+M.mult s(z,b)+M.mult s(a,b)) :
    Δ≤M.cutSize {z,a,b} := by
  have hId:=triple_cut_identity M z a b hza hzb hab
  have hOrdinary:M.mult s(a,b)≤1:=hstar a b hza.symm hzb.symm
  by_cases hA:0<M.mult s(z,a)
  · have hDA:=hEdges z a hA
    by_cases hB:0<M.mult s(z,b)
    · have hDB:=hEdges z b hB
      have hma:=hmult a
      have hmb:=hmult b
      have hMinA:=hMin a
      have hMinB:=hMin b
      omega
    · have hBal:=hBalanced a
      have hMinB:=hMin b
      omega
  · by_cases hB:0<M.mult s(z,b)
    · have hDB:=hEdges z b hB
      have hBal:=hBalanced b
      have hMinA:=hMin a
      omega
    · have hAB:0<M.mult s(a,b):=by omega
      have hh:=hEdges a b hAB
      omega

theorem cut_of_internal_positive (M : MultiGraph V) (Δ Y : ℕ) (z : V)
    (hstar : M.IsStarAt z) (hmult : ∀v,M.mult s(z,v)≤Y)
    (hMin : ∀v,M.degree z≤M.degree v)
    (hBalanced : ∀v,2*M.mult s(z,v)≤M.degree z)
    (hEdges : ∀u v,0<M.mult s(u,v) → Δ+2≤M.degree u+M.degree v)
    (hScale : 8*Y≤Δ+2) (S : Finset V) (hS : S.card=3) (hz : z∈S)
    (hPositive : 0<M.twiceInternal S) : Δ≤M.cutSize S := by
  have hErase:(S.erase z).card=2:=by have hh:=card_erase_add_one hz;omega
  obtain ⟨a,b,hab,hAB⟩:=card_eq_two.mp hErase
  have hza:z≠a:=by
    have ha:a∈S.erase z:=by rw [hAB];simp
    exact (mem_erase.mp ha).1.symm
  have hzb:z≠b:=by
    have hb:b∈S.erase z:=by rw [hAB];simp
    exact (mem_erase.mp hb).1.symm
  have hSet:S={z,a,b}:=by rw [←insert_erase hz,hAB]
  rw [hSet,triple_internal M z a b hza hzb hab] at hPositive
  rw [hSet]
  exact cut_of_base_edge M Δ Y z a b hza hzb hab hstar hmult hMin hBalanced
    hEdges hScale (by omega)

end OverfullWork.CriticalCentreTriples
