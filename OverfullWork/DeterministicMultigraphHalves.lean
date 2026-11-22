module

public import OverfullWork.BalancedHalves
public import OverfullWork.DeterministicHalving

@[expose] public section


/-! # Deterministic lifting of a split of the odd multiplicity layer -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Copies in the even layer are shared equally.  Only the simple odd
layer needs balancing. -/
theorem deterministic_halves_of_odd_halves (M : MultiGraph V) (d b : ℕ)
    (hmu : ∀ e, M.mult e ≤ 2*b) (hdeg : ∀ v, M.degree v ≤ d)
    (A B : MultiGraph V) (hAB : A.addCopies B = ofSimpleGraph M.oddGraph)
    (hbal : ∀ v, A.degree v ≤ B.degree v+2 ∧ B.degree v ≤ A.degree v+2) :
    ∃ P Q : MultiGraph V, P.addCopies Q=M ∧
      (∀ e,P.mult e≤b) ∧ (∀ e,Q.mult e≤b) ∧
      ∀ v,P.degree v≤d/2+1 ∧ Q.degree v≤d/2+1 := by
  let P := M.halfLayer.addCopies A
  let Q := M.halfLayer.addCopies B
  have hab (e : Sym2 V) : A.mult e+B.mult e=(ofSimpleGraph M.oddGraph).mult e := by
    exact congrArg (fun N : MultiGraph V => N.mult e) hAB
  have hPQ : P.addCopies Q=M := by
    apply ext_mult
    intro e
    have ho := M.half_odd_identity e
    have hh := hab e
    change (M.halfLayer.mult e+A.mult e)+(M.halfLayer.mult e+B.mult e)=M.mult e
    omega
  have hcaps (e : Sym2 V) : P.mult e≤b ∧ Q.mult e≤b := by
    have hh := hab e
    rw [M.oddGraph_mult] at hh
    have hm := hmu e
    change M.mult e/2+A.mult e≤b ∧ M.mult e/2+B.mult e≤b
    split_ifs at hh <;> omega
  refine ⟨P,Q,hPQ,fun e => (hcaps e).1,fun e => (hcaps e).2,fun v => ?_⟩
  have hs : P.degree v+Q.degree v=M.degree v := by rw [←degree_addCopies,hPQ]
  have ha : P.degree v=M.halfLayer.degree v+A.degree v := degree_addCopies _ _ _
  have hb : Q.degree v=M.halfLayer.degree v+B.degree v := degree_addCopies _ _ _
  have h := hbal v
  have hd := hdeg v
  omega

/-- Every bounded-multiplicity multigraph has balanced binary halves,
with a constant degree error and no size or moment hypothesis. -/
theorem exists_deterministic_halves (M : MultiGraph V) (d b : ℕ)
    (hmu : ∀ e,M.mult e≤2*b) (hdeg : ∀ v,M.degree v≤d) :
    ∃ P Q : MultiGraph V,P.addCopies Q=M ∧
      (∀ e,P.mult e≤b) ∧ (∀ e,Q.mult e≤b) ∧
      ∀ v,P.degree v≤d/2+1 ∧ Q.degree v≤d/2+1 := by
  obtain ⟨A,B,hAB,hbal⟩ := exists_deterministic_simple_halves M.oddGraph
  exact M.deterministic_halves_of_odd_halves d b hmu hdeg A B hAB hbal

end SimpleGraph.MultiGraph
