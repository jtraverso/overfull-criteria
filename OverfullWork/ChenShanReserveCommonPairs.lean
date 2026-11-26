module

public import OverfullWork.ChenShanReservePatternMass
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset

/-- For two different outer vertices, the two arcs to each candidate
inner vertex are distinct from those of every other candidate.
Each arc may use either orientation. -/
def reserveCommonArcPairs {V : Type*} (Z : Finset V) (u v : V)
    (huv : u ≠ v) (hu : u ∉ Z) (hv : v ∉ Z) (orient : Bool → Bool) :
    (↥Z × Bool) ↪ (V × V) where
  toFun zb :=
    let a := if zb.2 then v else u
    if orient zb.2 then (a,zb.1.1) else (zb.1.1,a)
  inj' := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    have ha := a.2
    have hc := c.2
    have hau : a.1 ≠ u := fun e => hu (e ▸ ha)
    have hav : a.1 ≠ v := fun e => hv (e ▸ ha)
    have hcu : c.1 ≠ u := fun e => hu (e ▸ hc)
    have hcv : c.1 ≠ v := fun e => hv (e ▸ hc)
    cases b <;> cases d <;> cases hF : orient false <;> cases hT : orient true <;>
      simp only [hF,hT,Bool.false_eq_true,ite_false,ite_true,Prod.mk.injEq,Subtype.ext_iff] at h ⊢ <;>
      grind

end OverfullWork.ChenShan
