module

public import OverfullWork.RobustSeedCompletion

@[expose] public section


/-! # Protected internal rows retain their actual edge-copy bundles

The residue update adds only the removed good matching. A protected row
has no such copies, so every incident internal bundle stays unchanged.
-/
namespace SimpleGraph.MultiGraph.PartialColouring.GoodRouteRun
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
variable {A E : Finset V} {h ell : ℕ} {P Q : M.PartialColouring k} {n t : ℕ}

theorem protected_internal_bundle (run : GoodRouteRun A E h ell P Q n t)
    (v : V) (hv : v ∈ E) (w : V) :
    (Q.available.internalPart A).mult s(v,w)=(P.available.internalPart A).mult s(v,w) := by
  induction run with
  | refl P => rfl
  | @step P Q n t i a b s hGood hCross hProtected hLen tail ih =>
    rw [ih,s.internal_residue A (s.removed_internal_of_good A h hGood) hCross]
    have hLe := s.removed.mult_pair_le_degree v w
    have hZero := hProtected v hv
    change (P.available.internalPart A).mult s(v,w)+s.removed.mult s(v,w)=_
    omega

end SimpleGraph.MultiGraph.PartialColouring.GoodRouteRun
