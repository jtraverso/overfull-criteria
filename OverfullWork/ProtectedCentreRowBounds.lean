module

public import OverfullWork.ResidueCopySelection

@[expose] public section


/-! # Bundle bounds in the protected saturated centre row

Good exchanges cannot remove a protected row. Once its degree reaches
the palette size, no incident bundle can grow either. The initial
centre run increases any bundle by at most its total centre gain.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem bundle_growth_le_degree_growth (M N : MultiGraph V) (a v : V) (d : ℕ)
    (hMono : ∀ w, M.mult s(a,w) ≤ N.mult s(a,w))
    (hDegree : N.degree a ≤ M.degree a+d) : N.mult s(a,v) ≤ M.mult s(a,v)+d := by
  have hOther := sum_le_sum (s := (univ.erase v)) (fun w _ => hMono w)
  have hM := sum_erase_add univ (fun w => M.mult s(a,w)) (mem_univ v)
  have hN := sum_erase_add univ (fun w => N.mult s(a,w)) (mem_univ v)
  rw [←M.degree_eq_sum_mult] at hM
  rw [←N.degree_eq_sum_mult] at hN
  omega

namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

theorem GoodRouteRun.protected_graph_row_mono {A E : Finset V} {h ell : ℕ}
    {P Q : M.PartialColouring k} {n t : ℕ} (run : GoodRouteRun A E h ell P Q n t)
    (a : V) (ha : a ∈ E) (v : V) : P.graph.mult s(a,v) ≤ Q.graph.mult s(a,v) := by
  induction run with
  | refl P => exact le_refl _
  | @step P Q n t i x y s hGood hCross hProtected hLen tail ih =>
    have hZero := hProtected a ha
    have hLe := s.removed.mult_pair_le_degree a v
    have hFirst : P.graph.mult s(a,v) ≤ s.result.graph.mult s(a,v) := by
      change P.graph.mult s(a,v) ≤ P.graph.mult s(a,v)-s.removed.mult s(a,v)+s.added.mult s(a,v)
      omega
    exact hFirst.trans ih

theorem GoodRouteRun.protected_saturated_bundle {A E : Finset V} {h ell : ℕ}
    {P Q : M.PartialColouring k} {n t : ℕ} (run : GoodRouteRun A E h ell P Q n t)
    (a : V) (ha : a ∈ E) (hSat : P.graph.degree a=k) (v : V) :
    Q.graph.mult s(a,v)=P.graph.mult s(a,v) := by
  have hDegree := Q.colouring.missingPalette_card_add_degree a
  have hBound := bundle_growth_le_degree_growth P.graph Q.graph a v 0
    (fun w => run.protected_graph_row_mono a ha w) (by omega)
  have hMono := run.protected_graph_row_mono a ha v
  omega

theorem ProtectedRun.centre_degree_gain {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (run : ProtectedRun a b w P Q n t) : Q.graph.degree a=P.graph.degree a+n := by
  induction run with
  | refl P => omega
  | step s tail ih => have hh := s.centre_gain;omega

theorem ProtectedRun.centre_bundle_growth_le {a b w : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (run : ProtectedRun a b w P Q n t) (v : V) :
    Q.graph.mult s(a,v) ≤ P.graph.mult s(a,v)+n := by
  apply bundle_growth_le_degree_growth P.graph Q.graph a v n
    (fun z => run.centre_bundle_mono z)
  rw [run.centre_degree_gain]

end PartialColouring
end SimpleGraph.MultiGraph
