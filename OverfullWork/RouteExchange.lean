module

public import OverfullWork.RouteCopyCapacity

@[expose] public section


/-! # Capacity-preserving variable-length route exchange

All removed/added copies are constructed from the route. Properness
follows from exact incidence counts and the two missing endpoints.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.PairedRoutes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 20000000

structure RouteInput (P : M.PartialColouring k) (i : Fin k) (a b : V) where
  mate : Equiv.Perm V
  freeGraph : SimpleGraph V
  eligible : Finset V
  last : V
  rounds : ℕ
  route : Route mate freeGraph eligible last rounds
  first_free : freeGraph.Adj a route.first
  last_free : freeGraph.Adj (mate last) b
  pair_ne : ∀ x ∈ eligible, x ≠ mate x
  pairs : ∀ x ∈ eligible, (P.colouring.colourGraph i).mult s(x,mate x)=1
  free : ∀ x y, freeGraph.Adj x y → 0 < P.available.mult s(x,y)
  simple : (a :: (route.vertices ++ [b])).Nodup
  distinct : a ≠ b
  first_missing : (P.colouring.colourGraph i).degree a=0
  last_missing : (P.colouring.colourGraph i).degree b=0

namespace RouteInput
variable {P : M.PartialColouring k} {i : Fin k} {a b : V}

def removed (s : RouteInput P i a b) : MultiGraph V := s.route.removedCopies s.pair_ne
def added (s : RouteInput P i a b) : MultiGraph V := s.route.addedCopies a b s.first_free s.last_free

theorem route_nodup (s : RouteInput P i a b) : s.route.vertices.Nodup :=
  (List.nodup_cons.mp s.simple).2.of_append_left

theorem removed_le (s : RouteInput P i a b) : ∀ e, s.removed.mult e ≤ P.colouring.col e i :=
  s.route.removed_le_of_pairs s.pair_ne s.route_nodup (P.colouring.colourGraph i)
    (fun x hx => (s.pairs x hx).ge)

theorem added_le (s : RouteInput P i a b) : ∀ e, s.added.mult e ≤ P.available.mult e :=
  s.route.added_le_of_free a b s.first_free s.last_free s.simple P.available s.free

theorem removed_degree (s : RouteInput P i a b) (v : V) : s.removed.degree v=s.route.vertices.count v :=
  s.route.degree_removedCopies s.pair_ne v

theorem added_degree (s : RouteInput P i a b) (v : V) : s.added.degree v=
    (if v=a then 1 else 0)+s.route.vertices.count v+(if v=b then 1 else 0) :=
  s.route.degree_addedCopies a b s.first_free s.last_free v

theorem removed_matching (s : RouteInput P i a b) (v : V) : s.removed.degree v ≤ 1 :=
  s.route.removed_degree_le_one s.pair_ne s.route_nodup v

theorem added_matching (s : RouteInput P i a b) (v : V) : s.added.degree v ≤ 1 :=
  s.route.added_degree_le_one a b s.first_free s.last_free s.simple v

theorem proper (s : RouteInput P i a b) (v : V) :
    ((P.colouring.colourGraph i).subtractCopies s.removed).degree v+s.added.degree v ≤ 1 := by
  have hSub := degree_subtract_add (P.colouring.colourGraph i) s.removed s.removed_le v
  have hOld := P.colouring.colourGraph_degree_le_one i v
  have hAdd := s.added_matching v
  by_cases hva : v=a
  · subst v;have hh := s.first_missing;omega
  by_cases hvb : v=b
  · subst v;have hh := s.last_missing;omega
  have hR := s.removed_degree v
  have hA := s.added_degree v
  rw [if_neg hva,if_neg hvb] at hA
  omega

def result (s : RouteInput P i a b) : M.PartialColouring k :=
  P.exchange i s.removed s.added s.removed_le s.added_le s.proper

theorem degree_change (s : RouteInput P i a b) (v : V) :
    s.result.graph.degree v=P.graph.degree v+(if v=a then 1 else 0)+(if v=b then 1 else 0) := by
  have hh := P.exchange_degree_identity i s.removed s.added s.removed_le s.added_le s.proper v
  change s.result.graph.degree v+s.removed.degree v=P.graph.degree v+s.added.degree v at hh
  have hR := s.removed_degree v
  have hA := s.added_degree v
  omega

theorem selected_degree_change (s : RouteInput P i a b) (v : V) :
    (s.result.colouring.colourGraph i).degree v=(P.colouring.colourGraph i).degree v+
      (if v=a then 1 else 0)+(if v=b then 1 else 0) := by
  have hEq := P.exchange_colour_selected i s.removed s.added s.removed_le s.added_le s.proper
  change s.result.colouring.colourGraph i=_ at hEq
  rw [hEq,degree_addCopies]
  have hSub := degree_subtract_add (P.colouring.colourGraph i) s.removed s.removed_le v
  have hR := s.removed_degree v
  have hA := s.added_degree v
  omega

theorem other_colour (s : RouteInput P i a b) (j : Fin k) (hj : j ≠ i) :
    s.result.colouring.colourGraph j=P.colouring.colourGraph j :=
  P.exchange_colour_other i s.removed s.added s.removed_le s.added_le s.proper j hj

theorem removed_count (s : RouteInput P i a b) : s.removed.edgeCount=s.rounds+1 :=
  s.route.edgeCount_removedCopies s.pair_ne

theorem added_count (s : RouteInput P i a b) : s.added.edgeCount=s.rounds+2 :=
  s.route.edgeCount_addedCopies a b s.first_free s.last_free

theorem size_change (s : RouteInput P i a b) : s.result.graph.edgeCount=P.graph.edgeCount+1 := by
  have hh := P.exchange_edgeCount_identity i s.removed s.added s.removed_le s.added_le s.proper
  change s.result.graph.edgeCount+s.removed.edgeCount=P.graph.edgeCount+s.added.edgeCount at hh
  rw [s.removed_count,s.added_count] at hh
  omega

theorem mass_change (s : RouteInput P i a b) :
    s.result.colouring.colourMass i=P.colouring.colourMass i+1 := by
  have hh := P.exchange_mass_identity i s.removed s.added s.removed_le s.added_le s.proper
  change s.result.colouring.colourMass i+s.removed.edgeCount=P.colouring.colourMass i+s.added.edgeCount at hh
  rw [s.removed_count,s.added_count] at hh
  omega

theorem missing_drop_two (s : RouteInput P i a b) :
    (P.colouring.missingSet univ i).card=(s.result.colouring.missingSet univ i).card+2 := by
  have hP := P.colouring.missing_card_add_twice_mass i
  have hQ := s.result.colouring.missing_card_add_twice_mass i
  have hMass := s.mass_change
  omega

end RouteInput
end SimpleGraph.MultiGraph.PartialColouring
