module

public import OverfullWork.OsthusStadenPhysicalBalance

@[expose] public section


/-! Project the multiplicities of the shadow graph to the p-cell pairs (38). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- A pair of cells receives the demand of its unique shadow edge, if
there is one. Both endpoint maps will be injective in the application. -/
noncomputable def shadowPairDemand {T U : Type*}
    (send receive : T → U) (M : T → T → ℕ) (u v : U) : ℕ :=
  if hs : u ∈ Set.range send then
    if hr : v ∈ Set.range receive then M (Classical.choose hs) (Classical.choose hr) else 0
  else 0

theorem shadowPairDemand_at_endpoints {T U : Type*}
    (send receive : T → U) (M : T → T → ℕ)
    (hSend : Function.Injective send) (hReceive : Function.Injective receive) (a b : T) :
    shadowPairDemand send receive M (send a) (receive b) = M a b := by
  have hs : send a ∈ Set.range send := ⟨a,rfl⟩
  have hr : receive b ∈ Set.range receive := ⟨b,rfl⟩
  unfold shadowPairDemand
  rw [dif_pos hs,dif_pos hr,hSend (Classical.choose_spec hs),hReceive (Classical.choose_spec hr)]

/-- A supported shadow matrix supplies a bounded demand on each
ordered p-cell pair, with zero demand off the physical reduced support. -/
theorem shadowPairDemand_le {T U : Type*}
    (Q : Digraph U) (send receive : T → U) (M : T → T → ℕ) (bound : ℕ)
    (hM : ∀ a b, M a b ≤ if Q.Adj (send a) (receive b) then bound else 0)
    (u v : U) : shadowPairDemand send receive M u v ≤ if Q.Adj u v then bound else 0 := by
  by_cases hs : u ∈ Set.range send
  · by_cases hr : v ∈ Set.range receive
    · rw [shadowPairDemand,dif_pos hs,dif_pos hr]
      simpa only [Classical.choose_spec hs,Classical.choose_spec hr] using
        hM (Classical.choose hs) (Classical.choose hr)
    · rw [shadowPairDemand,dif_pos hs,dif_neg hr]
      exact Nat.zero_le _
  · rw [shadowPairDemand,dif_neg hs]
    exact Nat.zero_le _

end OverfullWork.DirectedRobustExpansion
