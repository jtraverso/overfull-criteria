module

public import OverfullWork.RouteExchange

@[expose] public section


/-! # Normalize both path certificates to the same route exchange

Reverse the extra matching pair in the second parity case and append
it to the paired route. Both cases then start and end with free edges.
-/
namespace OverfullWork.PairedRoutes
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

theorem AlternatingCertificate.normalize {τ : Equiv.Perm V} {F K : SimpleGraph V} {U : Finset V}
    {a b : V} {xs : List V} (hc : AlternatingCertificate τ F K U a b xs)
    (hτ : ∀ x, τ (τ x)=x) (hU : ∀ x ∈ U, τ x ∈ U) :
    ∃ (z : V) (n : ℕ) (r : Route τ F U z n),
      F.Adj a r.first ∧ F.Adj (τ z) b ∧ xs=a :: (r.vertices ++ [b]) := by
  rcases hc.2 with hc|hc
  · exact hc
  · obtain ⟨z,y,n,r,hy,hStart,hEnd,hLast,hxs⟩ := hc
    let r' := Route.snoc r (τ y) (hU y hy) hEnd
    refine ⟨τ y,n+1,r',hStart,?_,?_⟩
    · rw [hτ];exact hLast
    · change xs=a :: ((r.vertices ++ [τ y,τ (τ y)]) ++ [b])
      simpa only [hτ,List.append_assoc,List.cons_append,List.nil_append] using hxs

end OverfullWork.PairedRoutes
