module

public import OverfullWork.InitialForbiddenGrowth
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section


/-! # Layered routes through distinct matching pairs

CMS Case 2, Step 3 constructs paths backwards, excluding every already
used matching pair. These routes record each matching edge and each
intervening free edge; simplicity will follow from vertex-list Nodup.
-/
namespace OverfullWork.PairedRoutes
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

inductive Route (τ : Equiv.Perm V) (F : SimpleGraph V) (U : Finset V) : V → ℕ → Type _
  | single (x : V) (hx : x ∈ U) : Route τ F U x 0
  | snoc {x : V} {n : ℕ} (p : Route τ F U x n) (z : V) (hz : z ∈ U)
      (edge : F.Adj (τ x) z) : Route τ F U z (n+1)

namespace Route
variable {τ : Equiv.Perm V} {F : SimpleGraph V} {U : Finset V} {z : V} {n : ℕ}

def first : {z : V} → {n : ℕ} → Route τ F U z n → V
  | _,_,.single x _ => x
  | _,_,.snoc p _ _ _ => p.first

def vertices : {z : V} → {n : ℕ} → Route τ F U z n → List V
  | _,_,.single x _ => [x,τ x]
  | _,_,.snoc p z _ _ => p.vertices ++ [z,τ z]

theorem length_vertices (p : Route τ F U z n) : p.vertices.length=2*(n+1) := by
  induction p with
  | single x hx => simp [vertices]
  | snoc p z hz he ih => simp only [vertices,List.length_append,List.length_cons,List.length_nil];omega

theorem first_mem (p : Route τ F U z n) : p.first ∈ p.vertices := by
  induction p with
  | single x hx => simp [first,vertices]
  | snoc p z hz he ih => exact List.mem_append_left _ ih

theorem last_pair_mem (p : Route τ F U z n) : z ∈ p.vertices ∧ τ z ∈ p.vertices := by
  cases p with
  | single x hx => simp [vertices]
  | snoc p z hz he => simp [vertices]

theorem vertices_safe (p : Route τ F U z n) (hU : ∀ x ∈ U, τ x ∈ U) :
    ∀ v ∈ p.vertices, v ∈ U := by
  induction p with
  | single x hx =>
    intro v hv
    simp only [vertices,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with hv|hv
    · exact hv ▸ hx
    · exact hv ▸ hU x hx
  | snoc p z hz he ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv|hv
    · exact ih v hv
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with hv|hv
      · exact hv ▸ hz
      · exact hv ▸ hU z hz

def toWalk (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x)) :
    {z : V} → {n : ℕ} → (p : Route τ F U z n) → (F ⊔ K).Walk p.first (τ z)
  | _,_,.single x hx => Walk.cons (Or.inr (hK x hx)) Walk.nil
  | _,_,.snoc p z hz he => ((p.toWalk K hK).concat (Or.inl he)).concat (Or.inr (hK z hz))

theorem support_toWalk (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (p : Route τ F U z n) : (p.toWalk K hK).support=p.vertices := by
  induction p with
  | single x hx => rfl
  | snoc p z hz he ih =>
    dsimp only [toWalk,vertices,first]
    rw [SimpleGraph.Walk.support_concat,SimpleGraph.Walk.support_concat,ih]
    simp only [List.append_assoc,List.cons_append,List.nil_append]

theorem length_toWalk (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (p : Route τ F U z n) : (p.toWalk K hK).length=2*n+1 := by
  induction p with
  | single x hx => rfl
  | snoc p z hz he ih =>
    dsimp only [toWalk,first]
    rw [SimpleGraph.Walk.length_concat,SimpleGraph.Walk.length_concat,ih]
    omega

theorem toWalk_isPath (K : SimpleGraph V) (hK : ∀ x ∈ U, K.Adj x (τ x))
    (p : Route τ F U z n) (hp : p.vertices.Nodup) : (p.toWalk K hK).IsPath := by
  rw [SimpleGraph.Walk.isPath_def,p.support_toWalk K hK]
  exact hp

end Route
end OverfullWork.PairedRoutes
