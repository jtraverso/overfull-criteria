module

public import OverfullWork.EvenPathClosure

@[expose] public section


/-! # Actual coloured spanning two-factors from ordinary Hamilton paths

The ordinary path is embedded into the original vertex type and closed
by the prescribed two boundary edges and one central pair edge. The
result has an explicit two-colouring and exact regularity.
-/
namespace OverfullWork.HamiltonPathClosure
open SimpleGraph Finset HeavyPairBoundary PathGraphRealization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V} {u v : outside a b}
set_option maxHeartbeats 5000000

theorem hamiltonian_endpoints_ne (p : (G.induce (outside a b : Set V)).Walk u v)
    (hp : p.IsHamiltonian) (hn : 2 ≤ Fintype.card ↥(outside a b)) : u ≠ v := by
  intro he
  subst v
  have hnil := (Walk.isPath_iff_nil.mp hp.isPath).eq_nil
  have hlen := hp.length_eq
  rw [hnil] at hlen
  change 0 = Fintype.card ↥(outside a b) - 1 at hlen
  omega

def ambientPath (p : (G.induce (outside a b : Set V)).Walk u v) : G.Walk u.val v.val :=
  p.map (Embedding.induce (outside a b : Set V)).toHom

theorem ambientPath_isPath (p : (G.induce (outside a b : Set V)).Walk u v)
    (hp : p.IsPath) : (ambientPath p).IsPath :=
  hp.map (show Function.Injective (Embedding.induce (outside a b : Set V)).toHom from
    Subtype.val_injective)

theorem ambientPath_support (p : (G.induce (outside a b : Set V)).Walk u v)
    (hp : p.IsHamiltonian) (w : V) : w ∈ (ambientPath p).support ↔ w ∈ outside a b := by
  have hs := Walk.support_map (Embedding.induce (outside a b : Set V)).toHom p
  change (ambientPath p).support = p.support.map (fun z => z.val) at hs
  rw [hs, List.mem_map]
  constructor
  · rintro ⟨z,_,hz⟩
    change z.val = w at hz
    exact hz ▸ z.property
  · intro hw
    exact ⟨⟨w,hw⟩, hp.mem_support _, rfl⟩

theorem ambientPath_adj_iff (p : (G.induce (outside a b : Set V)).Walk u v)
    (x y : outside a b) :
    (pathGraph (ambientPath p)).Adj x.val y.val ↔ (pathGraph p).Adj x y := by
  have hm := Walk.toSubgraph_map (Embedding.induce (outside a b : Set V)).toHom p
  change (ambientPath p).toSubgraph = _ at hm
  change (ambientPath p).toSubgraph.Adj x.val y.val ↔ p.toSubgraph.Adj x y
  rw [hm]
  constructor
  · rintro ⟨z,w,hadj,hz,hw⟩
    have hzx : z = x := Subtype.ext hz
    have hwy : w = y := Subtype.ext hw
    exact hzx ▸ hwy ▸ hadj
  · intro h
    exact ⟨x,y,h,rfl,rfl⟩

theorem ambientPath_degree (p : (G.induce (outside a b : Set V)).Walk u v)
    (hp : p.IsHamiltonian) (huv : u ≠ v) (w : V) :
    (pathGraph (ambientPath p)).degree w = if w = a ∨ w = b then 0
      else if w = u.val ∨ w = v.val then 1 else 2 := by
  have hq := ambientPath_isPath p hp.isPath
  have huvval : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  by_cases hout : w = a ∨ w = b
  · rw [if_pos hout]
    apply degree_outside
    intro hw
    have h := (mem_outside a b w).mp ((ambientPath_support p hp w).mp hw)
    rcases hout with rfl | rfl
    · exact h.1 rfl
    · exact h.2 rfl
  rw [if_neg hout]
  by_cases hwu : w = u.val
  · subst w
    rw [if_pos (Or.inl rfl)]
    exact degree_start _ hq huvval
  by_cases hwv : w = v.val
  · subst w
    rw [if_pos (Or.inr rfl)]
    exact degree_end _ hq huvval
  rw [if_neg (by tauto)]
  apply degree_internal _ hq ?_ hwu hwv
  apply (ambientPath_support p hp w).mpr
  simpa only [mem_outside, not_or] using hout

noncomputable def layer (p : (G.induce (outside a b : Set V)).Walk u v) (hab : a ≠ b) :
    MultiGraph V :=
  EvenPathClosure.closure (MultiGraph.ofSimpleGraph (pathGraph (ambientPath p))) a b hab u v

theorem layer_regular (p : (G.induce (outside a b : Set V)).Walk u v)
    (hab : a ≠ b) (hp : p.IsHamiltonian) (huv : u ≠ v) :
    (layer p hab).IsRegularOfDegree 2 := by
  apply EvenPathClosure.closure_regular _ a b hab u v huv
  intro w
  rw [MultiGraph.degree_ofSimpleGraph]
  exact ambientPath_degree p hp huv w

theorem layer_colourable (p : (G.induce (outside a b : Set V)).Walk u v)
    (hab : a ≠ b) (hp : p.IsHamiltonian) (huv : u ≠ v)
    (heven : Even (Fintype.card V)) : Nonempty ((layer p hab).EdgeColoring 2) := by
  have hq := ambientPath_isPath p hp.isPath
  have hc : (pathGraph (ambientPath p)).EdgeColorable 2 :=
    TwoColourTrimming.two_colourable_of_acyclic_and_degree_le_two _
      (isAcyclic _ hq) (degree_le_two _ hq)
  obtain ⟨C⟩ := MultiGraph.ofSimpleGraph_colouring _ 2 hc
  apply EvenPathClosure.closure_colourable C a b hab u v huv heven
  intro w
  rw [MultiGraph.degree_ofSimpleGraph]
  exact ambientPath_degree p hp huv w

end OverfullWork.HamiltonPathClosure
