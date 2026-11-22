module

public import OverfullWork.BoundedForkSelection
public import OverfullWork.CaoChenForkCounting

@[expose] public section


/-! # Constructed selection and a bounded potential for Cao--Chen Claim 5.3

The maximum is taken over admissible colourings with a fixed spine vertex.
The potential counts leaves possessing a good witness, so no selector is
silently held fixed while its domain changes under recolouring. This file
constructs the distinct anchors once that potential is large. The Kempe
augmentation needed to prove largeness is a separate remaining step.
-/
namespace OverfullWork.CaoChenForkSelection
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenForkCounting
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 3000000

/-- Admissible colourings retain the original missing edge and fixed spine vertex. -/
def RootedAdmissible (c : PEC G (Fin G.maxDegree)) (a b u : V) : Prop :=
  IsColMinus c a b ∧ ∃ α, c.col b u = some α ∧ c.IsFree a α

/-- Small second-neighbour leaves having a genuine A-coloured witness. -/
noncomputable def goodForkLeaves (c : PEC G (Fin G.maxDegree)) (a b u : V) (d : ℕ) : Finset V :=
  (goodSecondNeighbours c a b u ∩ smallVertices G d).filter fun t =>
    ∃ z ∈ goodNeighbours c a b u, Good c a b z t

theorem mem_goodForkLeaves (c : PEC G (Fin G.maxDegree)) (a b u : V) (d : ℕ) (t : V) :
    t ∈ goodForkLeaves c a b u d ↔ t ∈ goodSecondNeighbours c a b u ∧ G.degree t ≤ d ∧
      ∃ z ∈ goodNeighbours c a b u, Good c a b z t := by
  simp only [goodForkLeaves, mem_filter, mem_inter, smallVertices, mem_univ, true_and]
  tauto

/-- A maximizer exists among actual admissible colourings, without assuming
finiteness of the PEC structure or postulating a desirable configuration. -/
theorem exists_maximal_goodForkLeaves (c₀ : PEC G (Fin G.maxDegree)) (a b u : V) (d : ℕ)
    (h₀ : RootedAdmissible c₀ a b u) :
    ∃ c : PEC G (Fin G.maxDegree), RootedAdmissible c a b u ∧
      ∀ c' : PEC G (Fin G.maxDegree), RootedAdmissible c' a b u →
        (goodForkLeaves c' a b u d).card ≤ (goodForkLeaves c a b u d).card := by
  classical
  let P : ℕ → Prop := fun n => ∃ c : PEC G (Fin G.maxDegree),
    RootedAdmissible c a b u ∧ (goodForkLeaves c a b u d).card = n
  have hp₀ : P (goodForkLeaves c₀ a b u d).card := ⟨c₀, h₀, rfl⟩
  have hb₀ : (goodForkLeaves c₀ a b u d).card ≤ Fintype.card V := card_le_univ _
  obtain ⟨c, hc, hvalue⟩ := Nat.findGreatest_spec hb₀ hp₀
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  have hb' : (goodForkLeaves c' a b u d).card ≤ Fintype.card V := card_le_univ _
  have hle := Nat.le_findGreatest hb' (show P (goodForkLeaves c' a b u d).card from ⟨c', hc', rfl⟩)
  rwa [hvalue]

/-- A large good-leaf potential yields d+2 distinct anchors and distinct
small leaves with actual A-coloured edges. The local capacity follows from
criticality, rather than being an assumed expansion or matching. -/
theorem exists_good_anchors_of_many_goodForkLeaves (hcrit : IsDeltaCritical G)
    (c : PEC G (Fin G.maxDegree)) (a b u : V) (d : ℕ) (hd : 2 ≤ d)
    (hthreshold : 2 * d < G.maxDegree + 2)
    (hcount : (d + 1) * (d - 1) < (goodForkLeaves c a b u d).card) :
    ∃ z t : Fin (d + 2) → V, Function.Injective z ∧ Function.Injective t ∧
      ∀ i, z i ∈ goodNeighbours c a b u ∧ t i ∈ goodSecondNeighbours c a b u ∧
        G.degree (t i) ≤ d ∧ Good c a b (z i) (t i) := by
  classical
  have hcover : ∀ t ∈ goodForkLeaves c a b u d,
      ∃ z ∈ goodNeighbours c a b u, Good c a b z t := by
    intro t ht
    exact ((mem_goodForkLeaves c a b u d t).mp ht).2.2
  have hcap : ∀ z ∈ goodNeighbours c a b u,
      ((goodForkLeaves c a b u d).filter (Good c a b z)).card ≤ d - 1 := by
    intro z _hz
    have hsub : (goodForkLeaves c a b u d).filter (Good c a b z) ⊆
        ((insert z (G.neighborFinset z)).filter fun t => G.degree t ≤ d) := by
      intro t ht
      obtain ⟨htLeaf, htGood⟩ := mem_filter.mp ht
      obtain ⟨γ, hzt, _hγ⟩ := htGood
      have htSmall := ((mem_goodForkLeaves c a b u d t).mp htLeaf).2.1
      exact mem_filter.mpr ⟨mem_insert_of_mem ((mem_neighborFinset G z t).mpr (c.col_adj hzt)), htSmall⟩
    exact (card_le_card hsub).trans
      (CaoChenSmallNeighbourhood.closed_neighbourhood_small_degree_card_le G hcrit d hd hthreshold z)
  obtain ⟨z, t, hz, ht, hzt⟩ := exists_d_add_two_anchors_and_leaves
    (goodNeighbours c a b u) (goodForkLeaves c a b u d) (Good c a b) d hcover hcap hcount
  refine ⟨z, t, hz, ht, ?_⟩
  intro i
  obtain ⟨hzi, hti, hgood⟩ := hzt i
  have hleaf := (mem_goodForkLeaves c a b u d (t i)).mp hti
  exact ⟨hzi, hleaf.1, hleaf.2.1, hgood⟩

end OverfullWork.CaoChenForkSelection
