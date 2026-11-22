module

public import OverfullWork.DirectedRegularPairs
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Data.Finset.Preimage

@[expose] public section


/-! Faithful simple bipartite encoding of directed regular pairs.
An arc u -> v becomes the edge inl u -- inr v. This is only the
encoding step: a common directed partition with controlled vertex
losses is not supplied by an arbitrary partition of the two copies. -/
namespace OverfullWork.DirectedBipartiteEncoding
open Finset DirectedRobustExpansion DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 18000000

def graph (D : Digraph V) : SimpleGraph (V ⊕ V) where
  Adj x y := match x,y with
    | .inl u,.inr v => D.Adj u v
    | .inr v,.inl u => D.Adj u v
    | _,_ => False
  symm := ⟨by intro x y;cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x;cases x <;> exact id⟩

noncomputable def left (A : Finset V) : Finset (V ⊕ V) := A.map Function.Embedding.inl
noncomputable def right (A : Finset V) : Finset (V ⊕ V) := A.map Function.Embedding.inr

theorem left_card (A : Finset V) : (left A).card=A.card := card_map _
theorem right_card (A : Finset V) : (right A).card=A.card := card_map _

theorem interedges_card (D : Digraph V) (A B : Finset V) :
    ((graph D).interedges (left A) (right B)).card=incidences D A B := by
  simp only [SimpleGraph.interedges_def,card_filter,sum_product,left,right,sum_map]
  rw [sum_comm]
  simp only [incidences,inNeighbours,card_filter,graph]
  rfl

theorem density_eq (D : Digraph V) (A B : Finset V) :
    ((graph D).edgeDensity (left A) (right B):ℝ)=density D A B := by
  rw [SimpleGraph.edgeDensity_def]
  simp only [Rat.cast_div,Rat.cast_natCast,Rat.cast_mul,interedges_card,left_card,right_card,density]

theorem directed_uniform_of_encoded (D : Digraph V) (U W : Finset V) (ε : ℝ)
    (hUniform : (graph D).IsUniform ε (left U) (right W)) : IsUniform D ε U W := by
  intro A hA B hB hASize hBSize
  have hh := hUniform (show left A ⊆ left U from map_subset_map.mpr hA)
    (show right B ⊆ right W from map_subset_map.mpr hB)
    (by simpa only [left_card] using hASize) (by simpa only [right_card] using hBSize)
  simpa only [density_eq] using hh

theorem encoded_uniform_of_directed (D : Digraph V) (U W : Finset V) (ε : ℝ)
    (hUniform : IsUniform D ε U W) : (graph D).IsUniform ε (left U) (right W) := by
  intro A hA B hB hASize hBSize
  obtain ⟨A',hA',rfl⟩ := subset_map_iff.mp hA
  obtain ⟨B',hB',rfl⟩ := subset_map_iff.mp hB
  have hh := hUniform A' hA' B' hB'
    (by simpa only [card_map,left_card] using hASize)
    (by simpa only [card_map,right_card] using hBSize)
  change |((graph D).edgeDensity (left A') (right B'):ℝ)-
    ((graph D).edgeDensity (left U) (right W):ℝ)| < ε
  simpa only [density_eq] using hh

theorem uniform_iff (D : Digraph V) (U W : Finset V) (ε : ℝ) :
    (graph D).IsUniform ε (left U) (right W) ↔ IsUniform D ε U W :=
  ⟨directed_uniform_of_encoded D U W ε,encoded_uniform_of_directed D U W ε⟩

end OverfullWork.DirectedBipartiteEncoding
