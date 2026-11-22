module

public import OverfullWork.DoubleLayers
public import OverfullWork.PairedPartition

@[expose] public section


/-!
# A small additive colouring error for multiplicity two

Split the palette of the simple single-edge graph using the proved
sixth-moment partition. Add one copy of every double edge to each side.
The resulting layers are simple and have nearly equal degrees; Vizing
on each layer gives the final colouring. No multigraph Vizing axiom.
-/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_balanced_simple_layers (M : MultiGraph V) (d r : ℕ)
    (hmu : ∀ e,M.mult e≤2) (hdeg : ∀ v,M.degree v≤d)
    (hsize : 15*(Fintype.card V:ℝ)*(d/2+1:ℕ)^3<(2*r:ℝ)^6) :
    ∃ A B : MultiGraph V, A.addCopies B=M ∧ (∀ e,A.mult e≤1) ∧ (∀ e,B.mult e≤1) ∧
      ∀ v,A.degree v≤d/2+r ∧ B.degree v≤d/2+r := by
  let q:=d/2+1
  let n:=2*q
  have hg : ∀ v,M.singleGraph.degree v≤d := fun v => (M.single_degree_le v).trans (hdeg v)
  have hcol : M.singleGraph.EdgeColorable n := by
    apply (LeanPool.Vizing.lineGraph_colorable M.singleGraph).mono
    have h:=M.singleGraph.maxDegree_le_of_forall_degree_le d hg
    dsimp [n,q]
    omega
  obtain ⟨C⟩:=ofSimpleGraph_colouring M.singleGraph n hcol
  let w : V → Fin n → ℝ := fun v i => ((C.colourGraph i).degree v:ℝ)
  have hw : ∀ v i,0≤w v i ∧ w v i≤1 := by
    intro v i
    refine ⟨Nat.cast_nonneg _,?_⟩
    dsimp [w]
    exact_mod_cast C.colourGraph_degree_le_one i v
  let e : (Fin q×Bool) ≃ Fin n := Fintype.equivOfCardEq (by simp [n,Nat.mul_comm])
  obtain ⟨L,_,_,_,hdis⟩ := OverfullWork.PairedPartition.exists_balanced_partition e w hw
    (2*r:ℝ) (by positivity) hsize
  let A:=M.doubleLayer.addCopies (C.palettePart L)
  let B:=M.doubleLayer.addCopies (C.palettePart Lᶜ)
  have hAB : A.addCopies B=M := M.layers_add hmu C L
  refine ⟨A,B,hAB,M.simple_layer_of_palette C L,M.simple_layer_of_palette C Lᶜ,fun v => ?_⟩
  have hsum : A.degree v+B.degree v=M.degree v := by
    rw [←degree_addCopies,hAB]
  have hA : (A.degree v:ℝ)=(M.doubleLayer.degree v:ℝ)+∑ i∈L,w v i := by
    have h:=degree_addCopies M.doubleLayer (C.palettePart L) v
    rw [C.degree_palettePart] at h
    dsimp [A,w]
    exact_mod_cast h
  have hB : (B.degree v:ℝ)=(M.doubleLayer.degree v:ℝ)+∑ i∈Lᶜ,w v i := by
    have h:=degree_addCopies M.doubleLayer (C.palettePart Lᶜ) v
    rw [C.degree_palettePart] at h
    dsimp [B,w]
    exact_mod_cast h
  have he : (A.degree v:ℝ)-(B.degree v:ℝ)=(∑ i∈L,w v i)-(∑ i∈Lᶜ,w v i) := by rw [hA,hB]; ring
  have hd : |(A.degree v:ℝ)-(B.degree v:ℝ)|<(2*r:ℝ) := by rw [he]; exact hdis v
  obtain ⟨hl,hr⟩:=abs_lt.mp hd
  have hs : (A.degree v:ℝ)+(B.degree v:ℝ)≤(d:ℝ) := by
    exact_mod_cast hsum.le.trans (hdeg v)
  have h₁ : 2*A.degree v<d+2*r := by
    exact_mod_cast (show (2:ℝ)*(A.degree v:ℝ)<(d:ℝ)+2*(r:ℝ) by linarith)
  have h₂ : 2*B.degree v<d+2*r := by
    exact_mod_cast (show (2:ℝ)*(B.degree v:ℝ)<(d:ℝ)+2*(r:ℝ) by linarith)
  constructor <;> omega

/-- Explicit approximation with an additive error 2r+2 instead of the
multiplicative loss in Shannon. The size condition is fully numerical. -/
theorem exists_edgeColoring_multiplicity_two_approx (M : MultiGraph V) (d r : ℕ)
    (hmu : ∀ e,M.mult e≤2) (hdeg : ∀ v,M.degree v≤d)
    (hsize : 15*(Fintype.card V:ℝ)*(d/2+1:ℕ)^3<(2*r:ℝ)^6) :
    Nonempty (M.EdgeColoring (2*(d/2+r+1))) := by
  obtain ⟨A,B,hAB,hA,hB,hdeg⟩ := M.exists_balanced_simple_layers d r hmu hdeg hsize
  obtain ⟨C⟩:=A.exists_edgeColoring_simple (d/2+r) hA (fun v => (hdeg v).1)
  obtain ⟨F⟩:=B.exists_edgeColoring_simple (d/2+r) hB (fun v => (hdeg v).2)
  have h : Nonempty ((A.addCopies B).EdgeColoring ((d/2+r+1)+(d/2+r+1))) := ⟨C.addCopies F⟩
  rw [hAB] at h
  simpa only [two_mul] using h

end SimpleGraph.MultiGraph
