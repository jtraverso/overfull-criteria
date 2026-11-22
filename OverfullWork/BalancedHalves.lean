module

public import OverfullWork.FourLayers

@[expose] public section


/-! # Balanced binary splitting with a parameterized multiplicity cap -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem half_layer_of_palette_bound (M : MultiGraph V) (b : ℕ) (hmu : ∀ e,M.mult e≤2*b) {k : ℕ}
    (C : (ofSimpleGraph M.oddGraph).EdgeColoring k) (L : Finset (Fin k)) :
    ∀ e,(M.halfLayer.addCopies (C.palettePart L)).mult e≤b := by
  intro e
  have hh:=C.palettePart_mult_le L e
  rw [oddGraph_mult] at hh
  have hm:=hmu e
  change M.mult e/2+(C.palettePart L).mult e≤b
  split_ifs at hh <;> omega

theorem exists_balanced_halves (M : MultiGraph V) (d r b : ℕ)
    (hmu : ∀ e,M.mult e≤2*b) (hdeg : ∀ v,M.degree v≤d)
    (hsize : 15*(Fintype.card V:ℝ)*(d/2+1:ℕ)^3<(2*r:ℝ)^6) :
    ∃ A B : MultiGraph V, A.addCopies B=M ∧ (∀ e,A.mult e≤b) ∧ (∀ e,B.mult e≤b) ∧
      ∀ v,A.degree v≤d/2+r ∧ B.degree v≤d/2+r := by
  let q:=d/2+1
  let n:=2*q
  have hg : ∀ v,M.oddGraph.degree v≤d := fun v => (M.oddGraph_degree_le v).trans (hdeg v)
  have hcol : M.oddGraph.EdgeColorable n := by
    apply (LeanPool.Vizing.lineGraph_colorable M.oddGraph).mono
    have h:=M.oddGraph.maxDegree_le_of_forall_degree_le d hg
    dsimp [n,q]
    omega
  obtain ⟨C⟩:=ofSimpleGraph_colouring M.oddGraph n hcol
  let w : V → Fin n → ℝ := fun v i => ((C.colourGraph i).degree v:ℝ)
  have hw : ∀ v i,0≤w v i ∧ w v i≤1 := by
    intro v i
    refine ⟨Nat.cast_nonneg _,?_⟩
    dsimp [w]
    exact_mod_cast C.colourGraph_degree_le_one i v
  let e : (Fin q×Bool) ≃ Fin n := Fintype.equivOfCardEq (by simp [n,Nat.mul_comm])
  obtain ⟨L,_,_,_,hdis⟩ := OverfullWork.PairedPartition.exists_balanced_partition e w hw
    (2*r:ℝ) (by positivity) hsize
  let A:=M.halfLayer.addCopies (C.palettePart L)
  let B:=M.halfLayer.addCopies (C.palettePart Lᶜ)
  have hAB : A.addCopies B=M := M.half_layers_add C L
  refine ⟨A,B,hAB,M.half_layer_of_palette_bound b hmu C L,M.half_layer_of_palette_bound b hmu C Lᶜ,fun v => ?_⟩
  have hsum : A.degree v+B.degree v=M.degree v := by
    rw [←degree_addCopies,hAB]
  have hA : (A.degree v:ℝ)=(M.halfLayer.degree v:ℝ)+∑ i∈L,w v i := by
    have h:=degree_addCopies M.halfLayer (C.palettePart L) v
    rw [C.degree_palettePart] at h
    dsimp [A,w]
    exact_mod_cast h
  have hB : (B.degree v:ℝ)=(M.halfLayer.degree v:ℝ)+∑ i∈Lᶜ,w v i := by
    have h:=degree_addCopies M.halfLayer (C.palettePart Lᶜ) v
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


end SimpleGraph.MultiGraph
