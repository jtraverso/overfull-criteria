module

public import OverfullWork.ApproximateMulticolouring

@[expose] public section


/-! # Binary splitting for multiplicity four -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def halfLayer (M : MultiGraph V) : MultiGraph V where
  mult e:=M.mult e/2
  loopless e he:=by simp [M.loopless e he]

def oddGraph (M : MultiGraph V) : SimpleGraph V where
  Adj u v:=M.mult s(u,v)%2=1
  symm:=⟨by intro u v h;simpa only [Sym2.eq_swap] using h⟩
  loopless:=⟨by intro u h;have hh:=M.loopless s(u,u) (by simp);simp [hh] at h⟩

noncomputable instance (M : MultiGraph V) : DecidableRel M.oddGraph.Adj:=Classical.decRel _

omit [Fintype V] [DecidableEq V] in
theorem oddGraph_mult (M : MultiGraph V) (e : Sym2 V) :
    (ofSimpleGraph M.oddGraph).mult e=if M.mult e%2=1 then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | hf u v => simp only [ofSimpleGraph,mem_edgeSet,oddGraph]

omit [Fintype V] [DecidableEq V] in
theorem half_odd_identity (M : MultiGraph V) (e : Sym2 V) :
    2*M.halfLayer.mult e+(ofSimpleGraph M.oddGraph).mult e=M.mult e := by
  rw [oddGraph_mult]
  change 2*(M.mult e/2)+(if M.mult e%2=1 then 1 else 0)=M.mult e
  split_ifs <;> omega

theorem oddGraph_degree_le (M : MultiGraph V) (v : V) : M.oddGraph.degree v≤M.degree v := by
  rw [←degree_ofSimpleGraph,degree_eq_sum_mult,degree_eq_sum_mult]
  apply sum_le_sum
  intro w _
  rw [oddGraph_mult]
  split_ifs <;> omega

theorem double_layer_of_palette (M : MultiGraph V) (hmu : ∀ e,M.mult e≤4) {k : ℕ}
    (C : (ofSimpleGraph M.oddGraph).EdgeColoring k) (L : Finset (Fin k)) :
    ∀ e,(M.halfLayer.addCopies (C.palettePart L)).mult e≤2 := by
  intro e
  have hh:=C.palettePart_mult_le L e
  rw [oddGraph_mult] at hh
  have hm:=hmu e
  change M.mult e/2+(C.palettePart L).mult e≤2
  split_ifs at hh <;> omega

theorem half_layers_add (M : MultiGraph V) {k : ℕ}
    (C : (ofSimpleGraph M.oddGraph).EdgeColoring k) (L : Finset (Fin k)) :
    (M.halfLayer.addCopies (C.palettePart L)).addCopies
      (M.halfLayer.addCopies (C.palettePart Lᶜ))=M := by
  apply ext_mult
  intro e
  change (M.halfLayer.mult e+(C.palettePart L).mult e)+
    (M.halfLayer.mult e+(C.palettePart Lᶜ).mult e)=M.mult e
  have h₁:=C.palettePart_add_compl L e
  have h₂:=M.half_odd_identity e
  omega

theorem exists_balanced_double_layers (M : MultiGraph V) (d r : ℕ)
    (hmu : ∀ e,M.mult e≤4) (hdeg : ∀ v,M.degree v≤d)
    (hsize : 15*(Fintype.card V:ℝ)*(d/2+1:ℕ)^3<(2*r:ℝ)^6) :
    ∃ A B : MultiGraph V, A.addCopies B=M ∧ (∀ e,A.mult e≤2) ∧ (∀ e,B.mult e≤2) ∧
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
  refine ⟨A,B,hAB,M.double_layer_of_palette hmu C L,M.double_layer_of_palette hmu C Lᶜ,fun v => ?_⟩
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
