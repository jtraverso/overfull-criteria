module

public import OverfullWork.SimpleColouringBridge
public import OverfullWork.AlignedInternal

@[expose] public section


/-! # Splitting multiplicity two into simple layers by splitting a palette -/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

def singleGraph (M : MultiGraph V) : SimpleGraph V where
  Adj u v := M.mult s(u,v)=1
  symm := ⟨by intro u v h; simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨by intro u h; have hz:=M.loopless s(u,u) (by simp); omega⟩

noncomputable instance (M : MultiGraph V) : DecidableRel M.singleGraph.Adj := Classical.decRel _

def doubleLayer (M : MultiGraph V) : MultiGraph V where
  mult e := if M.mult e=2 then 1 else 0
  loopless e he := by simp [M.loopless e he]

theorem singleGraph_mult (M : MultiGraph V) (e : Sym2 V) :
    (ofSimpleGraph M.singleGraph).mult e=if M.mult e=1 then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | hf u v => simp only [ofSimpleGraph,SimpleGraph.mem_edgeSet,singleGraph]

theorem doubleLayer_le_one (M : MultiGraph V) (e : Sym2 V) : M.doubleLayer.mult e≤1 := by
  dsimp only [doubleLayer]
  split_ifs <;> omega

theorem double_single_identity (M : MultiGraph V) (hmu : ∀ e,M.mult e≤2) (e : Sym2 V) :
    2*M.doubleLayer.mult e+(ofSimpleGraph M.singleGraph).mult e=M.mult e := by
  rw [singleGraph_mult]
  dsimp only [doubleLayer]
  have h:=hmu e
  split_ifs <;> omega

theorem single_degree_le (M : MultiGraph V) (v : V) : M.singleGraph.degree v≤M.degree v := by
  rw [←degree_ofSimpleGraph,degree_eq_sum_mult,degree_eq_sum_mult]
  apply sum_le_sum
  intro u _
  rw [singleGraph_mult]
  split_ifs <;> omega

def EdgeColoring.palettePart (C : M.EdgeColoring k) (L : Finset (Fin k)) : MultiGraph V where
  mult e := ∑ i∈L,C.col e i
  loopless e he := by
    apply sum_eq_zero
    intro i _
    exact col_eq_zero_of_isDiag M C he i

theorem EdgeColoring.palettePart_mult_le (C : M.EdgeColoring k) (L : Finset (Fin k)) (e : Sym2 V) :
    (C.palettePart L).mult e≤M.mult e := by
  change (∑ i∈L,C.col e i)≤M.mult e
  rw [←C.sum_col e]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

theorem EdgeColoring.palettePart_add_compl (C : M.EdgeColoring k) (L : Finset (Fin k)) (e : Sym2 V) :
    (C.palettePart L).mult e+(C.palettePart Lᶜ).mult e=M.mult e := by
  change (∑ i∈L,C.col e i)+(∑ i∈Lᶜ,C.col e i)=M.mult e
  rw [sum_add_sum_compl,C.sum_col]

theorem EdgeColoring.degree_palettePart (C : M.EdgeColoring k) (L : Finset (Fin k)) (v : V) :
    (C.palettePart L).degree v=∑ i∈L,(C.colourGraph i).degree v := by
  unfold degree
  exact sum_comm

theorem simple_layer_of_palette (M : MultiGraph V) {k : ℕ}
    (C : (ofSimpleGraph M.singleGraph).EdgeColoring k) (L : Finset (Fin k)) :
    ∀ e,(M.doubleLayer.addCopies (C.palettePart L)).mult e≤1 := by
  intro e
  have h:=C.palettePart_mult_le L e
  rw [singleGraph_mult] at h
  change (if M.mult e=2 then 1 else 0)+(C.palettePart L).mult e≤1
  split_ifs <;> split_ifs at h <;> omega

theorem layers_add (M : MultiGraph V) (hmu : ∀ e,M.mult e≤2) {k : ℕ}
    (C : (ofSimpleGraph M.singleGraph).EdgeColoring k) (L : Finset (Fin k)) :
    (M.doubleLayer.addCopies (C.palettePart L)).addCopies
      (M.doubleLayer.addCopies (C.palettePart Lᶜ))=M := by
  apply ext_mult
  intro e
  change (M.doubleLayer.mult e+(C.palettePart L).mult e)+
    (M.doubleLayer.mult e+(C.palettePart Lᶜ).mult e)=M.mult e
  have h₁:=C.palettePart_add_compl L e
  have h₂:=M.double_single_identity hmu e
  omega

end SimpleGraph.MultiGraph
