module

public import OverfullWork.GeneralFreeColourMatching
public import OverfullWork.SparseInternalCompletion

@[expose] public section


namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Complete small internal classes simultaneously. The available graph
is recomputed after every colour; the bounds include the entire palette. -/
theorem exists_sparse_internal_cover_bounded (M : MultiGraph V) (S : Finset V) (x : V)
    (m D a k μ b : ℕ) (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤μ) (hstar : M.HasParallelBudget x b)
    (hroom : m+2*k+4*a+2*b+2≤2*D) (hcentre : k+2*μ*a<D)
    (C : (M.internalPart S).EdgeColoring k)
    (hcx : ∀ i,(C.colourGraph i).degree x=0)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hsmall : ∀ i,(C.colourGraph i).edgesWithin S≤a) :
    ∃ H : MultiGraph V,(∀ e,H.mult e≤M.mult e) ∧ H.IsRegularOfDegree k ∧
      Nonempty (H.EdgeColoring k) ∧
      ∀ u v,(u∈S ↔ v∈S) → H.mult s(u,v)=M.mult s(u,v) := by
  classical
  have hprocess : ∀ T : Finset (Fin k),∃ P : M.PartialColouring k,
      P.CoversInternal S ∧
      (∀ j∈T,(P.colouring.colourGraph j).IsRegularOfDegree 1) ∧
      (∀ j,j∉T → P.colouring.colourGraph j=C.colourGraph j) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      refine ⟨PartialColouring.internalSeed S C,?_,by simp,fun _ _ => rfl⟩
      intro u v huv
      exact M.internalPart_covers S u v huv
    | @insert i T hi ih =>
      obtain ⟨P,hcover,hfilled,hunfilled⟩:=ih
      have hCi:=hunfilled i hi
      obtain ⟨J,hJ,hdegree,hcross⟩:=P.exists_free_colour_matching_bounded S x m D a μ b hS hSc hx hreg hmu hstar
        hcover hroom hcentre i (by rw [hCi];exact hcx i)
        (by rw [hCi];exact C.internal_colour_cut_zero S i)
        (by rw [hCi];exact hbal i) (by rw [hCi];exact hsmall i)
      have hp : ∀ z,(P.colouring.colourGraph i).degree z+J.degree z≤1 := by
        intro z
        rw [hdegree]
        have hc:=P.colouring.colourGraph_degree_le_one i z
        split_ifs <;> omega
      let Q:=P.addMatching i J hJ hp
      have ho : ∀ j,j≠i → Q.colouring.colourGraph j=P.colouring.colourGraph j:=
        P.addMatching_other i J hJ hp
      have hselected : ∀ z,(Q.colouring.colourGraph i).degree z=1 := by
        intro z
        rw [P.addMatching_selected,degree_addCopies,hdegree]
        have hc:=P.colouring.colourGraph_degree_le_one i z
        split_ifs <;> omega
      refine ⟨Q,?_,?_,?_⟩
      · intro u v huv
        change P.graph.mult s(u,v)+J.mult s(u,v)=M.mult s(u,v)
        rw [hcover u v huv,hcross u v huv,Nat.add_zero]
      · intro j hj
        rcases mem_insert.mp hj with hj|hj
        · subst j
          exact hselected
        · have hji : j≠i:=fun he => hi (he ▸ hj)
          rw [ho j hji]
          exact hfilled j hj
      · intro j hj
        simp only [mem_insert,not_or] at hj
        rw [ho j hj.1]
        exact hunfilled j hj.2
  obtain ⟨P,hcover,hall,_⟩:=hprocess univ
  have hf : P.colouring.IsFactorization:=fun v i => hall i (mem_univ i) v
  exact ⟨P.graph,P.le,P.regular_of_factorization hf,⟨P.colouring⟩,hcover⟩

end SimpleGraph.MultiGraph
