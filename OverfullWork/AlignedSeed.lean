module

public import OverfullWork.AlignedInternal
public import OverfullWork.InternalSeed

@[expose] public section


namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem restrict_eq_of_pair_cover (M F : MultiGraph V) (S : Finset V)
    (h : ∀ u∈S, ∀ v∈S, F.mult s(u,v)=M.mult s(u,v)) : F.restrict S=M.restrict S := by
  apply ext_mult
  intro e
  change (if e.toFinset⊆S then F.mult e else 0)=(if e.toFinset⊆S then M.mult e else 0)
  by_cases he : e.toFinset⊆S
  · simp only [if_pos he]
    induction e using Sym2.inductionOn with
    | hf u v => exact h u (he (by simp)) v (he (by simp))
  · simp only [if_neg he]

end SimpleGraph.MultiGraph

namespace OverfullWork.MultigraphExtension

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Construct the internal recolouring and the aligning permutation from G.
The equal per-colour masses and per-side equitability are conclusions. -/
theorem exists_dense_point_aligned_internal (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (m : ℕ) (hm : 24576≤m) (hcard : Fintype.card V+1=2*m)
    (hgap : G.maxDegree-G.minDegree≤2)
    (hsat : 2*G.edgeFinset.card=G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1)≤7*G.maxDegree) :
    ∃ (L : Finset (Option V)) (k : ℕ)
      (C : ((pointExtension G).internalPart L).EdgeColoring k),
      L.card=m ∧ Lᶜ.card=m ∧ none∈L ∧ some y∉L ∧ k<G.maxDegree ∧ 7*k≤6*G.maxDegree ∧
      (∀ i, (C.colourGraph i).edgesWithin L=(C.colourGraph i).edgesWithin Lᶜ) ∧
      ∀ i j, (C.colourGraph i).edgesWithin L≤(C.colourGraph j).edgesWithin L+1 := by
  obtain ⟨L,F,k,hL,hB,hx,hy,hk,hbudget,hF,hcover,hFx,⟨C⟩⟩ :=
    exists_dense_point_coloured_seed G y m hm hcard hgap hsat hdense
  have hAeq : F.restrict L=(pointExtension G).restrict L :=
    MultiGraph.restrict_eq_of_pair_cover _ _ L (fun u hu v hv => hcover u v (by simp [hu,hv]))
  have hBeq : F.restrict Lᶜ=(pointExtension G).restrict Lᶜ :=
    MultiGraph.restrict_eq_of_pair_cover _ _ Lᶜ (fun u hu v hv => hcover u v (by
      have hu':=mem_compl.mp hu
      have hv':=mem_compl.mp hv
      simp [hu',hv']))
  have hA : Nonempty (((pointExtension G).restrict L).EdgeColoring k) := by
    rw [←hAeq]
    exact ⟨C.restrictColouring L⟩
  have hB' : Nonempty (((pointExtension G).restrict Lᶜ).EdgeColoring k) := by
    rw [←hBeq]
    exact ⟨C.restrictColouring Lᶜ⟩
  have hn : 1≤Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
  obtain ⟨B,hbal,heq⟩ := (pointExtension G).exists_balanced_internal_colouring L G.maxDegree k
    (regular_of_saturated G hn hsat) (hL.trans hB.symm) hA hB'
  exact ⟨L,k,B,hL,hB,hx,hy,hk,hbudget,hbal,heq⟩

end OverfullWork.MultigraphExtension
