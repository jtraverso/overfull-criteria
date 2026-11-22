module

public import OverfullWork.OrdinaryMatchingHamiltonPacking
public import OverfullWork.OrdinaryParallelMatchings

@[expose] public section


/-! Exact degree and copy accounting after the parallel matchings
of CMS §5.2, Case 1 have been covered by Hamilton layers. -/
namespace OverfullWork.EvenHamiltonFactorization

open Finset SimpleGraph MultiGraph CanonicalPairTriangle RobustExpansion
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The actual simple residue has degree `r-2ℓ`. Any colouring of it
extends using the two colours of each removed layer. -/
theorem regular_simple_residue_of_hamilton_layers (M : MultiGraph V) (r ℓ : ℕ)
    (hReg : M.IsRegularOfDegree r) (hDegree : 2*ℓ ≤ r)
    (J : Fin ℓ → MultiGraph V) (hJ : sumCopies univ J = M.parallelCopies)
    (F : Fin ℓ → SimpleGraph V) (hF : ∀ i, F i ≤ M.supportGraph)
    (hDis : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hLayers : ∀ i, let L := (ofSimpleGraph (F i)).addCopies (J i)
      L.IsRegularOfDegree 2 ∧ Nonempty (L.EdgeColoring 2)) :
    let H := M.supportGraph \ (⨆ i, F i)
    (∀ v, H.degree v = r-2*ℓ) ∧
    (Nonempty ((ofSimpleGraph H).EdgeColoring (r-2*ℓ)) → Nonempty (M.EdgeColoring r)) := by
  let H := M.supportGraph \ (⨆ i, F i)
  let L := fun i => (ofSimpleGraph (F i)).addCopies (J i)
  have hCount (x y : V) :
      (∑ i : Fin ℓ,(if (F i).Adj x y then 1 else 0 : ℕ)) =
        if (⨆ i, F i).Adj x y then 1 else 0 := by
    by_cases he : (⨆ i, F i).Adj x y
    · obtain ⟨i,hi⟩ := iSup_adj.mp he
      rw [if_pos he,sum_eq_single i]
      · simp [hi]
      · intro j _ hij
        apply if_neg
        intro hj
        exact (disjoint_iff_inf_le.mp (hDis j i hij)) ⟨hj,hi⟩
      · simp
    · have hn (i : Fin ℓ) : ¬ (F i).Adj x y := fun hi => he (iSup_adj.mpr ⟨i,hi⟩)
      simp [he,hn]
  have hSupportSplit : (ofSimpleGraph H).addCopies (sumCopies univ L) =
      (ofSimpleGraph M.supportGraph).addCopies (sumCopies univ J) := by
    apply ext_mult
    intro t
    induction t using Sym2.inductionOn with
    | hf x y =>
      change (if H.Adj x y then 1 else 0) +
        (∑ i : Fin ℓ, ((if (F i).Adj x y then 1 else 0) + (J i).mult s(x,y))) =
        (if M.supportGraph.Adj x y then 1 else 0) + ∑ i : Fin ℓ, (J i).mult s(x,y)
      rw [sum_add_distrib,hCount,←add_assoc]
      change ((if M.supportGraph.Adj x y ∧ ¬ (⨆ i, F i).Adj x y then 1 else 0) +
        (if (⨆ i, F i).Adj x y then 1 else 0)) + _ = _
      by_cases h : (⨆ i, F i).Adj x y
      · have hG : M.supportGraph.Adj x y := iSup_le hF h
        simp [h,hG]
      · simp [h]
  have hSplit : (ofSimpleGraph H).addCopies (sumCopies univ L) = M :=
    hSupportSplit.trans ((congrArg (fun C => (ofSimpleGraph M.supportGraph).addCopies C) hJ).trans
      M.simple_add_parallelCopies)
  have hLayerReg : (sumCopies univ L).IsRegularOfDegree (ℓ*2) :=
    ColouredLayerSum.regular L (fun i => (hLayers i).1)
  refine ⟨?_,?_⟩
  · intro v
    have hEq : H.degree v+(ℓ*2) = r := by
      have h := congrArg (fun X : MultiGraph V => X.degree v) hSplit
      rw [degree_addCopies,degree_ofSimpleGraph,hLayerReg,hReg] at h
      exact h
    change H.degree v = r-2*ℓ
    omega
  · rintro ⟨C⟩
    let D : ∀ i, (L i).EdgeColoring 2 := fun i => Classical.choice (hLayers i).2
    have hC := C.addCopies (ColouredLayerSum.colouring L D)
    rw [hSplit,show r-2*ℓ+ℓ*2 = r by omega] at hC
    exact ⟨hC⟩

end OverfullWork.EvenHamiltonFactorization
