module

public import OverfullWork.KuhnOsthusPathPartitionSizes
public import OverfullWork.KuhnOsthusOrdinaryPathPieces

@[expose] public section


/-! Cut all ordinary style classes of the 1-factor at the same
capacity and track the unique piece containing each source. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedDemandHall
open scoped Classical
variable {V J : Type*} [Fintype V]

theorem exists_ordinary_factor_style_partition (σ : Equiv.Perm V)
    (S Z : Finset V) (label : V → J) (styleOf : V → J × J)
    (hFixed : ∀ x, σ x ≠ x)
    (hOrdinary : ∀ x ∈ S, x ∉ Z ∧ σ x ∉ Z)
    (hStyles : ∀ x ∈ S,
      label x ∈ ({(styleOf x).1,(styleOf x).2} : Finset J) ∧
        label (σ x) ∈ ({(styleOf x).1,(styleOf x).2} : Finset J))
    {k t : ℕ} (hk : 2 ≤ k)
    (hCapacity : ∀ j, (S.filter (fun x => styleOf x = j)).card ≤ k*t) :
    ∃ P : (J × J) × Fin k → Digraph V,
      (∀ i, IsDirectedPathSystem (P i) ∧ Fintype.card (Arc (P i)) ≤ t ∧
        SupportedByStyles label Z {i.1.1,i.1.2} (P i) ∧
        ∀ x y, (P i).Adj x y → x ∉ Z ∧ y ∉ Z) ∧
      (∀ x y, (x ∈ S ∧ σ x = y) ↔ ∃! i, (P i).Adj x y) := by
  classical
  let T (j : J × J) := S.filter (fun x => styleOf x = j)
  have hCut (j : J × J) := exists_bounded_acyclic_style_pieces σ (T j) hFixed hk (hCapacity j)
  choose F hF hOwner using hCut
  let P (i : (J × J) × Fin k) := factorArcsOn σ (F i.1 i.2)
  have hT (j : J × J) (i : Fin k) {x : V} (hx : x ∈ F j i) :
      x ∈ S ∧ styleOf x = j := mem_filter.mp ((hF j i).1 hx)
  refine ⟨P,?_,?_⟩
  · intro i
    refine ⟨⟨(hF i.1 i.2).2.2,?_,?_⟩,?_,?_,?_⟩
    · exact fun h g => h.2.symm.trans g.2
    · exact fun h g => σ.injective (h.2.trans g.2.symm)
    · let f (e : Arc (P i)) : F i.1 i.2 := ⟨e.val.1,e.prop.1⟩
      have hf : Function.Injective f := by
        intro a b he
        have hEq := congrArg (fun v : F i.1 i.2 => (v : V)) he
        exact Subtype.ext (Prod.ext hEq (a.prop.2.symm.trans ((congrArg σ hEq).trans b.prop.2)))
      exact (by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf :
        Fintype.card (Arc (P i)) ≤ (F i.1 i.2).card).trans (hF i.1 i.2).2.1
    · intro x _ hx
      rcases hx with ⟨y,hy⟩ | ⟨y,hy⟩
      · obtain ⟨hS,hj⟩ := hT i.1 i.2 hy.1
        simpa only [hj] using (hStyles x hS).1
      · obtain ⟨hS,hj⟩ := hT i.1 i.2 hy.1
        simpa only [hj,hy.2] using (hStyles y hS).2
    · intro x y h
      simpa only [h.2] using hOrdinary x (hT i.1 i.2 h.1).1
  · intro x y
    constructor
    · rintro ⟨hx,hy⟩
      have hxT : x ∈ T (styleOf x) := mem_filter.mpr ⟨hx,rfl⟩
      obtain ⟨i,hi,hUniq⟩ := hOwner (styleOf x) x hxT
      refine ⟨(styleOf x,i),⟨hi,hy⟩,?_⟩
      rintro ⟨j,k⟩ hk
      obtain ⟨_,he⟩ := hT j k hk.1
      subst j
      exact Prod.ext rfl (hUniq k hk.1)
    · rintro ⟨⟨j,k⟩,h,_⟩
      exact ⟨(hT j k h.1).1,h.2⟩

end OverfullWork.DirectedRobustExpansion
