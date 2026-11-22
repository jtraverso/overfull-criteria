module

public import OverfullWork.KuhnOsthusStyleSchedule
public import OverfullWork.KuhnOsthusOrdinaryStylePartition

@[expose] public section


/-! The ordinary part of the 1-factor uses one class for each unordered
double style. The proof chooses a compatible class for each arc. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
variable {V : Type*} [Fintype V]

theorem exists_ordinary_double_style_pieces (σ : Equiv.Perm V) (Z : Finset V)
    (label : V → Fin 50) (hFixed : ∀ x, σ x ≠ x) {q t : ℕ}
    (hq : 2 ≤ q) (hCapacity : Fintype.card V ≤ q*t) :
    ∃ A : DoubleStyle × Fin q → Digraph V,
      (∀ k, IsDirectedPathSystem (A k) ∧ Fintype.card (Arc (A k)) ≤ t ∧
        SupportedByStyles label Z k.1.val (A k) ∧
        (∀ x y, (A k).Adj x y → σ x = y ∧ x ∉ Z ∧ y ∉ Z)) ∧
      ∀ x y, (σ x = y ∧ x ∉ Z ∧ y ∉ Z) ↔ ∃! k, (A k).Adj x y := by
  classical
  have hStyle (x : V) := exists_double_style (label x) (label (σ x))
  choose style hStyle using hStyle
  let S (j : DoubleStyle) := univ.filter (fun x => x ∉ Z ∧ σ x ∉ Z ∧ style x = j)
  have hCut (j : DoubleStyle) := exists_bounded_acyclic_style_pieces σ (S j) hFixed hq
    ((card_le_univ _).trans hCapacity)
  choose F hF hOwner using hCut
  let A (k : DoubleStyle × Fin q) := factorArcsOn σ (F k.1 k.2)
  have hMem (k : DoubleStyle × Fin q) {x : V} (hx : x ∈ F k.1 k.2) :
      x ∉ Z ∧ σ x ∉ Z ∧ style x = k.1 := (mem_filter.mp ((hF k.1 k.2).1 hx)).2
  refine ⟨A,?_,?_⟩
  · intro k
    refine ⟨⟨(hF k.1 k.2).2.2,?_,?_⟩,?_,?_,?_⟩
    · exact fun h g => h.2.symm.trans g.2
    · exact fun h g => σ.injective (h.2.trans g.2.symm)
    · let f (e : Arc (A k)) : F k.1 k.2 := ⟨e.val.1,e.prop.1⟩
      have hf : Function.Injective f := by
        intro a b he
        have hEq := congrArg (fun v : F k.1 k.2 => (v : V)) he
        exact Subtype.ext (Prod.ext hEq (a.prop.2.symm.trans ((congrArg σ hEq).trans b.prop.2)))
      exact (by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf :
        Fintype.card (Arc (A k)) ≤ (F k.1 k.2).card).trans (hF k.1 k.2).2.1
    · intro x _ hx
      rcases hx with ⟨y,hy⟩ | ⟨y,hy⟩
      · simpa only [(hMem k hy.1).2.2] using (hStyle x).1
      · simpa only [(hMem k hy.1).2.2,hy.2] using (hStyle y).2
    · intro x y h
      exact ⟨h.2,(hMem k h.1).1,h.2 ▸ (hMem k h.1).2.1⟩
  · intro x y
    constructor
    · rintro ⟨he,hx,hy⟩
      have hs : x ∈ S (style x) := mem_filter.mpr ⟨mem_univ _,hx,he.symm ▸ hy,rfl⟩
      obtain ⟨i,hi,hi'⟩ := hOwner (style x) x hs
      refine ⟨(style x,i),⟨hi,he⟩,?_⟩
      rintro ⟨j,k⟩ hk
      have hj := (hMem (j,k) hk.1).2.2
      dsimp only at hj
      subst j
      exact Prod.ext rfl (hi' k hk.1)
    · rintro ⟨k,h,_⟩
      exact ⟨h.2,(hMem k h.1).1,h.2 ▸ (hMem k h.1).2.1⟩

end OverfullWork.DirectedRobustExpansion
