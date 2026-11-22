module

public import OverfullWork.KuhnOsthusIntervalPathTransport
public import OverfullWork.KuhnOsthusExceptionalIntervalBalance
public import OverfullWork.KuhnOsthusWrappedPairCoordinates
public import OverfullWork.KuhnOsthusWindingIntervalGeometry

@[expose] public section


/-! Assemble the physical coordinates of one interval and one style
from the disjoint cells in the half-open interval and its terminal
cell in the next interval. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- The identified interval has the half-open interval as its
vertex set. Reopening it maps the quotient cells to their physical
cells and maps the extra copy of the boundary to the terminal
cell. Unions of quotient cells use the same physical coordinates. -/
theorem exists_physical_winding_interval_coordinates {I V : Type*} [Fintype I]
    (C : I → Finset V) (first : I) (T : Finset V)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hTerm : ∀ i, Disjoint (C i) T) (hSize : (C first).card = T.card) :
    let U := univ.biUnion C
    let A := U ∪ T
    let W := ↥(A \ T)
    ∃ cluster : W → I,
      let B := intervalCluster cluster first
      ∃ (coord : W ⊕ B ≃ A) (initial : B ≃ C first) (terminal : B ≃ T),
        (∀ b : B, (coord (Sum.inl b.val)).val = (initial b).val) ∧
        (∀ b : B, (coord (Sum.inr b)).val = (terminal b).val) ∧
        (∀ x : W, (coord (Sum.inl x)).val = x.val) ∧
        ∀ J : Finset I,
          ((univ : Finset W).filter (fun x => cluster x ∈ J)).map
            (Function.Embedding.inl.trans (coord.toEmbedding.trans (Function.Embedding.subtype _))) =
            J.biUnion C := by
  classical
  dsimp only
  let U := univ.biUnion C
  let A := U ∪ T
  let W := ↥(A \ T)
  have hU (i : I) : C i ⊆ U := fun _ hx => mem_biUnion.mpr ⟨i,mem_univ _,hx⟩
  have hS : C first ⊆ A := fun x hx => mem_union_left _ (hU first hx)
  have hT : T ⊆ A := fun _ hx => mem_union_right _ hx
  have hOwn (x : W) : ∃ i, x.val ∈ C i := by
    obtain ⟨hA,hT⟩ := mem_sdiff.mp x.prop
    have hu : x.val ∈ U := (mem_union.mp hA).resolve_right hT
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hu
    exact ⟨i,hi⟩
  let cluster (x : W) := (hOwn x).choose
  have hLabel (x : W) (i : I) : cluster x = i ↔ x.val ∈ C i := by
    have hx : x.val ∈ C (cluster x) := (hOwn x).choose_spec
    constructor
    · intro h
      exact h ▸ hx
    · intro hi
      by_contra h
      exact disjoint_left.mp (hDis _ _ h) hx hi
  let B := intervalCluster cluster first
  let B₀ := (univ : Finset W).filter (fun x => x.val ∈ C first)
  let eB : B ≃ B₀ := {
    toFun := fun b => ⟨b.val,mem_filter.mpr ⟨mem_univ _,(hLabel b.val first).mp
      ((mem_intervalCluster cluster first b.val).mp b.prop)⟩⟩
    invFun := fun b => ⟨b.val,(mem_intervalCluster cluster first b.val).mpr
      ((hLabel b.val first).mpr (mem_filter.mp b.prop).2)⟩
    left_inv := fun b => Subtype.ext rfl
    right_inv := fun b => Subtype.ext rfl }
  obtain ⟨e,init,term,heInit,heTerm,heOrd⟩ :=
    exists_interval_split_coordinates A (C first) T hS hT (hTerm first) hSize
  let coord : W ⊕ B ≃ A := (Equiv.sumCongr (Equiv.refl W) eB).trans e
  have hCoord (x : W) : (coord (Sum.inl x)).val = x.val := heOrd x
  refine ⟨cluster,coord,eB.trans init,eB.trans term,fun b => heInit (eB b),
    fun b => heTerm (eB b),hCoord,?_⟩
  intro J
  ext v
  simp only [mem_map,mem_filter,mem_univ,true_and,mem_biUnion,Function.Embedding.trans_apply]
  constructor
  · rintro ⟨x,hx,he⟩
    change (coord (Sum.inl x)).val = v at he
    rw [hCoord] at he
    exact ⟨cluster x,hx,he ▸ (hLabel x (cluster x)).mp rfl⟩
  · rintro ⟨i,hi,hv⟩
    let x : W := ⟨v,mem_sdiff.mpr ⟨mem_union_left _ (hU i hv),
      fun h => disjoint_left.mp (hTerm i) hv h⟩⟩
    refine ⟨x,?_,hCoord x⟩
    have hxi : cluster x = i := (hLabel x i).mpr hv
    exact hxi.symm ▸ hi

/-- The half-open intervals with their styles partition the ordinary
cells. Their initial cells lie in their own intervals, and the
terminal cell of each interval is the next initial cell. -/
theorem winding_styled_interval_partition {J V : Type*} {p q : ℕ}
    (C : J × Fin (p*q) → Finset V) (hp : 2 ≤ p) (hq : 0 < q) (m : ℕ)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hSize : ∀ i, (C i).card = m) :
    let next : Equiv.Perm (J × Fin p) := Equiv.prodCongr (Equiv.refl J) (finRotate p)
    let U (i : J × Fin p) := (univ : Finset (Fin q)).biUnion (fun j => C (i.1,intervalPosition i.2 j))
    let S (i : J × Fin p) := C (i.1,intervalPosition i.2 ⟨0,hq⟩)
    (∀ i, (next i).1 = i.1 ∧ next i ≠ i ∧ S i ⊆ U i ∧ (U i).card = q*m) ∧
    (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
    (∀ v, (∃ i, v ∈ U i) ↔ ∃ j, v ∈ C j) := by
  classical
  dsimp only
  let next : Equiv.Perm (J × Fin p) := Equiv.prodCongr (Equiv.refl J) (finRotate p)
  let f (i : J × Fin p) (j : Fin q) := (i.1,intervalPosition i.2 j)
  let U (i : J × Fin p) := (univ : Finset (Fin q)).biUnion (fun j => C (f i j))
  let S (i : J × Fin p) := C (f i ⟨0,hq⟩)
  have hId (i i' : J × Fin p) (x y : Fin q) (h : f i x = f i' y) : i = i' := by
    have he : (i.2,x) = (i'.2,y) :=
      finProdFinEquiv.injective (congrArg Prod.snd h)
    exact Prod.ext (congrArg (fun t : J × Fin (p*q) => t.1) h) (congrArg Prod.fst he)
  refine ⟨?_,?_,?_⟩
  · intro i
    have hMove : next i ≠ i := fun h => finRotate_interval_ne_self hp i.2 (congrArg Prod.snd h)
    have hSub : S i ⊆ U i := fun _ h => mem_biUnion.mpr ⟨⟨0,hq⟩,mem_univ _,h⟩
    have hCard : (U i).card = q*m := by
      unfold U
      rw [card_biUnion (fun j _ k _ h => hDis _ _
        (fun he => h ((intervalPosition i.2).injective (congrArg Prod.snd he))))]
      simp [hSize]
    exact ⟨rfl,hMove,hSub,hCard⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro v hi hj
    obtain ⟨x,_,hx⟩ := mem_biUnion.mp (show v ∈ U i from hi)
    obtain ⟨y,_,hy⟩ := mem_biUnion.mp (show v ∈ U j from hj)
    exact disjoint_left.mp (hDis _ _ (fun h => hij (hId i j x y h))) hx hy
  · intro v
    constructor
    · rintro ⟨i,hi⟩
      obtain ⟨x,_,hx⟩ := mem_biUnion.mp (show v ∈ U i from hi)
      exact ⟨f i x,hx⟩
    · rintro ⟨⟨a,t⟩,ht⟩
      obtain ⟨⟨i,x⟩,rfl⟩ := finProdFinEquiv.surjective t
      exact ⟨(a,i),mem_biUnion.mpr ⟨x,mem_univ _,ht⟩⟩

end OverfullWork.DirectedRobustExpansion
