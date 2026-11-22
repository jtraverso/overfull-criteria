module

public import OverfullWork.ClusterEqualization
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section


/-! Actual equal-size chunks of a finite cell. At most m-1 vertices
remain, with no existence assumption about the chunks themselves. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 18000000

theorem exists_uniform_chunks (A : Finset V) (m : ℕ) (hm : 0 < m) :
    ∃ C : Fin (A.card/m) → Finset V,
      (∀ i,C i ⊆ A) ∧ (∀ i,(C i).card=m) ∧
      (∀ i j,i ≠ j → Disjoint (C i) (C j)) ∧
      (A\univ.biUnion C).card < m := by
  let k := A.card/m
  obtain ⟨Y,hYA,hY⟩ := exists_subset_card_eq (Nat.mul_div_le A.card m)
  let e : (Fin k × Fin m) ≃ Y := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,hY,k]
    exact Nat.mul_comm _ _)
  let C : Fin k → Finset V := fun i => univ.image fun j : Fin m => (e (i,j)).val
  have hSub : ∀ i,C i ⊆ A := by
    intro i v hv
    obtain ⟨j,_,rfl⟩ := mem_image.mp hv
    exact hYA (e (i,j)).property
  have hCard : ∀ i,(C i).card=m := by
    intro i
    have hInj : Function.Injective (fun j : Fin m => (e (i,j)).val) := by
      intro j j' hh
      exact congrArg Prod.snd (e.injective (Subtype.ext hh))
    simp only [C,card_image_of_injective _ hInj,card_univ,Fintype.card_fin]
  have hDis : ∀ i j,i ≠ j → Disjoint (C i) (C j) := by
    intro i j hij
    apply disjoint_left.mpr
    intro v hi hj
    obtain ⟨a,_,ha⟩ := mem_image.mp hi
    obtain ⟨b,_,hb⟩ := mem_image.mp hj
    exact hij (congrArg Prod.fst (e.injective (Subtype.ext (ha.trans hb.symm))))
  have hUnion : univ.biUnion C=Y := by
    ext v
    constructor
    · intro hv
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
      obtain ⟨j,_,rfl⟩ := mem_image.mp hi
      exact (e (i,j)).property
    · intro hv
      obtain ⟨⟨i,j⟩,hh⟩ := e.surjective ⟨v,hv⟩
      refine mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨j,mem_univ _,?_⟩⟩
      exact congrArg Subtype.val hh
  refine ⟨C,hSub,hCard,hDis,?_⟩
  rw [hUnion,card_sdiff_of_subset hYA,hY]
  have hMod := Nat.mod_lt A.card hm
  have hDivide := Nat.mod_add_div A.card m
  omega

end OverfullWork.DirectedClusterQuotient
