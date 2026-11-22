module

public import OverfullWork.KuhnOsthusWalkBatchPartition

@[expose] public section


/-! Concatenate the matching orders in the four quarters of a
physical pair. A permutation of the quarters implements the
changed ordering at the last pair in Lemma 9.5. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*}

/-- Order the whole physical pair. As long as each quarter has the
same size, any list of the four quarters has the required
short-window matching property. -/
theorem exists_ordered_physical_walk_pair (A B : Fin 4 → Finset V) {k m : ℕ}
    (M : ∀ j, Fin k → A j ≃ B j) (rotation : Equiv.Perm (Fin 4)) (w : ℕ)
    (hRoom : 3*w ≤ m) (hA : ∀ j, (A j).card = m)
    (hDisA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hDisB : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    let E := Σ j : Fin 4, Fin k × A j
    let src (e : E) := e.2.2.val
    let dst (e : E) := (M e.1 e.2.1 e.2.2).val
    ∃ order : Fin (4*(k*m)) ≃ E,
      (∀ p, (order p).1 = rotation ((finProdFinEquiv.symm p).1)) ∧
      ∀ p q, p.val < q.val → q.val < p.val+w →
        src (order p) ≠ src (order q) ∧ dst (order p) ≠ dst (order q) := by
  intro E src dst
  choose C hC using fun j => exists_walk_quarter_ordering m w
    ((Fintype.card_coe (A j)).trans (hA j)) hRoom (M j)
  let F : Fin (4*(k*m)) ≃ Fin 4 × Fin (k*m) := finProdFinEquiv.symm
  let L : Fin 4 × Fin (k*m) ≃ E :=
    (Equiv.sigmaEquivProd _ _).symm.trans (Equiv.sigmaCongr rotation (fun j => C (rotation j)))
  let order := F.trans L
  refine ⟨order,fun _ => rfl,?_⟩
  intro p q hpq hq
  let i := (F p).1
  let j := (F q).1
  let a := (F p).2
  let b := (F q).2
  change (C (rotation i) a).2.val ≠ (C (rotation j) b).2.val ∧
    (M (rotation i) (C (rotation i) a).1 (C (rotation i) a).2).val ≠
      (M (rotation j) (C (rotation j) b).1 (C (rotation j) b).2).val
  by_cases he : i = j
  · have hp' : p.val = a.val+(k*m)*i.val :=
      congrArg Fin.val (finProdFinEquiv.apply_symm_apply p).symm
    have hq' : q.val = b.val+(k*m)*j.val :=
      congrArg Fin.val (finProdFinEquiv.apply_symm_apply q).symm
    rw [←he] at hq' ⊢
    have hSep := hC (rotation i) a b (by omega) (by omega)
    exact ⟨fun h => hSep.1 (Subtype.ext h),fun h => hSep.2 (Subtype.ext h)⟩
  · have hne : rotation i ≠ rotation j := fun h => he (rotation.injective h)
    have hsa := (C (rotation i) a).2.prop
    have hsb := (C (rotation j) b).2.prop
    have hta := (M (rotation i) (C (rotation i) a).1 (C (rotation i) a).2).prop
    have htb := (M (rotation j) (C (rotation j) b).1 (C (rotation j) b).2).prop
    exact ⟨fun h => disjoint_left.mp (hDisA _ _ hne) (h ▸ hsa) hsb,
      fun h => disjoint_left.mp (hDisB _ _ hne) (h ▸ hta) htb⟩

end OverfullWork.DirectedRobustExpansion
