module

public import OverfullWork.KuhnOsthusResidueMatchings
public import OverfullWork.KuhnOsthusTypeOrdering
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Defs

@[expose] public section


/-! The cyclic separation of double-types in Kühn–Osthus Lemma 8.7.
The ordering is obtained by packing the cyclic proximity relation
against the conflict relation on pairs of coarse intervals. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical Fin.CommRing

/-- Distinct positions within (h) steps of one another in either
direction of the cyclic ordering. -/
def residueCyclicClose {n : ℕ} (h : ℕ) (i j : Fin n) : Prop :=
  i ≠ j ∧ ∃ d : Fin h,
    (i.val + (d.val + 1)) % n = j.val ∨ (j.val + (d.val + 1)) % n = i.val

theorem residueCyclicClose_symm {n h : ℕ} {i j : Fin n}
    (he : residueCyclicClose h i j) : residueCyclicClose h j i := by
  obtain ⟨hne,d,hd⟩ := he
  exact ⟨hne.symm,d,hd.symm⟩

private theorem residueCyclicClose_iff {n h : ℕ} [NeZero n] (i j : Fin n) :
    residueCyclicClose h i j ↔ i ≠ j ∧ ∃ d : Fin h,
      i + ((d.val + 1 : ℕ) : Fin n) = j ∨ j + ((d.val + 1 : ℕ) : Fin n) = i := by
  simp only [residueCyclicClose, Fin.ext_iff, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]

theorem card_residue_cyclic_neighborhood {n : ℕ} [NeZero n] (h : ℕ) (i : Fin n) :
    ((univ : Finset (Fin n)).filter (residueCyclicClose h i)).card ≤ 2*h := by
  let advance (d : Fin h) := i + ((d.val + 1 : ℕ) : Fin n)
  let retreat (d : Fin h) := i - ((d.val + 1 : ℕ) : Fin n)
  let P := univ.image advance
  let Q := univ.image retreat
  have hSub : univ.filter (residueCyclicClose h i) ⊆ P ∪ Q := by
    intro j hj
    obtain ⟨_,d,hd | hd⟩ := (residueCyclicClose_iff i j).mp (mem_filter.mp hj).2
    · exact mem_union_left _ (mem_image.mpr ⟨d,mem_univ _,hd⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨d,mem_univ _,(eq_sub_of_add_eq hd).symm⟩)
  have hP : P.card ≤ h := by
    simpa [P] using card_image_le (s := (univ : Finset (Fin h))) (f := advance)
  have hQ : Q.card ≤ h := by
    simpa [Q] using card_image_le (s := (univ : Finset (Fin h))) (f := retreat)
  exact (card_le_card hSub).trans ((card_union_le _ _).trans (by omega))

noncomputable def residueIntervalClosure {g : ℕ} [NeZero g] (r : ℤ)
    (T : ResidueDoubleType g) : Finset (Fin g) :=
  T.val.biUnion (fun x => (Icc (-r) r).image (fun d : ℤ => x + (d : Fin g)))

/-- A double-type together with the predecessors and successors of
its two intervals. -/
noncomputable def residueTypeClosure {g : ℕ} [NeZero g] (T : ResidueDoubleType g) :
    Finset (Fin g) := residueIntervalClosure 1 T

theorem subset_residue_type_closure {g : ℕ} [NeZero g] (T : ResidueDoubleType g) :
    T.val ⊆ residueTypeClosure T := by
  intro x hx
  exact mem_biUnion.mpr ⟨x,hx,mem_image.mpr ⟨0,by simp,by simp⟩⟩

private theorem card_residue_radius_two {g : ℕ} [NeZero g] (T : ResidueDoubleType g) :
    (residueIntervalClosure 2 T).card ≤ 10 := by
  have hT := (mem_powersetCard.mp T.prop).2
  apply card_biUnion_le.trans
  calc
    (∑ x ∈ T.val, ((Icc (-2 : ℤ) 2).image (fun d : ℤ => x + (d : Fin g))).card) ≤
        ∑ _x ∈ T.val, 5 := by
      apply sum_le_sum
      intro x _
      exact card_image_le.trans (by norm_num [Int.card_Icc])
    _ = 10 := by simp [hT]

theorem card_double_types_through {g : ℕ} (a : Fin g) :
    ((univ : Finset (ResidueDoubleType g)).filter (fun T => a ∈ T.val)).card ≤ g := by
  let P := (univ : Finset (Fin g)).image (fun b => ({a,b} : Finset (Fin g)))
  have hCard : ((univ : Finset (ResidueDoubleType g)).filter (fun T => a ∈ T.val)).card
      ≤ P.card := by
    apply card_le_card_of_injOn Subtype.val _ Subtype.val_injective.injOn
    intro T hT
    have ha := (mem_filter.mp hT).2
    have hTwo := (mem_powersetCard.mp T.prop).2
    have hErase : (T.val.erase a).card = 1 := by rw [card_erase_of_mem ha,hTwo]
    obtain ⟨b,hb⟩ := card_eq_one.mp hErase
    have hInsert := insert_erase ha
    rw [hb] at hInsert
    exact mem_image.mpr ⟨b,mem_univ _,hInsert⟩
  exact hCard.trans (card_image_le.trans (by simp))

private theorem exists_mem_radius_two_of_overlap {g : ℕ} [NeZero g]
    {T U : ResidueDoubleType g} (h : ¬ Disjoint (residueTypeClosure T) (residueTypeClosure U)) :
    ∃ y ∈ U.val, y ∈ residueIntervalClosure 2 T := by
  obtain ⟨z,hzT,hzU⟩ := not_disjoint_iff.mp h
  obtain ⟨x,hx,zx⟩ := mem_biUnion.mp hzT
  obtain ⟨y,hy,zy⟩ := mem_biUnion.mp hzU
  obtain ⟨a,ha,heA⟩ := mem_image.mp zx
  obtain ⟨b,hb,heB⟩ := mem_image.mp zy
  refine ⟨y,hy,mem_biUnion.mpr ⟨x,hx,mem_image.mpr ⟨a-b,?_,?_⟩⟩⟩
  · rw [mem_Icc] at ha hb ⊢
    omega
  · rw [Int.cast_sub,← add_sub_assoc,heA,← heB,add_sub_cancel_right]

theorem card_residue_type_conflicts {g : ℕ} [NeZero g] (T : ResidueDoubleType g) :
    (@Finset.filter (ResidueDoubleType g)
      (fun U => ¬ Disjoint (residueTypeClosure T) (residueTypeClosure U)) (Classical.decPred _) univ).card
        ≤ 10*g := by
  let through (a : Fin g) := (univ : Finset (ResidueDoubleType g)).filter (fun U => a ∈ U.val)
  let K := residueIntervalClosure 2 T
  refine (card_le_card (t := K.biUnion through) ?_).trans ?_
  · intro U hU
    have hOverlap := (@mem_filter _ _ (Classical.decPred _) _ _).mp hU
    obtain ⟨y,hyU,hyK⟩ := exists_mem_radius_two_of_overlap hOverlap.2
    exact mem_biUnion.mpr ⟨y,hyK,mem_filter.mpr ⟨mem_univ _,hyU⟩⟩
  · exact card_biUnion_le.trans
      (calc
        (∑ a ∈ K,(through a).card) ≤ ∑ _a ∈ K,g :=
          sum_le_sum (fun a _ => card_double_types_through a)
        _ = K.card*g := by simp
        _ ≤ 10*g := Nat.mul_le_mul_right _ (card_residue_radius_two T))

/-- A cyclic ordering in which close double-types have disjoint
closures. The explicit numerical hypothesis leaves room for the
correcting swap in the auxiliary graph. -/
theorem exists_residue_double_type_ordering (g h : ℕ) [NeZero g]
    (hBig : 2*(2*h)*(10*g)+2*h+1 < g.choose 2) :
    ∃ order : Fin (g.choose 2) ≃ ResidueDoubleType g, ∀ i j,
      residueCyclicClose h i j → Disjoint (residueTypeClosure (order i)) (residueTypeClosure (order j)) := by
  let : NeZero (g.choose 2) := ⟨by omega⟩
  let e₀ := (Fintype.equivFinOfCardEq (card_residue_double_type g)).symm
  obtain ⟨order,hOrder⟩ := exists_disjoint_ordering_of_sparse_relations
    (residueCyclicClose h) (fun T U => ¬ Disjoint (residueTypeClosure T) (residueTypeClosure U))
    residueCyclicClose_symm (fun hDisj h' => hDisj h'.symm) (fun _ h' => h'.1 rfl)
    e₀ (2*h) (10*g) (card_residue_cyclic_neighborhood h) (fun T => card_residue_type_conflicts (g := g) T)
    (by simpa using hBig)
  exact ⟨order,fun i j h' => not_not.mp (hOrder i j h')⟩

/-- Reduction of a cyclic index modulo the length of a round. -/
def residueRoundIndex {N n : ℕ} [NeZero n] (i : Fin N) : Fin n :=
  ⟨i.val % n,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/-- Repeating a cyclic ordering preserves its separation across round
boundaries, including the boundary of the full cyclic ordering. -/
theorem residueCyclicClose_roundIndex {N n h : ℕ} [NeZero n]
    (hDiv : n ∣ N) (hLen : h < n) {i j : Fin N} (hClose : residueCyclicClose h i j) :
    residueCyclicClose h (residueRoundIndex i : Fin n) (residueRoundIndex j) := by
  have step (u v : Fin N) (d : Fin h) (he : (u.val + (d.val + 1)) % N = v.val) :
      residueCyclicClose h (residueRoundIndex u : Fin n) (residueRoundIndex v) := by
    let a : Fin n := residueRoundIndex u
    let b : Fin n := residueRoundIndex v
    have hab : (a.val + (d.val + 1)) % n = b.val := by
      change (u.val % n + (d.val + 1)) % n = v.val % n
      rw [← he,Nat.mod_mod_of_dvd _ hDiv,Nat.mod_add_mod]
    have hAdd : a + ((d.val + 1 : ℕ) : Fin n) = b := by
      apply Fin.ext
      simpa only [Fin.val_add,Fin.val_natCast,Nat.add_mod_mod] using hab
    have hne : a ≠ b := by
      intro h
      have hZero : ((d.val + 1 : ℕ) : Fin n) = 0 :=
        add_left_cancel (hAdd.trans (h.symm.trans (add_zero a).symm))
      have hVal := congrArg Fin.val hZero
      rw [Fin.val_natCast,Fin.val_zero,Nat.mod_eq_of_lt (by have := d.isLt; omega)] at hVal
      omega
    exact ⟨hne,d,Or.inl hab⟩
  obtain ⟨_,d,hd | hd⟩ := hClose
  · exact step i j d hd
  · exact residueCyclicClose_symm (step j i d hd)

end OverfullWork.DirectedRobustExpansion
