module

public import OverfullWork.OsthusStadenRedClusters
public import Mathlib.Data.Fintype.Fin

@[expose] public section


/-! Opposite orientations for the layers in each red phase of §5.4. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- A phase keeps the original factor index and the first unwind.
Negating the last nonzero shift pairs its two orientation classes. -/
def reverseLayerOrientation {r s p : ℕ} : Equiv.Perm (RefinedFactorIndex r s p) where
  toFun j := (j.1,j.2.1,⟨-j.2.2.val,neg_ne_zero.mpr j.2.2.property⟩)
  invFun j := (j.1,j.2.1,⟨-j.2.2.val,neg_ne_zero.mpr j.2.2.property⟩)
  left_inv := by rintro ⟨t,a,⟨b,hb⟩⟩; simp
  right_inv := by rintro ⟨t,a,⟨b,hb⟩⟩; simp

def usesFirstRedHalf {r s p : ℕ} (j : RefinedFactorIndex r s p) : Bool :=
  decide (j.2.2.val.val ≤ p/2)

theorem usesFirstRedHalf_reverse {r s p : ℕ} [NeZero p] (hp : Odd p)
    (j : RefinedFactorIndex r s p) :
    usesFirstRedHalf (reverseLayerOrientation j) = !(usesFirstRedHalf j) := by
  let b := j.2.2.val
  letI : NeZero b := ⟨j.2.2.property⟩
  have hb : (-b).val = p-b.val := ZMod.val_neg_of_ne_zero b
  have hpos : 0 < b.val := ZMod.val_pos.mpr j.2.2.property
  have hlt : b.val < p := ZMod.val_lt _
  obtain ⟨k,hk⟩ := hp
  change decide ((-b).val ≤ p/2) = !(decide (b.val ≤ p/2))
  rw [hb]
  by_cases h : b.val ≤ p/2
  · have h' : ¬ p-b.val ≤ p/2 := by omega
    simp only [decide_eq_false h',decide_eq_true h,Bool.not_true]
  · have h' : p-b.val ≤ p/2 := by omega
    simp only [decide_eq_true h',decide_eq_false h,Bool.not_false]

/-- Each red phase has equally many layers of the two orientations.
This uses the actual layer index and requires no divisibility of the
number of primary factors by the number of phases. -/
theorem red_phase_orientation_counts {r s p : ℕ} [NeZero s] [NeZero p]
    (hp : Odd p) (q : ZMod p × Bool) :
    ((univ : Finset (RefinedFactorIndex r s p)).filter
      (fun j => redPhase p j.1.val = q ∧ usesFirstRedHalf j = true)).card =
    (univ.filter (fun j : RefinedFactorIndex r s p =>
      redPhase p j.1.val = q ∧ usesFirstRedHalf j = false)).card := by
  let flip : Equiv.Perm (RefinedFactorIndex r s p) := reverseLayerOrientation
  have hRev (j : RefinedFactorIndex r s p) : usesFirstRedHalf (flip j) = !usesFirstRedHalf j :=
    usesFirstRedHalf_reverse hp j
  have hInv (j : RefinedFactorIndex r s p) : flip.symm j = flip j := rfl
  apply card_bij (fun j _ => flip j)
  · intro j hj
    obtain ⟨hq,hj'⟩ := (mem_filter.mp hj).2
    refine mem_filter.mpr ⟨mem_univ _,hq,?_⟩
    rw [hRev,hj',Bool.not_true]
  · intro j _ j' _ he
    exact flip.injective he
  · intro j hj
    obtain ⟨hq,hj'⟩ := (mem_filter.mp hj).2
    refine ⟨flip.symm j,mem_filter.mpr ⟨mem_univ _,hq,?_⟩,flip.apply_symm_apply j⟩
    rw [hInv,hRev,hj',Bool.not_false]

/-- Equation (21) on the actual labels of the two intermediate halves. -/
theorem exists_directional_red_labels (s : ℕ) (clean : Fin (2*s)) :
    ∃ first second : Finset (Fin (2*s)),
      first.card = s-1 ∧ second.card = s-1 ∧ Disjoint first second ∧
      (∀ i ∈ first, i.val < s ∧ i ≠ clean) ∧
      ∀ i ∈ second, s ≤ i.val ∧ i ≠ clean := by
  let lower := (univ : Finset (Fin (2*s))).filter (fun i => i.val < s)
  let upper := lowerᶜ
  have hLower : lower.card = s := by
    rw [Fin.card_filter_val_lt]
    exact min_eq_right (by omega)
  have hUpper : upper.card = s := by
    change lowerᶜ.card = s
    rw [card_compl,Fintype.card_fin,hLower]
    omega
  have hDis : Disjoint lower upper :=
    disjoint_left.mpr fun _ h₁ h₂ => (mem_compl.mp h₂) h₁
  obtain ⟨A,B,hA,hB,hACard,hBCard,hAB⟩ := exists_directional_red_cells lower upper clean s hLower hUpper hDis
  refine ⟨A,B,hACard,hBCard,hAB,?_,?_⟩
  · intro i hi
    have h := mem_erase.mp (hA hi)
    exact ⟨(mem_filter.mp h.2).2,h.1⟩
  · intro i hi
    have h := mem_erase.mp (hB hi)
    have he : i ∉ lower := mem_compl.mp h.2
    exact ⟨by
      by_contra! hn
      exact he (mem_filter.mpr ⟨mem_univ _,hn⟩),h.1⟩

end OverfullWork.DirectedRobustExpansion
