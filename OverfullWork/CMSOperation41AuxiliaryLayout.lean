module

public import OverfullWork.CMSOperation41CyclicLayouts
public import OverfullWork.OrderedCanonicalTransport

@[expose] public section


/-! The prescribed auxiliary edges in Operations 4.1 and the two
connector vertices have their actual positions in the cyclic layout. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset SimpleGraph OrderedCanonicalTransport
open scoped Classical

variable {V : Type*}

private def auxiliaryPosition {f : ℕ} (i : Fin f) : Fin (2*f+2) :=
  ⟨2*i.val+1,by omega⟩

private def orderValue {f : ℕ} (e : (Fin f × Bool) ↪ V) (x y : V) (i : Fin (2*f+2)) : V :=
  if h₀ : i.val = 0 then x
  else if h₁ : i.val = 2*f+1 then y
  else e ((pairedIndex f).symm ⟨i.val-1,by omega⟩)

private theorem orderValue_injective {f : ℕ} (e : (Fin f × Bool) ↪ V) (x y : V)
    (hxy : x ≠ y) (hx : x ∉ Set.range e) (hy : y ∉ Set.range e) :
    Function.Injective (orderValue e x y) := by
  intro i j he
  apply Fin.ext
  by_cases hi : i.val = 0
  · by_cases hj : j.val = 0
    · omega
    · by_cases hJ : j.val = 2*f+1
      · exact (hxy (by simpa only [orderValue,dif_pos hi,dif_neg hj,dif_pos hJ] using he)).elim
      · simp only [orderValue,dif_pos hi,dif_neg hj,dif_neg hJ] at he
        exact (hx ⟨_,he.symm⟩).elim
  · by_cases hi' : i.val = 2*f+1
    · by_cases hj : j.val = 0
      · exact (hxy (by simpa only [orderValue,dif_neg hi,dif_pos hi',dif_pos hj] using he.symm)).elim
      · by_cases hJ : j.val = 2*f+1
        · omega
        · simp only [orderValue,dif_neg hi,dif_pos hi',dif_neg hj,dif_neg hJ] at he
          exact (hy ⟨_,he.symm⟩).elim
    · by_cases hj : j.val = 0
      · simp only [orderValue,dif_neg hi,dif_neg hi',dif_pos hj] at he
        exact (hx ⟨_,he⟩).elim
      · by_cases hJ : j.val = 2*f+1
        · simp only [orderValue,dif_neg hi,dif_neg hi',dif_neg hj,dif_pos hJ] at he
          exact (hy ⟨_,he⟩).elim
        · simp only [orderValue,dif_neg hi,dif_neg hi',dif_neg hj,dif_neg hJ] at he
          have hh := congrArg Fin.val ((pairedIndex f).symm.injective (e.injective he))
          change i.val-1 = j.val-1 at hh
          omega

theorem exists_cyclic_layout_of_auxiliary_edges {f : ℕ} (e : (Fin f × Bool) ↪ V)
    (x y : V) (hxy : x ≠ y) (hx : x ∉ Set.range e) (hy : y ∉ Set.range e)
    (isolated : Finset V) (hxi : x ∉ isolated) (hyi : y ∉ isolated)
    (hIso : ∀ i, e i ∉ isolated) :
    ∃ (w : Fin (2*f+2) ↪ V) (F : Finset (Fin (2*f+2))) (mark : Fin f ↪ Fin (2*f+2)),
      w 0 = x ∧ w (Fin.last (2*f+1)) = y ∧
      (∀ i, w i ∉ isolated) ∧ F = univ.image mark ∧ F.card = f ∧
      Fin.last (2*f+1) ∉ F ∧
      (∀ i, w (mark i) = e (i,false) ∧ w (finRotate (2*f+2) (mark i)) = e (i,true)) ∧
      (∀ j, w j = x ∨ w j = y ∨ w j ∈ Set.range e) := by
  let w : Fin (2*f+2) ↪ V := ⟨orderValue e x y,orderValue_injective e x y hxy hx hy⟩
  let mark : Fin f ↪ Fin (2*f+2) := ⟨auxiliaryPosition,by
    intro i j he
    apply Fin.ext
    have hh := congrArg Fin.val he
    change 2*i.val+1 = 2*j.val+1 at hh
    omega⟩
  let F : Finset (Fin (2*f+2)) := univ.image mark
  refine ⟨w,F,mark,?_,?_,?_,rfl,?_,?_,?_,?_⟩
  · simp [w,orderValue]
  · simp [w,orderValue]
  · intro i
    by_cases h₀ : i.val = 0
    · simpa only [w,Function.Embedding.coeFn_mk,orderValue,dif_pos h₀] using hxi
    · by_cases h₁ : i.val = 2*f+1
      · simpa only [w,Function.Embedding.coeFn_mk,orderValue,dif_neg h₀,dif_pos h₁] using hyi
      · simp only [w,Function.Embedding.coeFn_mk,orderValue,dif_neg h₀,dif_neg h₁]
        exact hIso _
  · change (univ.image mark).card = f
    rw [card_image_of_injective _ mark.injective,card_univ,Fintype.card_fin]
  · intro h
    obtain ⟨i,_,hi⟩ := mem_image.mp h
    have hh := congrArg Fin.val hi
    change 2*i.val+1 = 2*f+1 at hh
    omega
  · intro i
    have hMap (j : Fin (2*f+2)) (h₀ : j.val ≠ 0) (h₁ : j.val ≠ 2*f+1) :
        w j = e ((pairedIndex f).symm ⟨j.val-1,by omega⟩) := by
      simp only [w,Function.Embedding.coeFn_mk,orderValue,dif_neg h₀,dif_neg h₁]
    have hMark : (mark i).val = 2*i.val+1 := rfl
    have hLt : (mark i).val < 2*f+1 := by omega
    have hNext : (finRotate (2*f+2) (mark i)).val = 2*i.val+2 := by
      have hh := congrArg Fin.val (finRotate_of_lt hLt)
      change (finRotate (2*f+2) (mark i)).val = (mark i).val+1 at hh
      omega
    constructor
    · rw [hMap _ (by omega) (by omega)]
      congr 1
      apply (pairedIndex f).injective
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      rw [pairedIndex_false_val]
      change (mark i).val-1 = 2*i.val
      omega
    · rw [hMap _ (by omega) (by omega)]
      congr 1
      apply (pairedIndex f).injective
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      rw [pairedIndex_true_val]
      change (finRotate (2*f+2) (mark i)).val-1 = 2*i.val+1
      omega
  · intro j
    by_cases h₀ : j.val = 0
    · simp only [w,Function.Embedding.coeFn_mk,orderValue,dif_pos h₀,true_or]
    · by_cases h₁ : j.val = 2*f+1
      · simp only [w,Function.Embedding.coeFn_mk,orderValue,dif_neg h₀,dif_pos h₁,true_or,or_true]
      · right
        right
        rw [show w j = orderValue e x y j from rfl]
        simp only [orderValue,dif_neg h₀,dif_neg h₁]
        exact ⟨_,rfl⟩

end OverfullWork.DirectedSpanningConfiguration
