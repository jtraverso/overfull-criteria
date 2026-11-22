module

public import OverfullWork.KuhnOsthusUniversalWalkOrdering
public import OverfullWork.KuhnOsthusChordLoadBalance

@[expose] public section


/-! The local degree calculation in Kühn–Osthus Lemma 9.5.
Every elementary sequence gives one unit of imbalance at either
end. Adding ordinary successor arcs to a sequence leaves that
identity unchanged. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {I E J : Type*} [Fintype I] [Fintype E] [Fintype J]

/-- Extend the block labels of the elementary chord occurrences
to all the edges of the universal walk. The other edges project
to base successor arcs and can carry any block label for this count. -/
theorem exists_augmented_chord_block_labels (s : Equiv.Perm I) (l : I → List I)
    (anchor : I) {L : ℕ} (F : Fin L → Equiv.Perm I)
    (hEnd : ∀ j, (j :: l j).getLast? = some (s j))
    (hMult : ∀ x y, ((univ : Finset (Fin L)).filter (fun j => F j x = y)).card =
      elementaryChordMultiplicity s l x y +
        if s x = y then L - (∑ z, elementaryChordMultiplicity s l x z) else 0) :
    ∃ owner : Fin L × I → I, ∀ j x,
      (∑ e : Fin L × I, if owner e = j ∧ e.2 = x then (1:ℕ) else 0) +
        (if j = x then 1 else 0) =
      (∑ e : Fin L × I, if owner e = j ∧ F e.1 e.2 = s x then (1:ℕ) else 0) +
        (if j = s x then 1 else 0) := by
  let P := Σ j, Fin (l j).length
  let W := Fin L × I
  let src (p : P) := s.symm ((p.1 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt))
  let dst (p : P) := (l p.1)[p.2.val]
  obtain ⟨emb,hEmb,hRest⟩ := exists_universal_chord_occurrence_embedding s l F hMult
  let owner (e : W) := if h : ∃ p, emb p = e then h.choose.1 else anchor
  have hOwner (p : P) : owner (emb p) = p.1 := by
    have hp : ∃ p', emb p' = emb p := ⟨p,rfl⟩
    dsimp only [owner]
    rw [dif_pos hp]
    exact congrArg Sigma.fst (emb.injective hp.choose_spec)
  let A := (univ : Finset P).map emb
  have hOther (e : W) (he : e ∈ Aᶜ) : F e.1 e.2 = s e.2 := by
    by_contra hn
    obtain ⟨p,hp⟩ := hRest e.1 e.2 hn
    exact (mem_compl.mp he) (mem_map.mpr ⟨p,mem_univ _,hp⟩)
  have hLeft (j x : I) :
      (∑ e ∈ A, if owner e = j ∧ e.2 = x then (1:ℕ) else 0) = (chordSources s j (l j)).count x := by
    dsimp only [A]
    rw [sum_map,Fintype.sum_sigma]
    simp only [hOwner,fun p => (hEmb p).1]
    have he (i : I) :
        (∑ p : Fin (l i).length, if i = j ∧ src ⟨i,p⟩ = x then (1:ℕ) else 0) =
          if i = j then ∑ p : Fin (l i).length, if src ⟨i,p⟩ = x then (1:ℕ) else 0 else 0 := by
      by_cases h : i = j <;> simp [h]
    change (∑ i, ∑ p : Fin (l i).length, if i = j ∧ src ⟨i,p⟩ = x then (1:ℕ) else 0) = _
    simp only [he,sum_ite_eq',mem_univ,if_true]
    rw [←sum_positions_eq_count]
    apply Fintype.sum_equiv (finCongr (chordSources_length s j (l j)).symm)
    intro p
    simp only [src,chordSources,List.getElem_map,List.getElem_dropLast]
    rfl
  have hRight (j x : I) :
      (∑ e ∈ A, if owner e = j ∧ F e.1 e.2 = s x then (1:ℕ) else 0) = (l j).count (s x) := by
    dsimp only [A]
    rw [sum_map,Fintype.sum_sigma]
    simp only [hOwner,fun p => (hEmb p).2]
    have he (i : I) :
        (∑ p : Fin (l i).length, if i = j ∧ dst ⟨i,p⟩ = s x then (1:ℕ) else 0) =
          if i = j then ∑ p : Fin (l i).length, if dst ⟨i,p⟩ = s x then (1:ℕ) else 0 else 0 := by
      by_cases h : i = j <;> simp [h]
    change (∑ i, ∑ p : Fin (l i).length, if i = j ∧ dst ⟨i,p⟩ = s x then (1:ℕ) else 0) = _
    simp only [he,sum_ite_eq',mem_univ,if_true]
    exact sum_positions_eq_count (l j) (s x)
  refine ⟨owner,?_⟩
  intro j x
  have hComp :
      (∑ e ∈ Aᶜ, if owner e = j ∧ e.2 = x then (1:ℕ) else 0) =
      (∑ e ∈ Aᶜ, if owner e = j ∧ F e.1 e.2 = s x then (1:ℕ) else 0) := by
    apply sum_congr rfl
    intro e he
    rw [hOther e he,s.injective.eq_iff]
  have hSumL := sum_add_sum_compl A (fun e => if owner e = j ∧ e.2 = x then (1:ℕ) else 0)
  have hSumR := sum_add_sum_compl A (fun e => if owner e = j ∧ F e.1 e.2 = s x then (1:ℕ) else 0)
  rw [hLeft,hComp] at hSumL
  rw [hRight] at hSumR
  have hBalance := elementary_count_balance s j x (l j) (hEnd j)
  omega

/-- Passing through the blocks from the target of a prescribed arc
to the successor of its source gives a locally balanced total.
A uniform padding of the whole walk is included in the identity. -/
theorem locally_balanced_augmented_chord_loads (s : Equiv.Perm I)
    (owner src dst : E → I) (a b : J → I) (len : J → ℕ) (pad : ℕ)
    (hEnd : ∀ j, (s : I → I)^[len j] (a j) = b j)
    (hBlock : ∀ j x,
      (∑ e, if owner e = j ∧ src e = x then (1:ℕ) else 0) + (if j = x then 1 else 0) =
      (∑ e, if owner e = j ∧ dst e = s x then (1:ℕ) else 0) + (if j = s x then 1 else 0)) :
    let load x := (∑ j, ∑ p ∈ range (len j), if (s : I → I)^[p] (a j) = x then (1:ℕ) else 0) + pad
    ∀ x, (∑ e, if src e = x then load (owner e) else 0) + (∑ j, if b j = s x then (1:ℕ) else 0) =
      (∑ e, if dst e = s x then load (owner e) else 0) + (∑ j, if a j = s x then (1:ℕ) else 0) := by
  intro load x
  have hFlow : load (s x) + (∑ j, if b j = s x then (1:ℕ) else 0) =
      load x + (∑ j, if a j = s x then (1:ℕ) else 0) := by
    have h := sum_congr (s₁ := (univ : Finset J)) rfl
      (fun j _ => forward_load_telescope s (a j) x (len j))
    simp only [sum_add_distrib,hEnd] at h
    dsimp only [load]
    omega
  have hGroup (f : E → I) (y : I) :
      (∑ j, load j * ∑ e, if owner e = j ∧ f e = y then (1:ℕ) else 0) =
      ∑ e, if f e = y then load (owner e) else 0 := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    by_cases he : f e = y <;> simp [he,eq_comm (a := owner e)]
  have hBalance := sum_congr (s₁ := (univ : Finset I)) rfl
    (fun j _ => congrArg (load j * ·) (hBlock j x))
  simp only [mul_add,sum_add_distrib, mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,if_true] at hBalance
  rw [hGroup src x,hGroup dst (s x)] at hBalance
  omega

end OverfullWork.DirectedRobustExpansion
