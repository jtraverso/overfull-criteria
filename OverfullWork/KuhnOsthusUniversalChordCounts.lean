module

public import OverfullWork.KuhnOsthusRoutedChords
public import OverfullWork.DirectedMultigraphFactors

@[expose] public section


/-! The multiplicity calculation in Kühn–Osthus Lemma 9.1.
Elementary chord sequences contribute individual occurrences.
Padding along the Hamilton cycle makes the two semidegrees exact. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {I : Type*} [Fintype I]

omit [Fintype I] in
theorem elementary_count_balance (s : Equiv.Perm I) (j i : I) (l : List I)
    (hEnd : (j :: l).getLast? = some (s j)) :
    (chordSources s j l).count i + (if j = i then 1 else 0) =
      l.count (s i) + (if j = s i then 1 else 0) := by
  have hSplit : (j :: l).dropLast ++ [s j] = j :: l :=
    List.dropLast_append_getLast? (s j) (by simp [hEnd])
  have hRel := congrArg (List.count (s i)) hSplit
  have hMap : (chordSources s j l).count i = (j :: l).dropLast.count (s i) := by
    unfold chordSources
    simpa only [Equiv.symm_apply_apply] using
      List.count_map_of_injective (j :: l).dropLast s.symm s.symm.injective (s i)
  simp only [List.count_append,List.count_cons,List.count_nil,zero_add,beq_iff_eq,s.injective.eq_iff] at hRel
  omega

/-- Count labeled occurrences in the elementary chord sequences. -/
noncomputable def elementaryChordMultiplicity (s : Equiv.Perm I) (l : I → List I)
    (x y : I) : ℕ :=
  (univ.filter (fun p : Σ j, Fin (l j).length =>
    s.symm ((p.1 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt)) = x ∧
      (l p.1)[p.2.val] = y)).card

/-- Label chords by their individual positions in the elementary
sequences. Row sums at a cluster equal column sums at its successor. -/
theorem elementary_chord_multiplicities (R : Digraph I) (s : Equiv.Perm I)
    (l : I → List I)
    (hRoute : ∀ j, DirectedListRoutes.Route (reindexSources R s.symm) j (s j) (l j)) :
    let M := elementaryChordMultiplicity s l
    (∀ x y, 0 < M x y → R.Adj x y) ∧
      (∀ x, (∑ y, M x y) = ∑ j, (chordSources s j (l j)).count x) ∧
      (∀ y, (∑ x, M x y) = ∑ j, (l j).count y) ∧
      ∀ x, (∑ y, M x y) = ∑ y, M y (s x) := by
  let K := Σ j, Fin (l j).length
  let a (p : K) := s.symm ((p.1 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt))
  let b (p : K) := (l p.1)[p.2.val]
  intro M
  have hx (x : I) : (∑ y, M x y) = ∑ p : K, if a p = x then 1 else 0 := by
    simp only [M,elementaryChordMultiplicity,card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    change (∑ y, if a p = x ∧ b p = y then (1:ℕ) else 0) = _
    by_cases hp : a p = x
    · simp [hp]
    · simp [hp]
  have hy (y : I) : (∑ x, M x y) = ∑ p : K, if b p = y then 1 else 0 := by
    simp only [M,elementaryChordMultiplicity,card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    change (∑ x, if a p = x ∧ b p = y then (1:ℕ) else 0) = _
    by_cases hp : b p = y
    · simp [hp]
    · simp [hp]
  have hRow (x : I) : (∑ y, M x y) = ∑ j, (chordSources s j (l j)).count x := by
    rw [hx,Fintype.sum_sigma]
    apply sum_congr rfl
    intro j _
    rw [←sum_positions_eq_count]
    let e := finCongr (chordSources_length s j (l j)).symm
    apply Fintype.sum_equiv e
    intro p
    simp only [a,e,chordSources,List.getElem_map,List.getElem_dropLast]
    rfl
  have hCol (y : I) : (∑ x, M x y) = ∑ j, (l j).count y := by
    rw [hy,Fintype.sum_sigma]
    exact sum_congr rfl (fun j _ => sum_positions_eq_count (l j) y)
  refine ⟨?_,hRow,hCol,?_⟩
  · intro x y hm
    obtain ⟨p,hp⟩ := card_pos.mp hm
    obtain ⟨hx,hy⟩ := (mem_filter.mp hp).2
    have h := List.isChain_iff_getElem.mp (hRoute p.1).1 p.2.val
      (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using p.2.isLt)
    exact hx ▸ hy ▸ h
  · intro x
    rw [hRow,hCol]
    have h := sum_congr (s₁ := univ) rfl
      (fun j _ => elementary_count_balance s j x (l j) (hRoute j).2)
    simp only [sum_add_distrib,sum_ite_eq',mem_univ,ite_true] at h
    omega

/-- Pad the elementary chord multiplicity by successor edges and
factor everything apart from one distinguished copy of the base cycle.
The distinguished copy can later join the orbits of the other factors. -/
theorem exists_padded_chord_factorization (R : Digraph I) (s : Equiv.Perm I)
    (l : I → List I) (L : ℕ)
    (hs : ∀ i, R.Adj i (s i))
    (hRoute : ∀ j, DirectedListRoutes.Route (reindexSources R s.symm) j (s j) (l j))
    (hCap : ∀ x, (∑ j, (chordSources s j (l j)).count x) ≤ L) :
    let M := elementaryChordMultiplicity s l
    ∃ F : Fin L → Equiv.Perm I,
      (∀ i x, R.Adj x (F i x)) ∧
      (∀ x, (∑ y, M x y) = ∑ j, (chordSources s j (l j)).count x) ∧
      (∀ y, (∑ x, M x y) = ∑ j, (l j).count y) ∧
      ∀ x y, ((univ : Finset (Fin L)).filter (fun i => F i x = y)).card =
        M x y + if s x = y then L - (∑ z, M x z) else 0 := by
  intro M
  obtain ⟨hM,hRow,hCol,hBal⟩ := elementary_chord_multiplicities R s l hRoute
  let pad (x : I) := L - ∑ z, M x z
  let A (x y : I) := M x y + if s x = y then pad x else 0
  have hPay (x : I) : (∑ z, M x z) + pad x = L := by
    exact Nat.add_sub_of_le (by rw [hRow]; exact hCap x)
  have hOut (x : I) : (∑ y, A x y) = L := by
    simpa only [A,sum_add_distrib,sum_ite_eq,mem_univ,if_true] using hPay x
  have hIn (y : I) : (∑ x, A x y) = L := by
    simp only [A,sum_add_distrib,←s.eq_symm_apply,sum_ite_eq',mem_univ,if_true]
    rw [←s.apply_symm_apply y,←hBal]
    simpa only [Equiv.symm_apply_apply] using hPay (s.symm y)
  obtain ⟨F,hF⟩ := DirectedMultigraphFactors.exists_factorization A L hOut hIn
  refine ⟨F,?_,hRow,hCol,hF⟩
  intro i x
  have hPos : 0 < A x (F i x) := by
    rw [←hF]
    exact card_pos.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  by_cases h : s x = F i x
  · exact h ▸ hs x
  · apply hM
    simpa only [A,h,if_false,add_zero] using hPos

end OverfullWork.DirectedRobustExpansion
