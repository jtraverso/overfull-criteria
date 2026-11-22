module

public import OverfullWork.KuhnOsthusMarkedSubdivision
public import OverfullWork.KuhnOsthusAlternatingSwitchOrder
public import OverfullWork.KuhnOsthusWindingIntervalGeometry

@[expose] public section


/-! In each row of (CyA3), one turn through a copy index visits the
two switch sources at offsets 0 and 4. The last index also visits the
reserved repair source at offset 8 before the return to the first copy. -/
namespace OverfullWork.DirectedRobustExpansion

open Function
open scoped Classical
variable {V : Type*}

def cycleAbsorberLastCopy (m : ℕ) (hm : 0 < m) : Fin m := ⟨m-1,by omega⟩

def cycleAbsorberColumn {m : ℕ} (i : Fin m) (b : Fin 2) : Fin (2*m+1) :=
  (cycleAbsorberSwitchSlot m (i,b)).castSucc

noncomputable def cycleAbsorberLane : Bool ≃ Fin 2 :=
  Equiv.ofBijective (fun b => if b then 1 else 0) ⟨by
    intro b c
    cases b <;> cases c <;> decide,by
    intro c
    fin_cases c
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩⟩

def cycleAbsorberReturn (m : ℕ) : Equiv.Perm (Fin m × Fin 2) :=
  Equiv.prodCongr (finRotate m) (Equiv.refl _)

def cycleAbsorberColumnCoordinates {m : ℕ} (hm : 0 < m) (c : Fin (2*m+1)) : Fin m × ℕ :=
  Fin.lastCases (cycleAbsorberLastCopy m hm,8)
    (fun j => let i := (cycleAbsorberSwitchSlot m).symm j; (i.1,4*i.2.val)) c

@[simp] theorem cycleAbsorberColumnCoordinates_column {m : ℕ} (hm : 0 < m) (i : Fin m) (b : Fin 2) :
    cycleAbsorberColumnCoordinates hm (cycleAbsorberColumn i b) = (i,4*b.val) := by
  simp [cycleAbsorberColumnCoordinates,cycleAbsorberColumn]

@[simp] theorem cycleAbsorberColumnCoordinates_last {m : ℕ} (hm : 0 < m) :
    cycleAbsorberColumnCoordinates hm (Fin.last (2*m)) = (cycleAbsorberLastCopy m hm,8) := by
  simp [cycleAbsorberColumnCoordinates]

theorem cycleAbsorber_column_cases {m : ℕ} (j : Fin (2*m+1)) :
    (∃ i, j = cycleAbsorberColumn i 0) ∨ (∃ i, j = cycleAbsorberColumn i 1) ∨ j = Fin.last _ := by
  refine Fin.lastCases (.inr (.inr rfl)) (fun j => ?_) j
  obtain ⟨⟨i,b⟩,rfl⟩ := (cycleAbsorberSwitchSlot m).surjective j
  fin_cases b
  · exact .inl ⟨i,rfl⟩
  · exact .inr (.inl ⟨i,rfl⟩)

theorem cycleAbsorber_column_val {m : ℕ} (i : Fin m) (b : Fin 2) :
    (cycleAbsorberColumn i b).val = 2*i.val+b.val := cycleAbsorberSwitchSlot_val i b

theorem cycleAbsorber_column_first_next {m : ℕ} (i : Fin m) :
    finRotate (2*m+1) (cycleAbsorberColumn i 0) = cycleAbsorberColumn i 1 := by
  apply Fin.ext
  rw [finRotate_val_modulo,cycleAbsorber_column_val,cycleAbsorber_column_val]
  have hi := i.isLt
  simp only [Fin.val_zero,Fin.val_one,add_zero]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem cycleAbsorber_column_second_next {m : ℕ} (hm : 0 < m) (i : Fin m)
    (hi : i ≠ cycleAbsorberLastCopy m hm) :
    finRotate (2*m+1) (cycleAbsorberColumn i 1) = cycleAbsorberColumn (finRotate m i) 0 := by
  have he : i.val ≠ m-1 := fun h => hi (Fin.ext h)
  have hlt : i.val+1 < m := by have := i.isLt; omega
  apply Fin.ext
  rw [finRotate_val_modulo,cycleAbsorber_column_val,cycleAbsorber_column_val,finRotate_val_modulo,
    Nat.mod_eq_of_lt hlt]
  simp only [Fin.val_zero,Fin.val_one,add_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem cycleAbsorber_column_second_last {m : ℕ} (hm : 0 < m) :
    finRotate (2*m+1) (cycleAbsorberColumn (cycleAbsorberLastCopy m hm) 1) = Fin.last _ := by
  apply Fin.ext
  rw [finRotate_val_modulo,cycleAbsorber_column_val]
  simp only [cycleAbsorberLastCopy,Fin.val_one,Fin.val_last]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem cycleAbsorber_column_last_next {m : ℕ} (hm : 0 < m) :
    finRotate (2*m+1) (Fin.last (2*m)) = cycleAbsorberColumn (finRotate m (cycleAbsorberLastCopy m hm)) 0 := by
  apply Fin.ext
  rw [finRotate_val_modulo,cycleAbsorber_column_val,finRotate_val_modulo]
  simp only [Fin.val_last,cycleAbsorberLastCopy,Fin.val_zero,add_zero,Nat.mod_self]
  have he : m-1+1 = m := by omega
  rw [he,Nat.mod_self,Nat.mul_zero]

/-- Insert the sources of all switches along the coarse return tour.
The new successor steps through the columns in cyclic order and
preserves the row. -/
noncomputable def cycleAbsorberMarkSubdivision {σ : Equiv.Perm V} {m : ℕ} (hm : 0 < m)
    {mark : Fin m × Fin 2 ↪ V}
    (H : MarkedCycleSegments σ mark (cycleAbsorberReturn m)) (hSpan : ∀ j, 8 < H.span j) :
    MarkedSegmentSubdivision H
      (Equiv.prodCongr (Equiv.refl Bool) (finRotate (2*m+1))) := by
  let last := cycleAbsorberLastCopy m hm
  let q := cycleAbsorberColumnCoordinates hm
  let base (j : Bool × Fin (2*m+1)) : Fin m × Fin 2 := ((q j.2).1,cycleAbsorberLane j.1)
  let start (j : Bool × Fin (2*m+1)) : ℕ := (q j.2).2
  let len (j : Bool × Fin (2*m+1)) : ℕ :=
    if start j = 0 ∨ start j = 4 ∧ (base j).1 = last then 4
    else H.span (base j)-start j
  have h0 (a : Bool) (i : Fin m) :
      base (a,cycleAbsorberColumn i 0) = (i,cycleAbsorberLane a) ∧
      start (a,cycleAbsorberColumn i 0) = 0 ∧ len (a,cycleAbsorberColumn i 0) = 4 := by
    simp [base,start,len,q]
  have h1 (a : Bool) (i : Fin m) :
      base (a,cycleAbsorberColumn i 1) = (i,cycleAbsorberLane a) ∧
      start (a,cycleAbsorberColumn i 1) = 4 ∧ len (a,cycleAbsorberColumn i 1) =
        if i = last then 4 else H.span (i,cycleAbsorberLane a)-4 := by
    simp [base,start,len,q]
  have hE (a : Bool) :
      base (a,Fin.last (2*m)) = (last,cycleAbsorberLane a) ∧
      start (a,Fin.last (2*m)) = 8 ∧ len (a,Fin.last (2*m)) = H.span (last,cycleAbsorberLane a)-8 := by
    simp [base,start,len,q,last]
  refine ⟨base,start,len,?_,?_,?_,?_⟩
  · rintro ⟨a,c⟩
    rcases cycleAbsorber_column_cases c with ⟨i,rfl⟩ | ⟨i,rfl⟩ | rfl
    · simp [(h0 a i).2.2]
    · rw [(h1 a i).2.2]
      have := hSpan (i,cycleAbsorberLane a)
      split <;> omega
    · rw [(hE a).2.2]
      have := hSpan (last,cycleAbsorberLane a)
      omega
  · rintro ⟨a,c⟩
    rcases cycleAbsorber_column_cases c with ⟨i,rfl⟩ | ⟨i,rfl⟩ | rfl
    · obtain ⟨hb,hs,hl⟩ := h0 a i
      rw [hb,hs,hl]
      have := hSpan (i,cycleAbsorberLane a)
      omega
    · obtain ⟨hb,hs,hl⟩ := h1 a i
      rw [hb,hs,hl]
      have := hSpan (i,cycleAbsorberLane a)
      split <;> omega
    · obtain ⟨hb,hs,hl⟩ := hE a
      rw [hb,hs,hl]
      have := hSpan (last,cycleAbsorberLane a)
      omega
  · rintro ⟨a,c⟩
    change (base (a,finRotate _ c) = base (a,c) ∧ start (a,finRotate _ c) = start (a,c) + len (a,c)) ∨
      (base (a,finRotate _ c) = cycleAbsorberReturn m (base (a,c)) ∧
        start (a,finRotate _ c) = 0 ∧ start (a,c)+len (a,c) = H.span (base (a,c)))
    rcases cycleAbsorber_column_cases c with ⟨i,rfl⟩ | ⟨i,rfl⟩ | rfl
    · left
      rw [cycleAbsorber_column_first_next,(h0 a i).1,(h1 a i).1,(h0 a i).2.1,
        (h0 a i).2.2,(h1 a i).2.1]
      exact ⟨rfl,rfl⟩
    · by_cases hi : i = last
      · subst i
        left
        rw [cycleAbsorber_column_second_last hm,(h1 a last).1,(hE a).1,(h1 a last).2.1,
          (h1 a last).2.2,if_pos rfl,(hE a).2.1]
        exact ⟨rfl,rfl⟩
      · right
        rw [cycleAbsorber_column_second_next hm i hi,(h1 a i).1,(h1 a i).2.1,(h1 a i).2.2,
          if_neg hi,(h0 a (finRotate m i)).1,(h0 a (finRotate m i)).2.1]
        have := hSpan (i,cycleAbsorberLane a)
        exact ⟨rfl,rfl,by omega⟩
    · right
      rw [cycleAbsorber_column_last_next hm,(hE a).1,(hE a).2.1,(hE a).2.2,
        (h0 a (finRotate m last)).1,(h0 a (finRotate m last)).2.1]
      have := hSpan (last,cycleAbsorberLane a)
      exact ⟨rfl,rfl,by omega⟩
  · intro x k hk
    let locate (i : Fin m) (k : ℕ) : Fin (2*m+1) :=
      if k < 4 then cycleAbsorberColumn i 0
      else if i = last ∧ 8 ≤ k then Fin.last _ else cycleAbsorberColumn i 1
    have hSelect (g : Bool × Fin (2*m+1)) (hStart : start g ≤ k) (hEnd : k < start g + len g) :
        g.2 = locate (base g).1 k := by
      obtain ⟨a,c⟩ := g
      rcases cycleAbsorber_column_cases c with ⟨i,rfl⟩ | ⟨i,rfl⟩ | rfl
      · obtain ⟨hb,hs,hl⟩ := h0 a i
        rw [hs,hl] at hEnd
        simp only [hb,locate,if_pos (show k < 4 by omega)]
      · obtain ⟨hb,hs,hl⟩ := h1 a i
        rw [hs,hl] at hEnd
        rw [hs] at hStart
        simp only [hb,locate,if_neg (not_lt_of_ge hStart)]
        by_cases hi : i = last
        · rw [if_pos hi] at hEnd
          rw [if_neg (show ¬ (i = last ∧ 8 ≤ k) by omega)]
        · rw [if_neg (fun h : i = last ∧ 8 ≤ k => hi h.1)]
      · obtain ⟨hb,hs,hl⟩ := hE a
        rw [hs] at hStart
        simp [locate,hb,show ¬ k < 4 by omega,hStart]
    obtain ⟨i,b⟩ := x
    let a := cycleAbsorberLane.symm b
    have hba : cycleAbsorberLane a = b := cycleAbsorberLane.apply_symm_apply b
    refine ⟨(a,locate i k),?_,?_⟩
    · by_cases h : k < 4
      · simp only [locate,if_pos h]
        obtain ⟨hb,hs,hl⟩ := h0 a i
        rw [hb,hs,hl,hba]
        exact ⟨rfl,Nat.zero_le _,by omega⟩
      · by_cases h' : i = last ∧ 8 ≤ k
        · simp only [locate,if_neg h,if_pos h']
          obtain ⟨hb,hs,hl⟩ := hE a
          rw [hb,hs,hl,hba,←h'.1]
          exact ⟨rfl,h'.2,by omega⟩
        · simp only [locate,if_neg h,if_neg h']
          obtain ⟨hb,hs,hl⟩ := h1 a i
          rw [hb,hs,hl,hba]
          refine ⟨rfl,by omega,?_⟩
          by_cases hi : i = last
          · rw [if_pos hi]
            omega
          · rw [if_neg hi]
            omega
    · rintro ⟨b',c⟩ ⟨hb,hl,hr⟩
      have hLane : cycleAbsorberLane b' = b := congrArg Prod.snd hb
      have ha : b' = a := cycleAbsorberLane.injective (hLane.trans hba.symm)
      have hc := hSelect (b',c) hl hr
      rw [hb] at hc
      exact Prod.ext ha hc

end OverfullWork.DirectedRobustExpansion
