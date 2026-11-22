module

public import OverfullWork.OsthusStadenPrimaryRedSelection

@[expose] public section


/-! Allocate a distinct request slot per base red half and direction,
as used in Claim 5.3 of Osthus–Staden. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

theorem redPhase_eq_implies_mod_eq {p x y : ℕ} (hp : 0 < p)
    (h : redPhase p x = redPhase p y) : x%(2*p) = y%(2*p) := by
  have hTwo : 0 < 2*p := Nat.mul_pos (by decide) hp
  have hDvd : p ∣ 2*p := dvd_mul_left _ _
  have hx := Nat.mod_lt x hTwo
  have hy := Nat.mod_lt y hTwo
  have hP : x%(2*p)%p = y%(2*p)%p := by
    rw [Nat.mod_mod_of_dvd _ hDvd,Nat.mod_mod_of_dvd _ hDvd]
    have h₁ := congrArg (fun q : ZMod p × Bool => q.1.val) h
    simpa [redPhase,ZMod.val_natCast] using h₁
  have hB : decide (p ≤ x%(2*p)) = decide (p ≤ y%(2*p)) := congrArg Prod.snd h
  by_cases hxp : p ≤ x%(2*p)
  · have hyp : p ≤ y%(2*p) := by simpa only [decide_eq_true hxp,true_eq_decide_iff] using hB
    rw [Nat.mod_eq_sub_mod hxp,Nat.mod_eq_sub_mod hyp,Nat.mod_eq_of_lt (show x%(2*p)-p < p by omega),
      Nat.mod_eq_of_lt (show y%(2*p)-p < p by omega)] at hP
    omega
  · have hyp : ¬ p ≤ y%(2*p) := by
      intro hyp
      simp only [decide_eq_false hxp,decide_eq_true hyp,Bool.false_eq_true] at hB
    rwa [Nat.mod_eq_of_lt (lt_of_not_ge hxp),Nat.mod_eq_of_lt (lt_of_not_ge hyp)] at hP

/-- A phase has at most one original factor per complete block of 2p,
with one extra block allowed in the bound. -/
theorem red_phase_primary_count_le {r p : ℕ} (hp : 0 < p) (q : ZMod p × Bool) :
    ((univ : Finset (Fin r)).filter (fun t => redPhase p t.val = q)).card ≤ r/(2*p)+1 := by
  let target (t : Fin r) : Fin (r/(2*p)+1) := ⟨t.val/(2*p),by
    have h : t.val/(2*p) ≤ r/(2*p) := Nat.div_le_div_right t.isLt.le
    omega⟩
  rw [←Fintype.card_fin (r/(2*p)+1),←card_univ]
  apply card_le_card_of_injOn target (fun _ _ => mem_univ _)
  intro x hx y hy he
  have hxy : x.val/(2*p) = y.val/(2*p) := congrArg Fin.val he
  have hPhase := (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
  have hMod := redPhase_eq_implies_mod_eq hp hPhase
  have hVal := Nat.mod_add_div x.val (2*p)
  rw [hMod,hxy,Nat.mod_add_div] at hVal
  exact Fin.ext hVal.symm

/-- A single uniform bank size suffices even when the final block of
primary factors is incomplete. -/
def exceptionalPhaseBankSize (r s p : ℕ) : ℕ :=
  ((r/(2*p)+1)*((s-1)*(p-1)))/2

theorem exceptionalPhaseBankSize_pos {r s p : ℕ} (hs : 2 ≤ s) (hp : 3 ≤ p) :
    0 < exceptionalPhaseBankSize r s p := by
  have h₁ : 2 ≤ (s-1)*(p-1) := by
    have h := Nat.mul_le_mul (show 1 ≤ s-1 by omega) (show 2 ≤ p-1 by omega)
    simpa only [one_mul] using h
  have h₂ := Nat.mul_le_mul_right ((s-1)*(p-1)) (Nat.le_add_left 1 (r/(2*p)))
  have h : 2 ≤ (r/(2*p)+1)*((s-1)*(p-1)) := h₁.trans (by simpa only [one_mul] using h₂)
  unfold exceptionalPhaseBankSize
  omega

theorem red_phase_direction_count_le {r s p : ℕ} [NeZero s] [NeZero p]
    (hp : Odd p) (q : ZMod p × Bool) (dir : Bool) :
    ((univ : Finset (RefinedFactorIndex r s p)).filter
      (fun j => redPhase p j.1.val = q ∧ usesFirstRedHalf j = dir)).card ≤
        exceptionalPhaseBankSize r s p := by
  let T := (univ : Finset (Fin r)).filter (fun t => redPhase p t.val = q)
  let J := (univ : Finset (RefinedFactorIndex r s p)).filter (fun j => redPhase p j.1.val = q)
  let A (b : Bool) : Finset (RefinedFactorIndex r s p) :=
    univ.filter (fun j => redPhase p j.1.val = q ∧ usesFirstRedHalf j = b)
  have hProd : J = T ×ˢ (univ : Finset (UnwindingLabel s × UnwindingLabel p)) := by
    ext j
    simp [J,T]
  have hJ : J.card ≤ (r/(2*p)+1)*((s-1)*(p-1)) := by
    rw [hProd,card_product,card_univ,Fintype.card_prod]
    change T.card*(Fintype.card (UnwindingLabel s)*Fintype.card (UnwindingLabel p)) ≤ _
    rw [count_unwinding_increments,count_unwinding_increments]
    exact Nat.mul_le_mul_right _ (red_phase_primary_count_le (NeZero.pos p) q)
  have hUnion : A true ∪ A false = J := by
    ext j
    cases h : usesFirstRedHalf j <;> simp [A,J,h]
  have hDis : Disjoint (A true) (A false) := by
    apply disjoint_left.mpr
    intro j ht hf
    exact ((by decide) : true ≠ false) ((mem_filter.mp ht).2.2.symm.trans (mem_filter.mp hf).2.2)
  have hSum := card_union_of_disjoint hDis
  rw [hUnion] at hSum
  have hEq : (A true).card = (A false).card := red_phase_orientation_counts hp q
  change (A dir).card ≤ _
  unfold exceptionalPhaseBankSize
  cases dir <;> omega

/-- Requests for the same base half and direction fit injectively into
the common bank size. The clean-cell rule can only remove requests. -/
theorem exists_exceptional_phase_slots
    {I : Type*} {r s p : ℕ} [NeZero (2*s)] [NeZero p]
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)} (D : PrimaryRedSelection (p := p) C)
    (hp : Odd p) (dir : Bool) (i : I) (z : Fin (2*s)) (q : ZMod p × Bool) :
    let requests := (univ : Finset (RefinedFactorIndex r (2*s) p)).filter
      (fun j => redPhase p j.1.val = q ∧ z ∈ D.select dir j i)
    Nonempty (↥requests ↪ Fin (exceptionalPhaseBankSize r (2*s) p)) := by
  intro requests
  let b := if z.val < s then dir else !dir
  have hSub : requests ⊆ (univ : Finset (RefinedFactorIndex r (2*s) p)).filter
      (fun j => redPhase p j.1.val = q ∧ usesFirstRedHalf j = b) := by
    intro j hj
    obtain ⟨hq,hz⟩ := (mem_filter.mp hj).2
    have hh := D.in_half dir j i z hz
    refine mem_filter.mpr ⟨mem_univ _,hq,?_⟩
    by_cases hsmall : z.val < s
    · rw [show b = dir from if_pos hsmall]
      by_contra h
      rw [if_neg (Ne.symm h)] at hh
      omega
    · rw [show b = !dir from if_neg hsmall]
      have hne : dir ≠ usesFirstRedHalf j := by
        intro he
        rw [if_pos he] at hh
        exact hsmall hh
      cases dir <;> cases he : usesFirstRedHalf j <;> simp_all
  have hCard : requests.card ≤ exceptionalPhaseBankSize r (2*s) p :=
    (card_le_card hSub).trans (red_phase_direction_count_le hp q b)
  exact ⟨(Fintype.equivFinOfCardEq (Fintype.card_coe requests)).toEmbedding.trans (Fin.castLEEmb hCard)⟩

end OverfullWork.DirectedRobustExpansion
