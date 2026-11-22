module

public import OverfullWork.KuhnOsthusWalkArcRealization
public import OverfullWork.KuhnOsthusWalkBankPartition

@[expose] public section


/-! The exact physical realization in Lemma 9.5 uses one bank from
(CA2). Every arc in the bank is assigned, and the cut prevents
all circuits in the resulting walk paths. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
variable {V : Type*} [Fintype V]

private def cutQuarterOrder {n : ℕ} (j : Fin (n+2)) : Equiv.Perm (Fin 4) :=
  if j = Fin.last (n+1) then (finRotate 4).trans (finRotate 4) else Equiv.refl _

private theorem cut_quarter_order_val {n : ℕ} (j : Fin (n+2)) (a : Fin 4) :
    (cutQuarterOrder j a).val = (a.val + if j = Fin.last (n+1) then 2 else 0)%4 := by
  by_cases h : j = Fin.last (n+1)
  · rw [cutQuarterOrder,if_pos h,if_pos h]
    fin_cases a <;> decide
  · rw [cutQuarterOrder,if_neg h,if_neg h,add_zero,Nat.mod_eq_of_lt a.isLt]
    rfl

/-- Split the physical walk reserve into prescribed path systems.
The conclusion gives the exact per-pair loads, coverage of the
whole bank, avoidance of the prescribed systems, and acyclicity. -/
theorem realize_physical_walk_bank {n b k m : ℕ} (s : ℕ)
    (rank : V → Fin (n+2)) (quarter : V → Fin 4)
    (Q : Fin (n+2) × Fin 4 → Finset V)
    (M : ∀ j : Fin (n+2) × Fin 4, Fin k → Q j ≃ Q (finRotate (n+2) j.1,j.2))
    (w : Fin (n+2) → Fin b → Fin 10 → ℕ) (P : Fin b → Fin 10 → Finset V)
    (hM : 0 < k*m) (hQ : 110 < 10*b) (hWidth : 3*s*(10*b) ≤ k*m)
    (hRoom : 3*(130*s) ≤ m) (hSize : ∀ j, (Q j).card = m)
    (hCell : ∀ j v, v ∈ Q j → rank v = j.1 ∧ quarter v = j.2)
    (hApart : ∀ j p q, p ≠ q → ∀ x, M j p x ≠ M j q x)
    (hLo : ∀ j a i, 11*s ≤ w j a i) (hHi : ∀ j a i, w j a i ≤ 13*s)
    (hTotal : ∀ j, (∑ a,∑ i, w j a i) = 4*(k*m))
    (hDis : ∀ a i i', i ≠ i' → Disjoint (P a i) (P a i'))
    (hMeet : ∀ j a i,
      (P a i ∩ finiteSatisfying (fun x => rank x = j)).card +
        (P a i ∩ finiteSatisfying (fun x => rank x = finRotate (n+2) j)).card ≤ 2*s) :
    let next := (finRotate (n+2)).prodCongr (Equiv.refl (Fin 4))
    let U := successorCellMatchingUnion Q next M
    ∃ D : Fin b × Fin 10 → Digraph V,
      (∀ x y, U.Adj x y ↔ ∃! p, (D p).Adj x y) ∧
      (∀ p, D p ≤ U) ∧
      (∀ p x y, (D p).Adj x y → rank y = finRotate (n+2) (rank x)) ∧
      (∀ a i, IsDirectedPathSystem (D (a,i))) ∧
      (∀ a i x, IncidentTo (D (a,i)) x → x ∉ P a i) ∧
      (∀ j a i, Fintype.card (Arc ⟨fun x y => (D (a,i)).Adj x y ∧ rank x = j⟩) = w j a i) := by
  intro next U
  let r := finRotate (n+2)
  have hDisQ (j : Fin (n+2)) (i i' : Fin 4) (hne : i ≠ i') :
      Disjoint (Q (j,i)) (Q (j,i')) := by
    rw [disjoint_left]
    intro v hv hv'
    exact hne ((hCell _ _ hv).2.symm.trans (hCell _ _ hv').2)
  have hOrders (j : Fin (n+2)) := exists_ordered_physical_walk_pair
    (fun i => Q (j,i)) (fun i => Q (r j,i)) (fun i => M (j,i)) (cutQuarterOrder j)
    (130*s) hRoom (fun i => hSize (j,i)) (hDisQ j) (hDisQ (r j))
  choose order hOrder hWindow using hOrders
  let source (j : Fin (n+2)) (p : Fin (4*(k*m))) := (order j p).2.2.val
  let target (j : Fin (n+2)) (p : Fin (4*(k*m))) :=
    (M (j,(order j p).1) (order j p).2.1 (order j p).2.2).val
  have hSource (j : Fin (n+2)) (p : Fin (4*(k*m))) :
      rank (source j p) = j ∧ quarter (source j p) = (order j p).1 :=
    hCell _ _ (order j p).2.2.prop
  have hTarget (j : Fin (n+2)) (p : Fin (4*(k*m))) :
      rank (target j p) = r j ∧ quarter (target j p) = (order j p).1 :=
    hCell _ _ (M (j,(order j p).1) (order j p).2.1 (order j p).2.2).prop
  have hColour (j : Fin (n+2)) (p : Fin (4*(k*m))) : (order j p).1.val =
      (p.val/(k*m)+if j = Fin.last (n+1) then 2 else 0)%4 := by
    rw [hOrder,cut_quarter_order_val]
    rfl
  have hInj (j : Fin (n+2)) : Function.Injective (fun p => (source j p,target j p)) := by
    intro p q he
    have hs := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    have hq : (order j p).1 = (order j q).1 :=
      (hSource j p).2.symm.trans ((congrArg quarter hs).trans (hSource j q).2)
    apply (order j).injective
    revert hs ht hq
    generalize hp : order j p = u
    generalize hp' : order j q = v
    dsimp only [source,target]
    rw [hp,hp']
    rcases u with ⟨i,a,x⟩
    rcases v with ⟨i',a',x'⟩
    dsimp only
    intro hs ht he
    subst i'
    have hx : x = x' := Subtype.ext hs
    subst x'
    have ha : a = a' := by
      by_contra hn
      exact hApart (j,i) a a' hn x (Subtype.ext ht)
    subst a'
    rfl
  have hSame (x y : V) : U.Adj x y ↔ ∃ j p, source j p = x ∧ target j p = y := by
    constructor
    · rintro ⟨⟨j,i⟩,a,v,hx,hy⟩
      obtain ⟨p,hp⟩ := (order j).surjective ⟨i,a,v⟩
      exact ⟨j,p,by unfold source; rw [hp]; exact hx,by unfold target; rw [hp]; exact hy⟩
    · rintro ⟨j,p,hx,hy⟩
      exact ⟨(j,(order j p).1),(order j p).2.1,(order j p).2.2,hx,hy⟩
  obtain ⟨D,hPartition,hLe,hStep,hPath,hAvoid,hCard⟩ := exists_walk_arc_realization s rank quarter
    source target w P hM hQ hWidth (fun j p => (hSource j p).1) (fun j p => (hTarget j p).1)
    (fun j p => (congrArg Fin.val (hSource j p).2).trans (hColour j p))
    (fun j p => (congrArg Fin.val (hTarget j p).2).trans (hColour j p))
    hInj hWindow hLo hHi hTotal hDis hMeet
  exact ⟨D,fun x y => (hSame x y).trans (hPartition x y),
    fun p x y h => (hSame x y).mpr (hLe p h),hStep,hPath,hAvoid,hCard⟩

end OverfullWork.DirectedRobustExpansion
