module

public import OverfullWork.KuhnOsthusSwitchExchanges

@[expose] public section


/-! Keep the cyclic order of switch marks by recording the directed
segments from consecutive marks. A successor exchange permutes just
the two segments that leave its marks. -/
namespace OverfullWork.DirectedRobustExpansion

open Function
open scoped Classical
variable {V M : Type*}

/-- A finite marking of all cycles, with positive distances between
consecutive marks and no other marks in the intervening segments. -/
structure MarkedCycleSegments (σ : Equiv.Perm V) (mark : M ↪ V) (next : Equiv.Perm M) where
  span : M → ℕ
  positive : ∀ a, 0 < span a
  finish : ∀ a, (σ : V → V)^[span a] (mark a) = mark (next a)
  interior : ∀ a d, 0 < d → d < span a → ∀ b, (σ : V → V)^[d] (mark a) ≠ mark b
  covers : ∀ v, ∃ a d, d < span a ∧ (σ : V → V)^[d] (mark a) = v

theorem MarkedCycleSegments.sameCycle [Finite M] [Finite V]
    {σ : Equiv.Perm V} {mark : M ↪ V} {next : Equiv.Perm M}
    (H : MarkedCycleSegments σ mark next) (a b : M) :
    σ.SameCycle (mark a) (mark b) ↔ next.SameCycle a b := by
  have hForward (k : ℕ) :
      ∀ a b, (σ : V → V)^[k] (mark a) = mark b → next.SameCycle a b := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a b hAt
      by_cases hk : k = 0
      · subst k
        have he : a = b := mark.injective hAt
        subst b
        exact Equiv.Perm.SameCycle.refl _ _
      have hSpan : H.span a ≤ k := by
        by_contra! h
        exact H.interior a k (Nat.pos_of_ne_zero hk) h b hAt
      have hLess : k - H.span a < k := by have := H.positive a; omega
      have he : k - H.span a + H.span a = k := Nat.sub_add_cancel hSpan
      rw [← he, iterate_add_apply, H.finish] at hAt
      exact ((Equiv.Perm.SameCycle.refl next a).apply_right).trans (ih _ hLess _ _ hAt)
  have hBackward (k : ℕ) :
      σ.SameCycle (mark a) (mark ((next : M → M)^[k] a)) := by
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ k ih =>
      rw [iterate_succ_apply']
      have hAt := successor_sameCycle_iterate σ (mark ((next : M → M)^[k] a))
        (H.span ((next : M → M)^[k] a))
      rw [H.finish] at hAt
      exact ih.trans hAt
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow] at hk
    exact hForward k a b hk
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow] at hk
    exact hk ▸ hBackward k

theorem MarkedCycleSegments.cycle_meets_mark {σ : Equiv.Perm V}
    {mark : M ↪ V} {next : Equiv.Perm M}
    (H : MarkedCycleSegments σ mark next) (v : V) : ∃ a, σ.SameCycle (mark a) v := by
  obtain ⟨a,d,_,hd⟩ := H.covers v
  exact ⟨a,hd ▸ successor_sameCycle_iterate σ (mark a) d⟩

/-- A switch at two marks swaps their outgoing segments. All internal
vertices retain their successors, so the same vertices stay covered. -/
noncomputable def MarkedCycleSegments.switch {σ : Equiv.Perm V}
    {mark : M ↪ V} {next : Equiv.Perm M}
    (H : MarkedCycleSegments σ mark next) (a b : M) :
    MarkedCycleSegments (switchSuccessors σ (mark a) (mark b)) mark
      (switchSuccessors next a b) := by
  let ρ := switchSuccessors σ (mark a) (mark b)
  let s := Equiv.swap a b
  have hComm (u : M) : Equiv.swap (mark a) (mark b) (mark u) = mark (s u) := by
    simp only [s,Equiv.swap_apply_def,mark.injective.eq_iff]
    split_ifs <;> rfl
  have hTrace (u : M) (d : ℕ) (hd : d < H.span (s u)) :
      (ρ : V → V)^[d+1] (mark u) = (σ : V → V)^[d+1] (mark (s u)) := by
    induction d with
    | zero =>
      simp only [Nat.zero_add,iterate_one]
      change σ (Equiv.swap (mark a) (mark b) (mark u)) = _
      rw [hComm]
    | succ d ih =>
      rw [iterate_succ_apply' (ρ : V → V) (d+1) (mark u),ih (by omega),
        iterate_succ_apply' (σ : V → V) (d+1) (mark (s u))]
      exact switchSuccessors_off σ
        (H.interior (s u) (d+1) (by omega) hd a)
        (H.interior (s u) (d+1) (by omega) hd b)
  refine ⟨fun u => H.span (s u),fun u => H.positive (s u),?_,?_,?_⟩
  · intro u
    have hPos := H.positive (s u)
    have he : H.span (s u) - 1 + 1 = H.span (s u) := by omega
    have h := hTrace u (H.span (s u)-1) (by omega)
    rw [he,H.finish] at h
    exact h
  · intro u d hdPos hdLt v
    have h := hTrace u (d-1) (by omega)
    rw [show d-1+1=d by omega] at h
    rw [h]
    exact H.interior (s u) d hdPos hdLt v
  · intro v
    obtain ⟨u,d,hd,he⟩ := H.covers v
    by_cases hz : d = 0
    · subst d
      exact ⟨u,0,H.positive _,he⟩
    have hs : s (s u) = u := Equiv.swap_apply_self a b u
    refine ⟨s u,d,?_,?_⟩
    · simpa only [hs] using hd
    · have h := hTrace (s u) (d-1) (by rw [hs]; omega)
      rw [hs,show d-1+1=d by omega,he] at h
      exact h

/-- The marks have two lanes and a fixed cyclic order of columns.
The transition may change lanes, but always advances to the next column. -/
def OrderedReserve {I : Type*} (σ : Equiv.Perm V) (mark : Bool × I ↪ V)
    (step : Equiv.Perm I) : Prop :=
  ∃ next : Equiv.Perm (Bool × I),
    Nonempty (MarkedCycleSegments σ mark next) ∧ ∀ a, (next a).2 = step a.2

theorem OrderedReserve.switch {I : Type*} {σ : Equiv.Perm V} {mark : Bool × I ↪ V}
    {step : Equiv.Perm I} (H : OrderedReserve σ mark step) (c : I) :
    OrderedReserve (switchSuccessors σ (mark (false,c)) (mark (true,c))) mark step := by
  obtain ⟨next,⟨hSeg⟩,hStep⟩ := H
  refine ⟨_,⟨hSeg.switch (false,c) (true,c)⟩,?_⟩
  intro a
  simp only [switchSuccessors, Equiv.Perm.mul_apply]
  rw [hStep]
  congr 1
  by_cases ha : a = (false,c)
  · simp [ha]
  by_cases hb : a = (true,c)
  · simp [hb]
  simp [Equiv.swap_apply_def,ha,hb]

/-- Every cycle contains a mark in any specified column. In particular
the two final marks certify either one Hamilton cycle or a bicycle. -/
theorem OrderedReserve.cycle_meets_column [Finite V] {I : Type*} [Finite I]
    {σ : Equiv.Perm V} {mark : Bool × I ↪ V} {step : Equiv.Perm I}
    (H : OrderedReserve σ mark step) (c : I) (hStep : ∀ i, step.SameCycle i c) (v : V) :
    σ.SameCycle (mark (false,c)) v ∨ σ.SameCycle (mark (true,c)) v := by
  obtain ⟨next,⟨hSeg⟩,hNext⟩ := H
  obtain ⟨a,ha⟩ := hSeg.cycle_meets_mark v
  have hMap (k : ℕ) : (((next : Bool × I → Bool × I)^[k]) a).2 = (step : I → I)^[k] a.2 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [iterate_succ_apply',hNext,ih,iterate_succ_apply']
  obtain ⟨k,hk⟩ := (hStep a.2).exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hk
  let b := (next : Bool × I → Bool × I)^[k] a
  have hb : b = (b.1,c) := Prod.ext rfl ((hMap k).trans hk)
  have hCycle : next.SameCycle (b.1,c) a :=
    hb ▸ (successor_sameCycle_iterate next a k).symm
  have hv := ((hSeg.sameCycle (b.1,c) a).mpr hCycle).trans ha
  cases hLane : b.1
  · exact Or.inl (hLane ▸ hv)
  · exact Or.inr (hLane ▸ hv)

theorem OrderedReserve.hamilton_or_markedBicycle [Fintype V] {I : Type*} [Finite I]
    {σ : Equiv.Perm V} {mark : Bool × I ↪ V} {step : Equiv.Perm I}
    (H : OrderedReserve σ mark step) (c : I) (hStep : ∀ i, step.SameCycle i c) :
    (∀ v, σ.SameCycle (mark (false,c)) v) ∨ MarkedBicycle σ (mark (false,c)) (mark (true,c)) := by
  by_cases hSame : σ.SameCycle (mark (false,c)) (mark (true,c))
  · exact .inl fun v => (H.cycle_meets_column c hStep v).elim id hSame.trans
  · exact .inr ⟨hSame,H.cycle_meets_column c hStep⟩

end OverfullWork.DirectedRobustExpansion
