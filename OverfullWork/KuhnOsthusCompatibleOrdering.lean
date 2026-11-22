module

public import OverfullWork.KuhnOsthusTypeOrdering
public import Mathlib.Data.Fintype.Powerset

@[expose] public section


/-! The augmenting exchange of Kühn–Osthus Lemma 9.6.
A full bijection labels both the assigned and the unassigned positions.
The active positions form the partial assignment that is maximized. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- The finite set satisfying a predicate, using a fixed decision
instance so that the same set can be transported between coordinates. -/
noncomputable def finiteSatisfying {A : Type*} [Fintype A] (p : A → Prop) : Finset A :=
  univ.filter p

@[simp] theorem mem_finiteSatisfying {A : Type*} [Fintype A] {p : A → Prop} {x : A} :
    x ∈ finiteSatisfying p ↔ p x := by
  simp [finiteSatisfying]

private theorem satisfying_card_preimage_le (e : I ↪ J) (p : J → Prop) :
    (finiteSatisfying (fun i => p (e i))).card ≤ (finiteSatisfying p).card :=
  card_le_card_of_injOn e
    (fun i hi => by
      have hp : p (e i) := (mem_finiteSatisfying (p := fun j => p (e j))).mp hi
      exact mem_finiteSatisfying.mpr hp) e.injective.injOn

omit [Fintype I] [Fintype K] in
private theorem card_biUnion_bound (S : Finset I) (A : I → Finset K) (a : ℕ)
    (hA : ∀ i, (A i).card ≤ a) : (S.biUnion A).card ≤ S.card*a :=
  card_biUnion_le.trans (by simpa using sum_le_sum (s := S) (fun i _ => hA i))

/-- Extend a partial bijective assignment by a two-edge exchange.
The degree bounds count forbidden position–label pairs in both
directions and the conflicts between nearby labels. -/
theorem exists_compatible_ordering (r : I → I → Prop) (s : J → J → Prop)
    (forbidden : I → J → Prop) (e₀ : I ≃ J)
    (hr : ∀ {x y}, r x y → r y x) (hs : ∀ {x y}, s x y → s y x)
    (hirr : ∀ x, ¬ r x x) (a b c d : ℕ)
    (hR : ∀ x, (finiteSatisfying (r x)).card ≤ a)
    (hS : ∀ y, (finiteSatisfying (s y)).card ≤ b)
    (hRow : ∀ x, (finiteSatisfying (forbidden x)).card ≤ c)
    (hCol : ∀ y, (finiteSatisfying (fun x => forbidden x y)).card ≤ d)
    (hSize : 2*a*b+a+1+c+d < Fintype.card I) :
    ∃ e : I ≃ J, (∀ x, ¬ forbidden x (e x)) ∧ ∀ x y, r x y → ¬ s (e x) (e y) := by
  let feasible (e : I ≃ J) (T : Finset I) :=
    (∀ x ∈ T, ¬ forbidden x (e x)) ∧ ∀ x ∈ T, ∀ y ∈ T, r x y → ¬ s (e x) (e y)
  let P := finiteSatisfying (fun p : Equiv.Perm I × Finset I => feasible (p.1.trans e₀) p.2)
  have hEmpty : (Equiv.refl I, ∅) ∈ P :=
    mem_finiteSatisfying.mpr ⟨by simp,by simp⟩
  obtain ⟨⟨p,T⟩,hPT,hMax⟩ := exists_max_image P (fun p => p.2.card) ⟨_,hEmpty⟩
  let e := p.trans e₀
  have hT : feasible e T :=
    (mem_finiteSatisfying (p := fun p : Equiv.Perm I × Finset I => feasible (p.1.trans e₀) p.2)).mp hPT
  have hAll : T = univ := by
    by_contra hNot
    obtain ⟨x,hx⟩ : ∃ x, x ∉ T := by
      by_contra! he
      exact hNot (eq_univ_iff_forall.mpr he)
    let near (v : I) := finiteSatisfying (r v)
    let conflict (v : I) := finiteSatisfying (fun w => s (e v) (e w))
    let X := near x
    let L := X.biUnion conflict
    let R := (conflict x).biUnion near
    let C := finiteSatisfying (fun z => forbidden x (e z))
    let D := finiteSatisfying (fun z => forbidden z (e x))
    let S := insert x (X ∪ L ∪ R ∪ C ∪ D)
    have hX : X.card ≤ a := hR x
    have hConflict (v : I) : (conflict v).card ≤ b :=
      (satisfying_card_preimage_le e.toEmbedding (s (e v))).trans (hS (e v))
    have hL : L.card ≤ a*b := (card_biUnion_bound X conflict b hConflict).trans
      (Nat.mul_le_mul_right b hX)
    have hR' : R.card ≤ a*b := (card_biUnion_bound (conflict x) near a hR).trans
      (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right a (hConflict x))
    have hC : C.card ≤ c :=
      (satisfying_card_preimage_le e.toEmbedding (forbidden x)).trans (hRow x)
    have hD : D.card ≤ d := hCol (e x)
    have hSCard : S.card ≤ 2*a*b+a+1+c+d := by
      have h₁ := card_union_le X L
      have h₂ := card_union_le (X ∪ L) R
      have h₃ := card_union_le (X ∪ L ∪ R) C
      have h₄ := card_union_le (X ∪ L ∪ R ∪ C) D
      have h₅ : S.card ≤ (X ∪ L ∪ R ∪ C ∪ D).card+1 := card_insert_le _ _
      rw [Nat.mul_assoc,two_mul]
      omega
    obtain ⟨z,hz⟩ : ∃ z, z ∉ S := by
      by_contra! hh
      rw [eq_univ_iff_forall.mpr hh,card_univ] at hSCard
      omega
    have hzx : z ≠ x := fun h => hz (h ▸ mem_insert_self _ _)
    have hzNo : z ∉ X ∧ z ∉ L ∧ z ∉ R ∧ z ∉ C ∧ z ∉ D := by
      have hh : z ∉ X ∪ L ∪ R ∪ C ∪ D := fun h => hz (mem_insert_of_mem h)
      simp only [mem_union,not_or] at hh
      exact ⟨hh.1.1.1.1,hh.1.1.1.2,hh.1.1.2,hh.1.2,hh.2⟩
    have hxz : ¬ r x z := fun h => hzNo.1 (mem_finiteSatisfying.mpr h)
    let p' := (Equiv.swap x z).trans p
    let e' := p'.trans e₀
    have he (v : I) : e' v = e (Equiv.swap x z v) := rfl
    have hXeq : e' x = e z := by rw [he,Equiv.swap_apply_left]
    have hZeq : e' z = e x := by rw [he,Equiv.swap_apply_right]
    have hOld (v : I) (hvx : v ≠ x) (hvz : v ≠ z) : e' v = e v := by
      rw [he,Equiv.swap_apply_of_ne_of_ne hvx hvz]
    have hxPair (v : I) (hv : r x v) : ¬ s (e' x) (e' v) := by
      have hvx : v ≠ x := fun h => hirr x (h ▸ hv)
      have hvz : v ≠ z := fun h => hxz (h ▸ hv)
      rw [hXeq,hOld v hvx hvz]
      intro h
      exact hzNo.2.1 (mem_biUnion.mpr ⟨v,mem_finiteSatisfying.mpr hv,mem_finiteSatisfying.mpr (hs h)⟩)
    have hzPair (v : I) (hv : r z v) : ¬ s (e' z) (e' v) := by
      have hvx : v ≠ x := fun h => hxz (hr (h ▸ hv))
      have hvz : v ≠ z := fun h => hirr z (h ▸ hv)
      rw [hZeq,hOld v hvx hvz]
      intro h
      exact hzNo.2.2.1 (mem_biUnion.mpr ⟨v,mem_finiteSatisfying.mpr h,mem_finiteSatisfying.mpr (hr hv)⟩)
    have hNew : feasible e' (insert x T) := by
      constructor
      · intro v hv
        by_cases heX : v = x
        · subst v
          rw [hXeq]
          exact fun hh => hzNo.2.2.2.1 (mem_finiteSatisfying.mpr hh)
        by_cases heZ : v = z
        · subst v
          rw [hZeq]
          exact fun hh => hzNo.2.2.2.2 (mem_finiteSatisfying.mpr hh)
        rw [hOld v heX heZ]
        exact hT.1 v ((mem_insert.mp hv).resolve_left heX)
      · intro v hv w hw h
        by_cases hvx : v = x
        · subst v
          exact hxPair w h
        by_cases hvz : v = z
        · subst v
          exact hzPair w h
        by_cases hwx : w = x
        · subst w
          exact fun hh => hxPair v (hr h) (hs hh)
        by_cases hwz : w = z
        · subst w
          exact fun hh => hzPair v (hr h) (hs hh)
        rw [hOld v hvx hvz,hOld w hwx hwz]
        exact hT.2 v ((mem_insert.mp hv).resolve_left hvx) w ((mem_insert.mp hw).resolve_left hwx) h
    have hle : (insert x T).card ≤ T.card :=
      hMax (p',insert x T) (mem_finiteSatisfying.mpr hNew)
    rw [card_insert_of_notMem hx] at hle
    omega
  rw [hAll] at hT
  exact ⟨e,fun x => hT.1 x (mem_univ _),fun x y => hT.2 x (mem_univ _) y (mem_univ _)⟩

end OverfullWork.DirectedRobustExpansion
