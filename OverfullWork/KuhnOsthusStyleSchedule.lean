module

public import OverfullWork.KuhnOsthusStyleAssignments
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Prod

@[expose] public section


/-! The two style assignments in Kühn–Osthus Lemma 8.1. The
exceptional slots use five styles with twenty intervals each. The
remaining slots can receive pieces indexed by unordered double styles. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset

abbrev DoubleStyle := ↥((univ : Finset (Fin 50)).powersetCard 2)

def isReservedStyleSlot {l : ℕ} (b : Fin 50 × Fin l) : Prop :=
  b.1.val < 5 ∧ b.2.val < 20

instance {l : ℕ} : DecidablePred (isReservedStyleSlot (l := l)) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Choose an unordered two-element style containing the two labels.
Coincident labels can be extended by any other style. -/
theorem exists_double_style (a b : Fin 50) :
    ∃ j : DoubleStyle, a ∈ j.val ∧ b ∈ j.val := by
  by_cases hab : a = b
  · obtain ⟨c,hc⟩ := exists_ne a
    have hs : ({a,c} : Finset (Fin 50)).card = 2 := card_pair hc.symm
    exact ⟨⟨{a,c},mem_powersetCard.mpr ⟨subset_univ _,hs⟩⟩,by simp,by simp [←hab]⟩
  · exact ⟨⟨{a,b},mem_powersetCard.mpr ⟨subset_univ _,card_pair hab⟩⟩,by simp,by simp⟩

theorem card_double_style : Fintype.card DoubleStyle = 1225 := by
  rw [Fintype.card_coe,card_powersetCard,card_univ,Fintype.card_fin]
  decide

private theorem card_double_styles_containing (j : Fin 50) :
    Fintype.card {b : DoubleStyle // j ∈ b.val} = 49 := by
  let S := (univ : Finset (Fin 50)).powersetCard 2
  let T := S.filter (fun a => j ∈ a)
  let e : {b : DoubleStyle // j ∈ b.val} ≃ T :=
    { toFun := fun b => ⟨b.val.val,mem_filter.mpr ⟨b.val.prop,b.prop⟩⟩
      invFun := fun b => ⟨⟨b.val,(mem_filter.mp b.prop).1⟩,(mem_filter.mp b.prop).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_coe]
  have he : T = S.filter (fun a => {j} ⊆ a) := by
    ext a
    simp [T]
  rw [he]
  exact (card_filter_powersetCard_subset {j} univ 2 (subset_univ _) (by simp)).trans (by simp [Nat.choose_one_right])

private theorem card_reserved_style_slots {l : ℕ} (hl : 20 ≤ l) :
    Fintype.card {b : Fin 50 × Fin l // isReservedStyleSlot b} = 100 := by
  let e : {b : Fin 50 × Fin l // isReservedStyleSlot b} ≃ Fin 5 × Fin 20 :=
    { toFun := fun b => (⟨b.val.1,b.prop.1⟩,⟨b.val.2,b.prop.2⟩)
      invFun := fun b => ⟨(Fin.castLE (by decide) b.1,Fin.castLE hl b.2),⟨b.1.isLt,b.2.isLt⟩⟩
      left_inv := by intro b; cases b; rfl
      right_inv := by intro b; cases b; rfl }
  rw [Fintype.card_congr e,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]

private theorem card_unreserved_style_slots {l : ℕ} (hl : 20 ≤ l) :
    Fintype.card {b : Fin 50 × Fin l // ¬ isReservedStyleSlot b} = 50*l - 100 := by
  rw [Fintype.card_subtype_compl,card_reserved_style_slots hl,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_fin]

private theorem card_fiber_of_embedding {A B C : Type*} [Fintype A] [Fintype C]
    [DecidableEq B] (e : A ↪ B × C) (j : B) :
    ((univ : Finset A).filter (fun a => (e a).1 = j)).card ≤ Fintype.card C := by
  rw [←Fintype.card_coe]
  let f (a : ↥((univ : Finset A).filter (fun a => (e a).1 = j))) : C := (e a.val).2
  apply Fintype.card_le_of_injective f
  intro a b h
  apply Subtype.ext
  apply e.injective
  exact Prod.ext ((mem_filter.mp a.prop).2.trans (mem_filter.mp b.prop).2.symm) h

private theorem card_filter_on_prod_left {A B : Type*} [Fintype A] [Fintype B]
    (p : A → Prop) [DecidablePred p] :
    ((univ : Finset (A × B)).filter (fun x => p x.1)).card =
      Fintype.card {a // p a} * Fintype.card B := by
  let f : ↥((univ : Finset (A × B)).filter (fun x => p x.1)) ≃ {a // p a} × B :=
    { toFun := fun x => (⟨x.val.1,(mem_filter.mp x.prop).2⟩,x.val.2)
      invFun := fun x => ⟨(x.1.val,x.2),mem_filter.mpr ⟨mem_univ _,x.1.prop⟩⟩
      left_inv := by rintro ⟨⟨x,y⟩,_⟩; rfl
      right_inv := by rintro ⟨⟨x,_⟩,y⟩; rfl }
  rw [←Fintype.card_coe,Fintype.card_congr f,Fintype.card_prod]

/-- Assign all 100 directional exceptional classes to reserved slots,
and all ordinary classes to disjoint unreserved slots. -/
theorem exists_kuhn_osthus_style_schedule {l q : ℕ}
    (hl : 20 ≤ l) (hq : 100 ≤ q) (hScale : 1226*q ≤ 50*l) :
    ∃ (e : (Bool × Fin 50) ↪ (Fin 50 × Fin l))
      (a : (DoubleStyle × Fin q) ↪ (Fin 50 × Fin l)),
      (∀ k, isReservedStyleSlot (e k) ∧ (e k).1 ≠ k.2) ∧
      (∀ k, ¬ isReservedStyleSlot (a k) ∧ (a k).1 ∉ k.1.val) ∧
      ∀ k j, e k ≠ a j := by
  classical
  let B₀ := {b : Fin 50 × Fin l // isReservedStyleSlot b}
  let B₁ := {b : Fin 50 × Fin l // ¬ isReservedStyleSlot b}
  let X := Bool × Fin 50
  let Y := DoubleStyle × Fin q
  let : Fintype X := inferInstanceAs (Fintype (Bool × Fin 50))
  let : Fintype Y := inferInstanceAs (Fintype (DoubleStyle × Fin q))
  let : Fintype B₀ := inferInstanceAs (Fintype {b : Fin 50 × Fin l // isReservedStyleSlot b})
  let : Fintype B₁ := inferInstanceAs (Fintype {b : Fin 50 × Fin l // ¬ isReservedStyleSlot b})
  have hX : Fintype.card X = 100 := by simp [X]
  have hY : Fintype.card Y = 1225*q := by rw [show Fintype.card Y = Fintype.card (DoubleStyle × Fin q) from rfl,
    Fintype.card_prod,card_double_style,Fintype.card_fin]
  have hB₀ : Fintype.card B₀ = 100 := card_reserved_style_slots hl
  have hB₁ : Fintype.card B₁ = 50*l - 100 := card_unreserved_style_slots hl
  let e₀ : B₀ ↪ Fin 50 × Fin 20 :=
    { toFun := fun x => (x.val.1,⟨x.val.2,x.prop.2⟩)
      inj' := by
        intro a b h
        have h₁ := congrArg (fun v : Fin 50 × Fin 20 => v.1) h
        have h₂ := congrArg (fun v : Fin 50 × Fin 20 => v.2.val) h
        exact Subtype.ext (Prod.ext h₁ (Fin.ext h₂)) }
  have hf₀ (j : Fin 50) : ((univ : Finset B₀).filter (fun b => b.val.1 = j)).card ≤ 20 := by
    have he := card_fiber_of_embedding e₀ j
    rw [Fintype.card_fin] at he
    convert he using 2 <;> (ext b; simp only [mem_filter]; rfl)
  have hf₁ (j : Fin 50) : ((univ : Finset B₁).filter (fun b => b.val.1 = j)).card ≤ l := by
    let e₁ : B₁ ↪ Fin 50 × Fin l := ⟨Subtype.val,Subtype.coe_injective⟩
    have he := card_fiber_of_embedding e₁ j
    rw [Fintype.card_fin] at he
    convert he using 2 <;> (ext b; simp only [mem_filter]; rfl)
  have hBad₀ (j : Fin 50) : ((univ : Finset X).filter (fun k => j ∈ ({k.2} : Finset _))).card ≤ 2 := by
    rw [←Fintype.card_coe]
    let f (k : ↥((univ : Finset X).filter (fun k => j ∈ ({k.2} : Finset _)))) : Bool := k.val.1
    have hf : Function.Injective f := by
      intro a b h
      have hEq (k : ↥((univ : Finset X).filter (fun k => j ∈ ({k.2} : Finset _)))) :
          j = k.val.2 := mem_singleton.mp (mem_filter.mp k.prop).2
      exact Subtype.ext (Prod.ext h ((hEq a).symm.trans (hEq b)))
    exact (Fintype.card_le_of_injective f hf).trans_eq (by decide)
  have hBad₁ (j : Fin 50) : ((univ : Finset Y).filter (fun k => j ∈ k.1.val)).card ≤ 49*q := by
    have he := card_filter_on_prod_left (B := Fin q) (fun k : DoubleStyle => j ∈ k.val)
    rw [card_double_styles_containing,Fintype.card_fin] at he
    exact he.le
  obtain ⟨fe,hfe,he⟩ := exists_style_assignment_from_multiplicities
    (p := 1) (t := 20) (u := 2) (fun k : X => {k.2}) (fun b : B₀ => b.val.1)
    (by omega) (fun _ => by simp) hf₀ hBad₀ (by omega) (by omega)
  obtain ⟨fa,hfa,ha⟩ := exists_style_assignment_from_multiplicities
    (p := 2) (t := l) (u := 49*q) (fun k : Y => k.1.val) (fun b : B₁ => b.val.1)
    (by omega) (fun k => (mem_powersetCard.mp k.1.prop).2.le) hf₁ hBad₁
    (by omega) (by omega)
  refine ⟨⟨fun k => (fe k).val,Subtype.coe_injective.comp hfe⟩,
    ⟨fun k => (fa k).val,Subtype.coe_injective.comp hfa⟩,?_,?_,?_⟩
  · exact fun k => ⟨(fe k).prop,fun h => he k (mem_singleton.mpr h)⟩
  · exact fun k => ⟨(fa k).prop,ha k⟩
  · intro k j h
    change (fe k).val = (fa j).val at h
    exact (fa j).prop (h ▸ (fe k).prop)

end OverfullWork.DirectedRobustExpansion
