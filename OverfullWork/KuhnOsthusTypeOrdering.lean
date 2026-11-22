module

public import OverfullWork.DirectedRobustExpansion
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Perm

@[expose] public section


/-! An elementary packing argument for the near-complete auxiliary graph
in Kühn–Osthus Lemma 8.7. A swap removes a bad pair while keeping
all the previously good pairs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {I J : Type*} [Fintype I] [Fintype J]

private noncomputable def related (r : I → I → Prop) (x : I) : Finset I :=
  univ.filter (r x)

private theorem mem_related (r : I → I → Prop) (x y : I) :
    y ∈ related r x ↔ r x y := by simp [related]

/-- A bijection can separate two symmetric relations if their
maximum neighborhood sizes leave room for a correcting swap. -/
theorem exists_disjoint_ordering_of_sparse_relations (r : I → I → Prop) (s : J → J → Prop)
    (hr : ∀ {x y}, r x y → r y x) (hs : ∀ {x y}, s x y → s y x)
    (hLoop : ∀ x, ¬ r x x)
    (e₀ : I ≃ J) (a b : ℕ)
    (hR : ∀ x, ((univ : Finset I).filter (r x)).card ≤ a)
    (hS : ∀ x, ((univ : Finset J).filter (s x)).card ≤ b)
    (hSize : 2*a*b+a+1 < Fintype.card I) :
    ∃ e : I ≃ J, ∀ x y, r x y → ¬ s (e x) (e y) := by
  let bad (e : I ≃ J) := (univ : Finset (I × I)).filter (fun p => r p.1 p.2 ∧ s (e p.1) (e p.2))
  let P := (univ : Finset (Equiv.Perm I))
  obtain ⟨p,_,hp⟩ := exists_min_image P (fun p => (bad (p.trans e₀)).card)
    (show P.Nonempty from ⟨Equiv.refl I,mem_univ _⟩)
  let e := p.trans e₀
  refine ⟨e,?_⟩
  intro x y hxy hexy
  let A := related r x
  let B := related (fun u v => s (e u) (e v)) x
  let F := A.biUnion (related (fun u v => s (e u) (e v)))
  let G := B.biUnion (related r)
  let X := insert x (A ∪ F ∪ G)
  have hA : A.card ≤ a := hR x
  have hPull (v : I) : (related (fun u v => s (e u) (e v)) v).card ≤ b := by
    apply le_trans _ (hS (e v))
    apply card_le_card_of_injOn e
    · intro j hj
      exact mem_filter.mpr ⟨mem_univ _,(mem_related (fun u w => s (e u) (e w)) v j).mp hj⟩
    · exact e.injective.injOn
  have hB : B.card ≤ b := hPull x
  have hUnion {T : Finset I} (f : I → Finset I) (c : ℕ)
      (hf : ∀ i, (f i).card ≤ c) : (T.biUnion f).card ≤ T.card*c :=
    card_biUnion_le.trans (by simpa using sum_le_sum (s := T) (fun i _ => hf i))
  have hF : F.card ≤ a*b := (hUnion _ b hPull).trans (Nat.mul_le_mul_right _ hA)
  have hG : G.card ≤ a*b := (hUnion _ a hR).trans (by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right a hB)
  have hX : X.card ≤ 2*a*b+a+1 := by
    have h₁ := card_union_le A F
    have h₂ := card_union_le (A ∪ F) G
    have h₃ := card_insert_le (s := A ∪ F ∪ G) x
    change X.card ≤ (A ∪ F ∪ G).card+1 at h₃
    rw [Nat.mul_assoc,two_mul]
    omega
  have hNot : X ≠ univ := by
    intro h
    rw [h,card_univ] at hX
    omega
  obtain ⟨z,hz⟩ : ∃ z, z ∉ X := by
    by_contra! h
    exact hNot (eq_univ_iff_forall.mpr h)
  have hzx : z ≠ x := fun h => hz (h ▸ mem_insert_self _ _)
  have hzA : z ∉ A := fun h => hz (mem_insert_of_mem (mem_union_left _ (mem_union_left _ h)))
  have hzF : z ∉ F := fun h => hz (mem_insert_of_mem (mem_union_left _ (mem_union_right _ h)))
  have hzG : z ∉ G := fun h => hz (mem_insert_of_mem (mem_union_right _ h))
  let t := Equiv.swap x z
  let p' := t.trans p
  let e' := p'.trans e₀
  have hSwap (i : I) : e' i = e (t i) := rfl
  have hxz : ¬ r x z := fun h => hzA ((mem_related _ _ _).mpr h)
  have hSpare (v : I) (hvx : v ≠ x) (hvz : v ≠ z) : e' v = e v := by
    rw [hSwap]
    exact congrArg e (Equiv.swap_apply_of_ne_of_ne hvx hvz)
  have hxGood (v : I) (h : r x v) : ¬ s (e' x) (e' v) := by
    have hvx : v ≠ x := fun h' => hLoop x (h' ▸ h)
    have hvz : v ≠ z := fun h' => hxz (h' ▸ h)
    rw [hSwap x,show t x = z from Equiv.swap_apply_left _ _,hSpare v hvx hvz]
    intro h'
    exact hzF (mem_biUnion.mpr ⟨v,(mem_related _ _ _).mpr h,(mem_related _ _ _).mpr (hs h')⟩)
  have hzGood (v : I) (h : r z v) : ¬ s (e' z) (e' v) := by
    have hvx : v ≠ x := fun h' => hxz (hr (h' ▸ h))
    have hvz : v ≠ z := fun h' => hLoop z (h' ▸ h)
    rw [hSwap z,show t z = x from Equiv.swap_apply_right _ _,hSpare v hvx hvz]
    intro h'
    exact hzG (mem_biUnion.mpr ⟨v,(mem_related _ _ _).mpr h',(mem_related _ _ _).mpr (hr h)⟩)
  have hSub : bad e' ⊆ bad e := by
    rintro ⟨u,v⟩ hm
    obtain ⟨huv,hBad⟩ := (mem_filter.mp hm).2
    have hux : u ≠ x := fun h => (hxGood v (h ▸ huv)) (h ▸ hBad)
    have huz : u ≠ z := fun h => (hzGood v (h ▸ huv)) (h ▸ hBad)
    have hvx : v ≠ x := fun h => (hxGood u (h ▸ hr huv)) (h ▸ hs hBad)
    have hvz : v ≠ z := fun h => (hzGood u (h ▸ hr huv)) (h ▸ hs hBad)
    rw [hSpare u hux huz,hSpare v hvx hvz] at hBad
    exact mem_filter.mpr ⟨mem_univ _,huv,hBad⟩
  have hNe : bad e' ≠ bad e := by
    intro he
    have hm : (x,y) ∈ bad e := mem_filter.mpr ⟨mem_univ _,hxy,hexy⟩
    rw [←he] at hm
    exact hxGood y hxy (mem_filter.mp hm).2.2
  exact (not_le_of_gt (card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSub,hNe⟩)))
    (hp p' (mem_univ _))

end OverfullWork.DirectedRobustExpansion
