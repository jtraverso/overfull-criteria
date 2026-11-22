module

public import OverfullWork.KuhnOsthusAugmentedChordBalance
public import OverfullWork.KuhnOsthusRealizedPathSystems
public import OverfullWork.KuhnOsthusLocalBalance

@[expose] public section


/-! Transfer the multiplicity identity of Lemma 9.5 to physical
arcs and to the cardinalities of the free successor pairs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedDemandHall
open scoped Classical
variable {V J I : Type*} [Fintype V] [Fintype J]

/-- Count a realized walk at its coarse labels through the exact
counts of the fine successor pairs. -/
theorem arc_loads_from_walk_realization (D : Digraph V) (rank : V → J)
    (next : J → J) (coarse : J → I) (load : J → ℕ)
    (hStep : ∀ x y, D.Adj x y → rank y = next (rank x))
    (hCount : ∀ j, Fintype.card (Arc (⟨fun x y => D.Adj x y ∧ rank x = j⟩ : Digraph V)) = load j) :
    (∀ c, (∑ e : Arc D, if coarse (rank e.val.1) = c then (1:ℕ) else 0) =
      ∑ j, if coarse j = c then load j else 0) ∧
    ∀ c, (∑ e : Arc D, if coarse (rank e.val.2) = c then (1:ℕ) else 0) =
      ∑ j, if coarse (next j) = c then load j else 0 := by
  let K (j : J) := Arc (⟨fun x y => D.Adj x y ∧ rank x = j⟩ : Digraph V)
  let eqv : Arc D ≃ (Σ j, K j) :=
    ⟨fun e => ⟨rank e.val.1,⟨e.val,e.prop,rfl⟩⟩,
      fun e => ⟨e.2.val,e.2.prop.1⟩,fun _ => rfl,by
        rintro ⟨j,⟨⟨x,y⟩,he,hj⟩⟩
        subst j
        rfl⟩
  have hSum (p : J → Prop) :
      (∑ e : Arc D, if p (rank e.val.1) then (1:ℕ) else 0) =
        ∑ j, if p j then load j else 0 := by
    have hE : (∑ e : Arc D, if p (rank e.val.1) then (1:ℕ) else 0) =
        ∑ e : (Σ j, K j), if p e.1 then (1:ℕ) else 0 :=
      Fintype.sum_equiv eqv _ _ (fun _ => rfl)
    rw [hE,Fintype.sum_sigma]
    apply sum_congr rfl
    intro j _
    by_cases h : p j <;> simp [h, hCount j, K]
  refine ⟨fun c => hSum (fun j => coarse j = c),fun c => ?_⟩
  calc
    _ = (∑ e : Arc D, if coarse (next (rank e.val.1)) = c then (1:ℕ) else 0) := by
      apply sum_congr rfl
      intro e _
      rw [hStep _ _ e.prop]
    _ = _ := hSum (fun j => coarse (next j) = c)

private theorem card_occupied_endpoints {A : Type*} [Fintype A] (f : A → V)
    (hf : Function.Injective f) (p : V → Prop) :
    (finiteSatisfying (fun v => p v ∧ ∃ a, f a = v)).card =
      ∑ a, if p (f a) then (1:ℕ) else 0 := by
  rw [← card_filter]
  symm
  apply card_bij (fun a _ => f a)
  · intro a ha
    exact mem_finiteSatisfying.mpr ⟨(mem_filter.mp ha).2,a,rfl⟩
  · intro a _ b _ hab
    exact hf hab
  · intro v hv
    obtain ⟨hp,a,rfl⟩ :=
      (mem_finiteSatisfying (p := fun v => p v ∧ ∃ a, f a = v)).mp hv
    exact ⟨a,mem_filter.mpr ⟨mem_univ _,hp⟩,rfl⟩

omit [Fintype J] in
/-- Arc sums of a path system count the occupied source and target
vertices, with respect to any predicate on the vertices. -/
theorem path_arc_endpoint_counts (D : Digraph V) (hD : IsDirectedPathSystem D) (p : V → Prop) :
    (∑ a : Arc D, if p a.val.1 then (1:ℕ) else 0) =
      (finiteSatisfying (fun v => p v ∧ ∃ w, D.Adj v w)).card ∧
    (∑ a : Arc D, if p a.val.2 then (1:ℕ) else 0) =
      (finiteSatisfying (fun v => p v ∧ ∃ w, D.Adj w v)).card := by
  have hs : Function.Injective (fun e : Arc D => e.val.1) := by
    intro a b h
    change a.val.1 = b.val.1 at h
    have hb : D.Adj a.val.1 b.val.2 := by rw [h]; exact b.prop
    exact Subtype.ext (Prod.ext h (hD.out_unique a.prop hb))
  have ht : Function.Injective (fun e : Arc D => e.val.2) := by
    intro a b h
    change a.val.2 = b.val.2 at h
    have hb : D.Adj b.val.1 a.val.2 := by rw [h]; exact b.prop
    exact Subtype.ext (Prod.ext (hD.in_unique a.prop hb) h)
  have hOut : finiteSatisfying (fun v => p v ∧ ∃ e : Arc D, e.val.1 = v) =
      finiteSatisfying (fun v => p v ∧ ∃ w, D.Adj v w) := by
    ext v
    simp only [mem_finiteSatisfying]
    exact and_congr_right fun _ => ⟨fun ⟨e,he⟩ => ⟨e.val.2,he ▸ e.prop⟩,
      fun ⟨w,hw⟩ => ⟨⟨(v,w),hw⟩,rfl⟩⟩
  have hIn : finiteSatisfying (fun v => p v ∧ ∃ e : Arc D, e.val.2 = v) =
      finiteSatisfying (fun v => p v ∧ ∃ w, D.Adj w v) := by
    ext v
    simp only [mem_finiteSatisfying]
    exact and_congr_right fun _ => ⟨fun ⟨e,he⟩ => ⟨e.val.1,he ▸ e.prop⟩,
      fun ⟨w,hw⟩ => ⟨⟨(w,v),hw⟩,rfl⟩⟩
  exact ⟨(card_occupied_endpoints _ hs p).symm.trans (congrArg Finset.card hOut),
    (card_occupied_endpoints _ ht p).symm.trans (congrArg Finset.card hIn)⟩

omit [Fintype J] in
/-- For a path system each counted arc occupies one source and one
target. Equal coarse counts therefore give the balanced free pairs
needed for the final Hamilton completion. -/
theorem free_successor_slots_of_balanced_arc_counts (D : Digraph V) (cluster : V → I)
    (s : Equiv.Perm I) (hD : IsDirectedPathSystem D)
    (hSize : ∀ i, (finiteSatisfying (fun x => cluster x = i)).card =
      (finiteSatisfying (fun x => cluster x = s i)).card)
    (hCount : ∀ i, (∑ e : Arc D, if cluster e.val.1 = i then (1:ℕ) else 0) =
      ∑ e : Arc D, if cluster e.val.2 = s i then (1:ℕ) else 0) :
    ∀ i, (freeOut D cluster i).card = (freeIn D cluster (s i)).card := by
  have hs : Function.Injective (fun e : Arc D => e.val.1) := by
    intro a b he
    change a.val.1 = b.val.1 at he
    have hb : D.Adj a.val.1 b.val.2 := by rw [he]; exact b.prop
    exact Subtype.ext (Prod.ext he (hD.out_unique a.prop hb))
  have ht : Function.Injective (fun e : Arc D => e.val.2) := by
    intro a b he
    change a.val.2 = b.val.2 at he
    have hb : D.Adj b.val.1 a.val.2 := by rw [he]; exact b.prop
    exact Subtype.ext (Prod.ext (hD.in_unique a.prop hb) he)
  intro i
  have hDep (v : V) : (∃ e : Arc D, e.val.1 = v) ↔ ∃ x, D.Adj v x :=
    ⟨fun ⟨e,he⟩ => ⟨e.val.2,he ▸ e.prop⟩,fun ⟨x,hx⟩ => ⟨⟨(v,x),hx⟩,rfl⟩⟩
  have hArr (v : V) : (∃ e : Arc D, e.val.2 = v) ↔ ∃ x, D.Adj x v :=
    ⟨fun ⟨e,he⟩ => ⟨e.val.1,he ▸ e.prop⟩,fun ⟨x,hx⟩ => ⟨⟨(x,v),hx⟩,rfl⟩⟩
  have hSO := card_occupied_endpoints (fun e : Arc D => e.val.1) hs (fun v => cluster v = i)
  have hSI := card_occupied_endpoints (fun e : Arc D => e.val.2) ht (fun v => cluster v = s i)
  have hCo := card_filter_add_card_filter_not (s := finiteSatisfying (fun x => cluster x = i))
    (fun x => ∃ y, D.Adj x y)
  have hCi := card_filter_add_card_filter_not (s := finiteSatisfying (fun x => cluster x = s i))
    (fun x => ∃ y, D.Adj y x)
  have hOut : (finiteSatisfying (fun v => cluster v = i ∧ ∃ e : Arc D, e.val.1 = v)) =
      (finiteSatisfying (fun x => cluster x = i)).filter (fun x => ∃ y, D.Adj x y) := by
    ext x
    simp [hDep]
  have hIn : (finiteSatisfying (fun v => cluster v = s i ∧ ∃ e : Arc D, e.val.2 = v)) =
      (finiteSatisfying (fun x => cluster x = s i)).filter (fun x => ∃ y, D.Adj y x) := by
    ext x
    simp [hArr]
  rw [hOut] at hSO
  rw [hIn] at hSI
  have hFO : (finiteSatisfying (fun x => cluster x = i)).filter (fun x => ¬ ∃ y, D.Adj x y) =
      freeOut D cluster i := by ext x; simp [mem_freeOut]
  have hFI : (finiteSatisfying (fun x => cluster x = s i)).filter (fun x => ¬ ∃ y, D.Adj y x) =
      freeIn D cluster (s i) := by ext x; simp [mem_freeIn]
  rw [hSO,hFO] at hCo
  rw [hSI,hFI] at hCi
  have hp := hSize i
  have hq := hCount i
  omega

omit [Fintype J] in
private theorem arc_weight_disjoint_union (D C : Digraph V) (f : V × V → ℕ)
    (hDis : ∀ x y, D.Adj x y → ¬ C.Adj x y) :
    (∑ e : Arc (D ⊔ C), f e.val) = (∑ e : Arc D, f e.val) + (∑ e : Arc C, f e.val) := by
  let g : Arc D ⊕ Arc C → Arc (D ⊔ C) :=
    Sum.elim (fun a => ⟨a.val,Or.inl a.prop⟩) (fun a => ⟨a.val,Or.inr a.prop⟩)
  have hG : Function.Bijective g := by
    constructor
    · intro a b he
      have hv := congrArg Subtype.val he
      cases a with
      | inl x =>
        cases b with
        | inl y => exact congrArg Sum.inl (Subtype.ext hv)
        | inr y => exact (hDis x.val.1 x.val.2 x.prop (hv.symm ▸ y.prop)).elim
      | inr x =>
        cases b with
        | inl y => exact (hDis y.val.1 y.val.2 y.prop (hv ▸ x.prop)).elim
        | inr y => exact congrArg Sum.inr (Subtype.ext hv)
    · rintro ⟨e,he | he⟩
      · exact ⟨Sum.inl ⟨e,he⟩,rfl⟩
      · exact ⟨Sum.inr ⟨e,he⟩,rfl⟩
  let equiv := Equiv.ofBijective g hG
  have h := Fintype.sum_equiv equiv (fun e => f (g e).val) (fun a => f a.val) (fun _ => rfl)
  rw [←h,Fintype.sum_sum_type]
  rfl

/-- Combine the exact fine loads with the balance identity for the
original arcs and the exceptional paths. This constructs the
equal-size free successor pairs for Claim 5. -/
theorem free_successor_pairs_after_realized_chords (D H C : Digraph V)
    (rank : V → J) (next : J → J) (coarse : J → I) (s : Equiv.Perm I) (load : J → ℕ)
    (hStep : ∀ x y, D.Adj x y → rank y = next (rank x))
    (hCount : ∀ j, Fintype.card (Arc (⟨fun x y => D.Adj x y ∧ rank x = j⟩ : Digraph V)) = load j)
    (hApart : ∀ x y, D.Adj x y → ¬ (H ⊔ C).Adj x y)
    (hHC : ∀ x y, H.Adj x y → ¬ C.Adj x y)
    (hPath : IsDirectedPathSystem (D ⊔ (H ⊔ C)))
    (hSize : ∀ i, (finiteSatisfying (fun x => coarse (rank x) = i)).card =
      (finiteSatisfying (fun x => coarse (rank x) = s i)).card)
    (hBalance : ∀ i,
      (∑ j, if coarse j = i then load j else 0) +
        (∑ a : Arc H, if coarse (rank a.val.1) = i then (1:ℕ) else 0) =
      (∑ j, if coarse (next j) = s i then load j else 0) +
        (∑ a : Arc H, if coarse (rank a.val.2) = s i then (1:ℕ) else 0))
    (hBalanceC : ∀ i,
      (∑ a : Arc C, if coarse (rank a.val.1) = i then (1:ℕ) else 0) =
      (∑ a : Arc C, if coarse (rank a.val.2) = s i then (1:ℕ) else 0)) :
    ∀ i, (freeOut (D ⊔ (H ⊔ C)) (coarse ∘ rank) i).card =
      (freeIn (D ⊔ (H ⊔ C)) (coarse ∘ rank) (s i)).card := by
  apply free_successor_slots_of_balanced_arc_counts _ _ s hPath hSize
  intro i
  let f (e : V × V) := if coarse (rank e.1) = i then (1:ℕ) else 0
  let g (e : V × V) := if coarse (rank e.2) = s i then (1:ℕ) else 0
  change (∑ a : Arc (D ⊔ (H ⊔ C)), f a.val) = ∑ a : Arc (D ⊔ (H ⊔ C)), g a.val
  rw [arc_weight_disjoint_union D (H ⊔ C) f hApart,arc_weight_disjoint_union D (H ⊔ C) g hApart,
    arc_weight_disjoint_union H C f hHC,arc_weight_disjoint_union H C g hHC]
  obtain ⟨hOut,hIn⟩ := arc_loads_from_walk_realization D rank next coarse load hStep hCount
  simp only [f,g,hOut,hIn,hBalanceC]
  have h := hBalance i
  omega

end OverfullWork.DirectedRobustExpansion
