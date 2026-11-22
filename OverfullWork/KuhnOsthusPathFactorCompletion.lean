module

public import OverfullWork.KuhnOsthusLocalBalance
public import Mathlib.Combinatorics.Hall.Finite

@[expose] public section


/-! In Kühn–Osthus Lemma 8.3 the unused source and target sets
of consecutive clusters are balanced. Hall matchings on the reserved
pairs then complete the corrected system to a 1-factor. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V I : Type*} [Fintype V]

/-- A sparse pair with both minimum degrees at least the rectangle
threshold has a perfect matching when it hits every large rectangle. -/
theorem exists_matching_of_rectangle_threshold {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (r : ℕ) (hSize : Fintype.card A = Fintype.card B)
    (hOut : ∀ a, r ≤ (univ.filter (R a)).card)
    (hIn : ∀ b, r ≤ (univ.filter (fun a => R a b)).card)
    (hRect : ∀ S : Finset A, ∀ T : Finset B, r ≤ S.card → r ≤ T.card →
      ∃ a ∈ S, ∃ b ∈ T, R a b) :
    ∃ f : A ≃ B, ∀ a, R a (f a) := by
  classical
  let N (a : A) := univ.filter (R a)
  have hHall (S : Finset A) : S.card ≤ (S.biUnion N).card := by
    by_contra! h
    obtain ⟨a,ha⟩ := card_pos.mp (show 0 < S.card by omega)
    have hNa : N a ⊆ S.biUnion N := fun b hb => mem_biUnion.mpr ⟨a,ha,hb⟩
    have hLargeS := (hOut a).trans (card_le_card hNa)
    let T := univ \ S.biUnion N
    have hT : T.card = Fintype.card B - (S.biUnion N).card := by
      rw [←card_univ,←card_sdiff_of_subset (subset_univ (S.biUnion N))]
    have hS : S.card ≤ Fintype.card A := card_le_univ _
    obtain ⟨b,hb⟩ := card_pos.mp (show 0 < T.card by omega)
    have hNb : (univ.filter (fun a => R a b)) ⊆ univ \ S := by
      intro x hx
      refine mem_sdiff.mpr ⟨mem_univ _,fun hSx => ?_⟩
      exact (mem_sdiff.mp hb).2 (mem_biUnion.mpr ⟨x,hSx,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩⟩)
    have hLargeT := (hIn b).trans (card_le_card hNb)
    rw [card_sdiff_of_subset (subset_univ S),card_univ] at hLargeT
    obtain ⟨x,hx,y,hy,hxy⟩ := hRect S T (by omega) (by omega)
    exact (mem_sdiff.mp hy).2 (mem_biUnion.mpr ⟨x,hx,mem_filter.mpr ⟨mem_univ _,hxy⟩⟩)
  obtain ⟨f,hf,hN⟩ := (all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hSize⟩),
    fun a => (mem_filter.mp (hN a)).2⟩

/-- Insert a matching for each successor pair. Every old arc is
preserved and the new arcs use precisely the free slots. -/
theorem exists_factor_completion_of_successor_matchings (D R : Digraph V)
    (cluster : V → I) (s : Equiv.Perm I) (hD : IsDirectedPathSystem D)
    (hMatch : ∀ i, ∃ f : freeOut D cluster i ≃ freeIn D cluster (s i),
      ∀ x : freeOut D cluster i, R.Adj x (f x)) :
    ∃ σ : Equiv.Perm V,
      (∀ x y, D.Adj x y → σ x = y) ∧
      (∀ x, ((∃ y, D.Adj x y) ∨
        (R.Adj x (σ x) ∧ cluster (σ x) = s (cluster x)))) ∧
      ∀ x, (¬ ∃ y, D.Adj x y) ↔ ¬ D.Adj x (σ x) := by
  classical
  choose f hR using hMatch
  let T (x y : V) : Prop :=
    ∃ i, ∃ a : freeOut D cluster i, a.val = x ∧ (f i a).val = y
  have hInfo {x y : V} (h : T x y) :
      (¬ ∃ z, D.Adj x z) ∧ (¬ ∃ z, D.Adj z y) ∧ R.Adj x y ∧ cluster y = s (cluster x) := by
    obtain ⟨i,a,rfl,rfl⟩ := h
    have ha := (mem_filter.mp a.prop).2
    have hb := (mem_filter.mp (f i a).prop).2
    exact ⟨ha.2,hb.2,hR i a,hb.1.trans (congrArg s ha.1.symm)⟩
  have hOut (x : V) : ∃! y, D.Adj x y ∨ T x y := by
    have hUnique (y z : V) (hy : D.Adj x y ∨ T x y) (hz : D.Adj x z ∨ T x z) : y = z := by
      rcases hy with hy | hy <;> rcases hz with hz | hz
      · exact hD.out_unique hy hz
      · exact ((hInfo hz).1 ⟨y,hy⟩).elim
      · exact ((hInfo hy).1 ⟨z,hz⟩).elim
      · obtain ⟨i,a,rfl,rfl⟩ := hy
        obtain ⟨j,b,hb,rfl⟩ := hz
        have hi : i = j := ((mem_filter.mp a.prop).2.1).symm.trans
          (hb ▸ (mem_filter.mp b.prop).2.1)
        subst j
        have he : b = a := Subtype.ext hb
        rw [he]
    by_cases hx : ∃ y, D.Adj x y
    · obtain ⟨y,hy⟩ := hx
      exact ⟨y,Or.inl hy,fun z hz => hUnique z y hz (Or.inl hy)⟩
    · let a : freeOut D cluster (cluster x) := ⟨x,mem_filter.mpr ⟨mem_univ _,rfl,hx⟩⟩
      let y := (f (cluster x) a).val
      have hy : D.Adj x y ∨ T x y := Or.inr ⟨cluster x,a,rfl,rfl⟩
      exact ⟨y,hy,fun z hz => hUnique z y hz hy⟩
  have hIn (y : V) : ∃! x, D.Adj x y ∨ T x y := by
    have hUnique (x z : V) (hx : D.Adj x y ∨ T x y) (hz : D.Adj z y ∨ T z y) : x = z := by
      rcases hx with hx | hx <;> rcases hz with hz | hz
      · exact hD.in_unique hx hz
      · exact ((hInfo hz).2.1 ⟨x,hx⟩).elim
      · exact ((hInfo hx).2.1 ⟨z,hz⟩).elim
      · obtain ⟨i,a,rfl,ha⟩ := hx
        obtain ⟨j,b,rfl,hb⟩ := hz
        have hi : s i = s j := ((mem_filter.mp (f i a).prop).2.1).symm.trans
          (show cluster (f i a).val = s j by rw [ha,←hb]; exact (mem_filter.mp (f j b).prop).2.1)
        have he := s.injective hi
        subst j
        have hab : f i a = f i b := Subtype.ext (ha.trans hb.symm)
        rw [(f i).injective hab]
    by_cases hy : ∃ x, D.Adj x y
    · obtain ⟨x,hx⟩ := hy
      exact ⟨x,Or.inl hx,fun z hz => hUnique z x hz (Or.inl hx)⟩
    · let i := s.symm (cluster y)
      let b : freeIn D cluster (s i) :=
        ⟨y,mem_filter.mpr ⟨mem_univ _,(s.apply_symm_apply _).symm,hy⟩⟩
      let a := (f i).symm b
      have hx : D.Adj a y ∨ T a y :=
        Or.inr ⟨i,a,rfl,congrArg (fun z : freeIn D cluster (s i) => z.val) ((f i).apply_symm_apply b)⟩
      exact ⟨a,hx,fun z hz => hUnique z a hz hx⟩
  choose g hg hUnique using hOut
  have hinj : Function.Injective g := by
    intro x z he
    obtain ⟨w,_,hw⟩ := hIn (g z)
    exact (hw x (he ▸ hg x)).trans (hw z (hg z)).symm
  let σ := Equiv.ofBijective g ⟨hinj,Finite.surjective_of_injective hinj⟩
  have hPreserve (x y : V) (h : D.Adj x y) : σ x = y := (hUnique x y (Or.inl h)).symm
  refine ⟨σ,hPreserve,?_,?_⟩
  · intro x

    rcases hg x with hd | ht
    · exact Or.inl ⟨σ x,hd⟩
    · have hi := hInfo ht
      exact Or.inr ⟨hi.2.2.1,hi.2.2.2⟩
  · intro x
    exact ⟨fun h hd => h ⟨_,hd⟩,fun h ⟨y,hy⟩ => h ((hPreserve x y hy).symm ▸ hy)⟩

/-- In an acyclic partial system, every orbit of a completing permutation
contains a source whose outgoing edge was supplied by the completion. -/
theorem every_completed_orbit_uses_a_free_source (D : Digraph V)
    (hD : NoDirectedCycle D) (σ : Equiv.Perm V)
    (hPreserve : ∀ x y, D.Adj x y → σ x = y) (x : V) :
    ∃ y, σ.SameCycle x y ∧ ¬ ∃ z, D.Adj y z := by
  by_contra! h
  have hEdge (m : ℕ) : D.Adj ((σ^m) x) ((σ^(m+1)) x) := by
    have horb : σ.SameCycle x ((σ^m) x) := Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl σ x)
    obtain ⟨y,hy⟩ := h ((σ^m) x) horb
    rw [pow_succ',Equiv.Perm.mul_apply,hPreserve _ _ hy]
    exact hy
  have hPath (n : ℕ) : Relation.TransGen D.Adj x ((σ^(n+1)) x) := by
    induction n with
    | zero => exact .single (by simpa only [pow_zero,Equiv.Perm.one_apply] using hEdge 0)
    | succ n hn => exact hn.tail (hEdge (n+1))
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (orderOf_pos σ))
  have hc := hPath n
  change Relation.TransGen D.Adj x ((σ^(n.succ)) x) at hc
  rw [←hn,pow_orderOf_eq_one,Equiv.Perm.one_apply] at hc
  exact hD x hc

/-- Combine the chord balance identity with Hall on the successor
pairs. The rectangle and degree bounds concern only the free slots. -/
theorem exists_factor_completion_of_chord_lists {E : Type*} [Fintype E] (k : E → ℕ)
    (D R : Digraph V) (cluster : V → I) (s : Equiv.Perm I) (r : I → ℕ)
    (src dst : (Σ e, Fin (k e + 1)) → V)
    (hD : IsDirectedPathSystem D)
    (hArcs : ∀ x y, D.Adj x y ↔ ∃ e, src e = x ∧ dst e = y)
    (hSrc : Function.Injective src) (hDst : Function.Injective dst)
    (hStep : ∀ e (j : Fin (k e + 1)),
       cluster (dst ⟨e,j⟩) = s (cluster (src ⟨e,finRotate (k e+1) j⟩)))
    (hSize : ∀ i, (univ.filter (fun x => cluster x = i)).card =
      (univ.filter (fun x => cluster x = s i)).card)
    (hOut : ∀ i (a : freeOut D cluster i), r i ≤
      (univ.filter (fun b : freeIn D cluster (s i) => R.Adj a b)).card)
    (hIn : ∀ i (b : freeIn D cluster (s i)), r i ≤
      (univ.filter (fun a : freeOut D cluster i => R.Adj a b)).card)
    (hRect : ∀ i (S : Finset (freeOut D cluster i)) (T : Finset (freeIn D cluster (s i))),
      r i ≤ S.card → r i ≤ T.card → ∃ a ∈ S, ∃ b ∈ T, R.Adj a b) :
    ∃ σ : Equiv.Perm V,
      (∀ x y, D.Adj x y → σ x = y) ∧
      (∀ x, (∃ y, D.Adj x y) ∨ (R.Adj x (σ x) ∧ cluster (σ x) = s (cluster x))) ∧
      ∀ x, ∃ y, σ.SameCycle x y ∧ ¬ ∃ z, D.Adj y z := by
  have hBalance :=
    locally_balanced_of_chord_lists k D cluster s src dst hArcs hSrc hDst hStep hSize
  have hMatch (i : I) : ∃ f : freeOut D cluster i ≃ freeIn D cluster (s i),
      ∀ x : freeOut D cluster i, R.Adj x (f x) := by
    apply exists_matching_of_rectangle_threshold (fun a : freeOut D cluster i =>
      fun b : freeIn D cluster (s i) => R.Adj a b) (r i)
    · simpa only [Fintype.card_coe] using hBalance i
    · exact hOut i
    · exact hIn i
    · exact hRect i
  obtain ⟨σ,hs,hNew,_⟩ := exists_factor_completion_of_successor_matchings D R cluster s hD hMatch
  exact ⟨σ,hs,hNew,every_completed_orbit_uses_a_free_source D hD.acyclic σ hs⟩

end OverfullWork.DirectedRobustExpansion
