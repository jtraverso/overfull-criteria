module

public import OverfullWork.KuhnOsthusLocalBalance

@[expose] public section


/-! The greedy matching selection in Kühn–Osthus Lemma 8.3.
A candidate matching for each request loses at most the occupied
endpoints in its two clusters. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V I J : Type*} [Fintype J]

/-- Realize requested chords by mutually vertex-disjoint arcs.
The total endpoint load in a cluster counts source and target requests
with multiplicities, as in (8.2). -/
theorem exists_disjoint_chord_realization (cluster : V → I) (source target : J → I)
    (M : J → Finset (V × V)) (load : I → ℕ)
    (hCells : ∀ j e, e ∈ M j → cluster e.1 = source j ∧ cluster e.2 = target j)
    (hDistinct : ∀ j e, e ∈ M j → e.1 ≠ e.2)
    (hMatching : ∀ j, Set.InjOn Prod.fst (↑(M j) : Set (V × V)) ∧
      Set.InjOn Prod.snd (↑(M j) : Set (V × V)))
    (hLoad : ∀ i, (univ.filter (fun j => source j = i)).card +
      (univ.filter (fun j => target j = i)).card ≤ load i)
    (hRoom : ∀ j, load (source j) + load (target j) < (M j).card) :
    ∃ f : J → V × V, (∀ j, f j ∈ M j ∧ (f j).1 ≠ (f j).2) ∧
      ∀ j k, j ≠ k →
        (f j).1 ≠ (f k).1 ∧ (f j).1 ≠ (f k).2 ∧
        (f j).2 ≠ (f k).1 ∧ (f j).2 ≠ (f k).2 := by
  classical
  have chooseOn (P : Finset J) : ∃ f : P → V × V, (∀ j, f j ∈ M j.val) ∧
      ∀ j k, j ≠ k →
        (f j).1 ≠ (f k).1 ∧ (f j).1 ≠ (f k).2 ∧
        (f j).2 ≠ (f k).1 ∧ (f j).2 ≠ (f k).2 := by
    induction P using Finset.induction_on with
    | empty =>
      exact ⟨fun j => (notMem_empty _ j.prop).elim,
        fun j => (notMem_empty _ j.prop).elim,fun j => (notMem_empty _ j.prop).elim⟩
    | @insert j P hj ih =>
      obtain ⟨f,hf,hDis⟩ := ih
      let Used (i : I) :=
        ((univ : Finset P).filter (fun u => source u.val = i)).image (fun u => (f u).1) ∪
        ((univ : Finset P).filter (fun u => target u.val = i)).image (fun u => (f u).2)
      have hUsed (i : I) : (Used i).card ≤ load i := by
        refine (card_union_le _ _).trans ((Nat.add_le_add card_image_le card_image_le).trans ?_)
        have hCut (p : J → I) : ((univ : Finset P).filter (fun u => p u.val = i)).card ≤
            (univ.filter (fun u => p u = i)).card := by
          apply card_le_card_of_injOn Subtype.val
          · intro u hu
            exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩
          · exact Subtype.coe_injective.injOn
        exact (Nat.add_le_add (hCut source) (hCut target)).trans (hLoad i)
      let X := (M j).filter (fun e => e.1 ∈ Used (source j))
      let Y := (M j).filter (fun e => e.2 ∈ Used (target j))
      have hX : X.card ≤ load (source j) := by
        apply Nat.le_trans _ (hUsed (source j))
        apply card_le_card_of_injOn Prod.fst
        · exact fun e he => (mem_filter.mp he).2
        · exact (hMatching j).1.mono (fun _ he => (mem_filter.mp he).1)
      have hY : Y.card ≤ load (target j) := by
        apply Nat.le_trans _ (hUsed (target j))
        apply card_le_card_of_injOn Prod.snd
        · exact fun e he => (mem_filter.mp he).2
        · exact (hMatching j).2.mono (fun _ he => (mem_filter.mp he).1)
      have hCard : (X ∪ Y).card < (M j).card :=
        ((card_union_le X Y).trans (Nat.add_le_add hX hY)).trans_lt (hRoom j)
      obtain ⟨e,he,hn⟩ := exists_mem_notMem_of_card_lt_card hCard
      have hnX : e.1 ∉ Used (source j) := fun h => hn (mem_union_left _ (mem_filter.mpr ⟨he,h⟩))
      have hnY : e.2 ∉ Used (target j) := fun h => hn (mem_union_right _ (mem_filter.mpr ⟨he,h⟩))
      have fresh (u : P) : e.1 ≠ (f u).1 ∧ e.1 ≠ (f u).2 ∧
          e.2 ≠ (f u).1 ∧ e.2 ≠ (f u).2 := by
        have heC := hCells j e he
        have hfC := hCells u.val (f u) (hf u)
        have hS (i : I) (hi : source u.val = i) : (f u).1 ∈ Used i :=
          mem_union_left _ (mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩)
        have hT (i : I) (hi : target u.val = i) : (f u).2 ∈ Used i :=
          mem_union_right _ (mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩)
        refine ⟨?_,?_,?_,?_⟩
        · intro h
          exact hnX (h.symm ▸ hS _ (hfC.1.symm.trans ((congrArg cluster h).symm.trans heC.1)))
        · intro h
          exact hnX (h.symm ▸ hT _ (hfC.2.symm.trans ((congrArg cluster h).symm.trans heC.1)))
        · intro h
          exact hnY (h.symm ▸ hS _ (hfC.1.symm.trans ((congrArg cluster h).symm.trans heC.2)))
        · intro h
          exact hnY (h.symm ▸ hT _ (hfC.2.symm.trans ((congrArg cluster h).symm.trans heC.2)))
      let g (u : ↥(insert j P)) := if hu : u.val = j then e
        else f ⟨u.val,(mem_insert.mp u.prop).resolve_left hu⟩
      refine ⟨g,?_,?_⟩
      · intro u
        by_cases hu : u.val = j
        · simpa only [g,dif_pos hu,hu] using he
        · simpa only [g,dif_neg hu] using hf ⟨u.val,(mem_insert.mp u.prop).resolve_left hu⟩
      · intro u v huv
        by_cases hu : u.val = j <;> by_cases hv : v.val = j
        · exact (huv (Subtype.ext (hu.trans hv.symm))).elim
        · simpa only [g,dif_pos hu,dif_neg hv] using fresh ⟨v.val,(mem_insert.mp v.prop).resolve_left hv⟩
        · obtain ⟨h₁,h₂,h₃,h₄⟩ := fresh ⟨u.val,(mem_insert.mp u.prop).resolve_left hu⟩
          simpa only [g,dif_neg hu,dif_pos hv] using And.intro h₁.symm (And.intro h₃.symm (And.intro h₂.symm h₄.symm))
        · have hne : (⟨u.val,(mem_insert.mp u.prop).resolve_left hu⟩ : P) ≠
              ⟨v.val,(mem_insert.mp v.prop).resolve_left hv⟩ :=
            fun h => huv (Subtype.ext (congrArg (fun x : P => x.val) h))
          simpa only [g,dif_neg hu,dif_neg hv] using hDis _ _ hne
  obtain ⟨f,hf,hApart⟩ := chooseOn (univ : Finset J)
  refine ⟨fun j => f ⟨j,mem_univ _⟩,?_,?_⟩
  · intro j
    have hj := hf ⟨j,mem_univ _⟩
    exact ⟨hj,hDistinct j _ hj⟩
  · intro j k hjk
    exact hApart _ _ (fun h => hjk (congrArg (fun x : ↥(univ : Finset J) => x.val) h))

/-- The paper's (21m/100) endpoint load and (23m/50) candidate
matching size suffice for the greedy realization. -/
theorem exists_disjoint_chords_at_kuhn_osthus_load (cluster : V → I) (source target : J → I)
    (M : J → Finset (V × V)) (m : ℕ) (hm : 0 < m)
    (hCells : ∀ j e, e ∈ M j → cluster e.1 = source j ∧ cluster e.2 = target j)
    (hDistinct : ∀ j e, e ∈ M j → e.1 ≠ e.2)
    (hMatching : ∀ j, Set.InjOn Prod.fst (↑(M j) : Set (V × V)) ∧
      Set.InjOn Prod.snd (↑(M j) : Set (V × V)))
    (hLoad : ∀ i, 100*((univ.filter (fun j => source j = i)).card +
      (univ.filter (fun j => target j = i)).card) ≤ 21*m)
    (hSize : ∀ j, 23*m ≤ 50*(M j).card) :
    ∃ f : J → V × V, (∀ j, f j ∈ M j ∧ (f j).1 ≠ (f j).2) ∧
      ∀ j k, j ≠ k →
        (f j).1 ≠ (f k).1 ∧ (f j).1 ≠ (f k).2 ∧
        (f j).2 ≠ (f k).1 ∧ (f j).2 ≠ (f k).2 := by
  let load (i : I) := (univ.filter (fun j => source j = i)).card +
    (univ.filter (fun j => target j = i)).card
  apply exists_disjoint_chord_realization cluster source target M load
    hCells hDistinct hMatching (fun _ => le_rfl)
  intro j
  have h₁ : 100 * load (source j) ≤ 21*m := hLoad (source j)
  have h₂ : 100 * load (target j) ≤ 21*m := hLoad (target j)
  have h₃ := hSize j
  omega

end OverfullWork.DirectedRobustExpansion
