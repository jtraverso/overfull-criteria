module

public import OverfullWork.PartialColouring
public import Mathlib.Combinatorics.Hall.Basic

@[expose] public section


/-! # Perfect matchings in a dense balanced bipartite relation -/

namespace OverfullWork.DenseHall

open Finset
open scoped Classical

/-- An explicit Hall proof: minimum degree at least half the common side
size gives a perfect bipartite matching. Empty sides are included. -/
theorem exists_matching {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → Prop) (d : ℕ) (heq : Fintype.card A=Fintype.card B)
    (hsize : Fintype.card B≤2*d)
    (hA : ∀ a,d≤(univ.filter (r a)).card)
    (hB : ∀ b,d≤(univ.filter (fun a => r a b)).card) :
    ∃ f : A ≃ B,∀ a,r a (f a) := by
  classical
  have hall : ∀ S : Finset A,S.card≤(univ.filter (fun b => ∃ a∈S,r a b)).card := by
    intro S
    by_cases hs : S.card≤d
    · rcases S.eq_empty_or_nonempty with hS|⟨a,ha⟩
      · simp [hS]
      · have hsub : univ.filter (r a) ⊆ univ.filter (fun b => ∃ a∈S,r a b) := by
          intro b hb
          exact mem_filter.mpr ⟨mem_univ _,a,ha,(mem_filter.mp hb).2⟩
        exact hs.trans ((hA a).trans (card_le_card hsub))
    · have hallB : ∀ b : B,∃ a∈S,r a b := by
        intro b
        by_contra hn
        have hsub : univ.filter (fun a => r a b) ⊆ Sᶜ := by
          intro a ha
          apply mem_compl.mpr
          intro hS
          exact hn ⟨a,hS,(mem_filter.mp ha).2⟩
        have hcard:=card_le_card hsub
        have hc:=card_compl S
        have hd:=hB b
        have hSmax : S.card≤Fintype.card A:=card_le_univ S
        omega
      have hfull : univ.filter (fun b => ∃ a∈S,r a b)=(univ : Finset B) := by
        ext b
        simp only [mem_filter,mem_univ,true_and]
        exact iff_true_intro (hallB b)
      rw [hfull,card_univ,←heq]
      exact card_le_univ S
  obtain ⟨f,hf,hr⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hall
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,heq⟩
  exact ⟨Equiv.ofBijective f hb,hr⟩

theorem subtype_filter_card {V : Type*} [DecidableEq V] (S : Finset V) (p : V → Prop) :
    (univ.filter (fun v : S => p v)).card=(S.filter p).card := by
  classical
  apply card_bij (fun v _ => v.val)
  · intro v hv
    exact mem_filter.mpr ⟨v.2,(mem_filter.mp hv).2⟩
  · intro v _ w _ he
    exact Subtype.ext he
  · intro v hv
    obtain ⟨hs,hp⟩:=mem_filter.mp hv
    exact ⟨⟨v,hs⟩,mem_filter.mpr ⟨mem_univ _,hp⟩,rfl⟩

/-- The finset interface permits previously covered vertices to be
removed before applying Hall. The matching uses the supplied relation. -/
theorem exists_matching_on {V : Type*} [DecidableEq V]
    (A B : Finset V) (r : V → V → Prop) (d : ℕ)
    (heq : A.card=B.card) (hsize : B.card≤2*d)
    (hA : ∀ a∈A,d≤(B.filter (r a)).card)
    (hB : ∀ b∈B,d≤(A.filter (fun a => r a b)).card) :
    ∃ f : A ≃ B,∀ a : A,r a (f a) := by
  classical
  apply exists_matching (fun a : A => fun b : B => r a b) d
  · simpa only [Fintype.card_coe] using heq
  · simpa only [Fintype.card_coe] using hsize
  · intro a
    have hcard : (univ.filter (fun b : B => r a b)).card=(B.filter (r a)).card := by
      exact subtype_filter_card B (r a)
    rw [hcard]
    exact hA a a.2
  · intro b
    have hcard : (univ.filter (fun a : A => r a b)).card=(A.filter (fun a => r a b)).card := by
      exact subtype_filter_card A (fun a => r a b)
    rw [hcard]
    exact hB b b.2

end OverfullWork.DenseHall
