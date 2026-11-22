module

public import OverfullWork.DenseHall

@[expose] public section


namespace OverfullWork.DenseHall
open Finset
open scoped Classical

/-- Dense Hall remains valid with one exceptional left vertex having
only one neighbour. All other rows and all columns meet the half bound. -/
theorem exists_matching_exceptional {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → Prop) (x : A) (d : ℕ) (heq : Fintype.card A=Fintype.card B)
    (hsize : Fintype.card B≤2*d) (hx : ∃ b,r x b)
    (hA : ∀ a,a≠x → d≤(univ.filter (r a)).card)
    (hB : ∀ b,d≤(univ.filter (fun a => r a b)).card) :
    ∃ f : A ≃ B,∀ a,r a (f a) := by
  classical
  have hall : ∀ S : Finset A,S.card≤(univ.filter (fun b => ∃ a∈S,r a b)).card := by
    intro S
    by_cases hs : S.card≤d
    · by_cases hex : ∃ a∈S,a≠x
      · obtain ⟨a,ha,hax⟩:=hex
        have hsub : univ.filter (r a) ⊆ univ.filter (fun b => ∃ a∈S,r a b) := by
          intro b hb
          exact mem_filter.mpr ⟨mem_univ _,a,ha,(mem_filter.mp hb).2⟩
        exact hs.trans ((hA a hax).trans (card_le_card hsub))
      · have hsub : S⊆{x} := by
          intro a ha
          exact mem_singleton.mpr (by by_contra hn; exact hex ⟨a,ha,hn⟩)
        have hcard : S.card≤1:=by simpa only [card_singleton] using card_le_card hsub
        rcases S.eq_empty_or_nonempty with hS|⟨a,ha⟩
        · simp [hS]
        · have hax : a=x:=mem_singleton.mp (hsub ha)
          obtain ⟨b,hb⟩:=hx
          have hn : (univ.filter (fun b => ∃ a∈S,r a b)).Nonempty :=
            ⟨b,mem_filter.mpr ⟨mem_univ _,a,ha,by simpa only [hax] using hb⟩⟩
          have hpos:=card_pos.mpr hn
          omega
    · have hallB : ∀ b : B,∃ a∈S,r a b := by
        intro b
        by_contra hn
        have hsub : univ.filter (fun a => r a b) ⊆ Sᶜ := by
          intro a ha
          exact mem_compl.mpr (fun hS => hn ⟨a,hS,(mem_filter.mp ha).2⟩)
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
  obtain ⟨f,hf,hr⟩:=(Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hall
  have hb : Function.Bijective f:=(Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,heq⟩
  exact ⟨Equiv.ofBijective f hb,hr⟩

end OverfullWork.DenseHall
