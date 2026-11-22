module

public import OverfullWork.DenseHall
public import OverfullWork.MatchingPartner

@[expose] public section


namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def pairingGraph (A B : Finset V) (hdis : Disjoint A B) (f : A ≃ B) : SimpleGraph V where
  Adj u v := (∃ a : A,u=a ∧ v=f a) ∨ (∃ a : A,v=a ∧ u=f a)
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by
    intro v h
    rcases h with ⟨a,hu,hv⟩|⟨a,hu,hv⟩
    all_goals exact (Finset.disjoint_left.mp hdis) (hu ▸ a.2) (hv ▸ (f a).2)⟩

noncomputable instance (A B : Finset V) (hdis : Disjoint A B) (f : A ≃ B) :
    DecidableRel (pairingGraph A B hdis f).Adj := Classical.decRel _

theorem pairing_adj_left (A B : Finset V) (hdis : Disjoint A B) (f : A ≃ B)
    (u : V) (hu : u∈A) (v : V) :
    (pairingGraph A B hdis f).Adj u v ↔ v=f ⟨u,hu⟩ := by
  constructor
  · intro h
    rcases h with ⟨a,ha,hv⟩|⟨a,ha,hv⟩
    · have he : a=⟨u,hu⟩:=Subtype.ext ha.symm
      simpa only [he] using hv
    · exact False.elim ((Finset.disjoint_left.mp hdis) hu (hv ▸ (f a).2))
  · intro h
    exact Or.inl ⟨⟨u,hu⟩,rfl,h⟩

theorem pairing_adj_right (A B : Finset V) (hdis : Disjoint A B) (f : A ≃ B)
    (u : V) (hu : u∈B) (v : V) :
    (pairingGraph A B hdis f).Adj u v ↔ v=f.symm ⟨u,hu⟩ := by
  constructor
  · intro h
    rcases h with ⟨a,ha,hv⟩|⟨a,ha,hv⟩
    · exact False.elim ((Finset.disjoint_left.mp hdis) (ha ▸ a.2) hu)
    · have he : f a=⟨u,hu⟩:=Subtype.ext hv.symm
      have he' : a=f.symm ⟨u,hu⟩ := by rw [←he]; simp
      simpa only [he'] using ha
  · intro h
    refine Or.inr ⟨f.symm ⟨u,hu⟩,h,?_⟩
    simp

theorem pairing_degree (A B : Finset V) (hdis : Disjoint A B) (f : A ≃ B) (u : V) :
    (pairingGraph A B hdis f).degree u=if u∈A ∨ u∈B then 1 else 0 := by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  by_cases ha : u∈A
  · rw [if_pos (Or.inl ha)]
    apply card_eq_one.mpr
    refine ⟨(f ⟨u,ha⟩:V),?_⟩
    ext v
    simp only [SimpleGraph.mem_neighborFinset,mem_singleton]
    exact pairing_adj_left A B hdis f u ha v
  · by_cases hb : u∈B
    · rw [if_pos (Or.inr hb)]
      apply card_eq_one.mpr
      refine ⟨(f.symm ⟨u,hb⟩:V),?_⟩
      ext v
      simp only [SimpleGraph.mem_neighborFinset,mem_singleton]
      exact pairing_adj_right A B hdis f u hb v
    · rw [if_neg (by simp [ha,hb])]
      apply card_eq_zero.mpr
      ext v
      simp only [SimpleGraph.mem_neighborFinset,notMem_empty,iff_false]
      intro h
      rcases h with ⟨a,hu,_⟩|⟨a,_,hu⟩
      · exact ha (hu ▸ a.2)
      · exact hb (hu ▸ (f a).2)

noncomputable def pairingMatching (A B : Finset V) (hdis : Disjoint A B) (f : A ≃ B) : MultiGraph V :=
  ofSimpleGraph (pairingGraph A B hdis f)

theorem pairingMatching_degree (A B : Finset V) (hdis : Disjoint A B) (f : A ≃ B) (u : V) :
    (pairingMatching A B hdis f).degree u=if u∈A ∨ u∈B then 1 else 0 := by
  exact (degree_ofSimpleGraph _ u).trans (pairing_degree A B hdis f u)

theorem pairingMatching_le (A B : Finset V) (hdis : Disjoint A B) (f : A ≃ B) (M : MultiGraph V)
    (hf : ∀ a : A,0<M.mult s((a:V),(f a:V))) :
    ∀ e,(pairingMatching A B hdis f).mult e≤M.mult e := by
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    change (if s(u,v)∈(pairingGraph A B hdis f).edgeSet then 1 else 0)≤_
    by_cases hmem : s(u,v)∈(pairingGraph A B hdis f).edgeSet
    · rw [if_pos hmem]
      rw [SimpleGraph.mem_edgeSet] at hmem
      rcases hmem with ⟨a,rfl,rfl⟩|⟨a,rfl,rfl⟩
      · exact hf a
      · have h:=hf a
        rw [Sym2.eq_swap] at h
        omega
    · rw [if_neg hmem]
      exact Nat.zero_le _

end SimpleGraph.MultiGraph
