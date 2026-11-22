module

public import OverfullWork.KuhnOsthusPathPartitionSizes

@[expose] public section


/-! Assign the exceptional arcs of an original 1-factor by the
style of their ordinary endpoint and their direction. -/
namespace OverfullWork.DirectedRobustExpansion

open DirectedDemandHall (Arc)
variable {V J : Type*}

def exceptionalFactorPiece (σ : Equiv.Perm V) (label : V → J)
    (Z : Finset V) (i : Bool × J) : Digraph V :=
  ⟨fun x y => σ x = y ∧
    ((i.1 = false ∧ x ∈ Z ∧ y ∉ Z ∧ label y = i.2) ∨
     (i.1 = true ∧ x ∉ Z ∧ y ∈ Z ∧ label x = i.2))⟩

theorem exceptional_factor_piece_sides (σ : Equiv.Perm V) (label : V → J)
    (Z : Finset V) (i : Bool × J) :
    (∀ {x y}, (exceptionalFactorPiece σ label Z i).Adj x y → x ∈ Z ∧ y ∉ Z) ∨
    (∀ {x y}, (exceptionalFactorPiece σ label Z i).Adj x y → x ∉ Z ∧ y ∈ Z) := by
  cases hi : i.1
  · left
    intro x y h
    rcases h.2 with h | h
    · exact ⟨h.2.1,h.2.2.1⟩
    · simp [hi] at h
  · right
    intro x y h
    rcases h.2 with h | h
    · simp [hi] at h
    · exact ⟨h.2.1,h.2.2.1⟩

theorem exceptional_factor_piece_path_system (σ : Equiv.Perm V) (label : V → J)
    (Z : Finset V) (i : Bool × J) :
    IsDirectedPathSystem (exceptionalFactorPiece σ label Z i) := by
  let H := exceptionalFactorPiece σ label Z i
  have hn {x y z : V} (h : H.Adj x y) (g : H.Adj y z) : False := by
    rcases exceptional_factor_piece_sides σ label Z i with hs | hs
    · exact (hs h).2 (hs g).1
    · exact (hs g).1 (hs h).2
  have hCycle : NoDirectedCycle H := by
    have hBot : NoDirectedCycle ((⊥ : Digraph V) ⊔ H) := by
      apply no_directed_cycle_sup_of_fresh_ends
      · intro x h
        obtain ⟨_,h,_⟩ := Relation.TransGen.head'_iff.mp h
        exact h
      · intro x y h
        right
        intro w hw
        exact ((Digraph.sup_adj _ _ _ _).mp hw).elim id (hn h)
    simpa only [bot_sup_eq] using hBot
  refine ⟨hCycle,?_,?_⟩
  · intro x y z h g
    exact h.1.symm.trans g.1
  · intro x y z h g
    exact σ.injective (h.1.trans g.1.symm)

theorem exceptional_factor_arc_owner (σ : Equiv.Perm V) (label : V → J)
    (Z : Finset V) {x y : V} :
    (σ x = y ∧ ((x ∈ Z ∧ y ∉ Z) ∨ (x ∉ Z ∧ y ∈ Z))) ↔
      ∃! i, (exceptionalFactorPiece σ label Z i).Adj x y := by
  constructor
  · rintro ⟨hσ,⟨hx,hy⟩ | ⟨hx,hy⟩⟩
    · refine ⟨(false,label y),⟨hσ,Or.inl ⟨rfl,hx,hy,rfl⟩⟩,?_⟩
      rintro i ⟨_,hi | hi⟩
      · exact Prod.ext hi.1 hi.2.2.2.symm
      · exact (hi.2.1 hx).elim
    · refine ⟨(true,label x),⟨hσ,Or.inr ⟨rfl,hx,hy,rfl⟩⟩,?_⟩
      rintro i ⟨_,hi | hi⟩
      · exact (hx hi.2.1).elim
      · exact Prod.ext hi.1 hi.2.2.2.symm
  · rintro ⟨i,he,_⟩
    exact ⟨he.1,(exceptional_factor_piece_sides σ label Z i).elim
      (fun h => Or.inl (h he)) (fun h => Or.inr (h he))⟩

theorem exceptional_factor_incidences_owners (σ : Equiv.Perm V) (label : V → J)
    (Z : Finset V) (hNoInternal : ∀ x ∈ Z, σ x ∉ Z) :
    (∀ x ∈ Z, ∃! i, ∃ y, (exceptionalFactorPiece σ label Z i).Adj x y) ∧
    (∀ x ∈ Z, ∃! i, ∃ y, (exceptionalFactorPiece σ label Z i).Adj y x) := by
  constructor
  · intro x hx
    obtain ⟨i,hi,hUnique⟩ := (exceptional_factor_arc_owner σ label Z).mp
      ⟨rfl,Or.inl ⟨hx,hNoInternal x hx⟩⟩
    exact ⟨i,⟨σ x,hi⟩,fun j ⟨y,hy⟩ => hUnique j (hy.1.symm ▸ hy)⟩
  · intro x hx
    have he := σ.apply_symm_apply x
    have hpre : σ.symm x ∉ Z := by
      intro hp
      apply hNoInternal (σ.symm x) hp
      rwa [he]
    obtain ⟨i,hi,hUnique⟩ := (exceptional_factor_arc_owner σ label Z).mp
      ⟨he,Or.inr ⟨hpre,hx⟩⟩
    refine ⟨i,⟨σ.symm x,hi⟩,?_⟩
    rintro j ⟨y,hy⟩
    have hy' : y = σ.symm x := σ.injective (hy.1.trans he.symm)
    exact hUnique j (hy' ▸ hy)

theorem exceptional_factor_piece_style [DecidableEq J] (σ : Equiv.Perm V)
    (label : V → J) (Z : Finset V) (i : Bool × J) :
    SupportedByStyles label Z {i.2} (exceptionalFactorPiece σ label Z i) := by
  intro v hv he
  rcases he with ⟨w,hw⟩ | ⟨w,hw⟩
  · rcases hw.2 with h | h
    · exact (hv h.2.1).elim
    · exact Finset.mem_singleton.mpr h.2.2.2
  · rcases hw.2 with h | h
    · exact Finset.mem_singleton.mpr h.2.2.2
    · exact (hv h.2.2.1).elim

theorem card_exceptional_factor_piece [Fintype V] (σ : Equiv.Perm V)
    (label : V → J) (Z : Finset V) (i : Bool × J) :
    Fintype.card (Arc (exceptionalFactorPiece σ label Z i)) ≤ Z.card := by
  let H := exceptionalFactorPiece σ label Z i
  have hp := exceptional_factor_piece_path_system σ label Z i
  rw [←Fintype.card_coe]
  rcases exceptional_factor_piece_sides σ label Z i with hs | hs
  · let f (e : Arc H) : Z := ⟨e.val.1,(hs e.prop).1⟩
    apply Fintype.card_le_of_injective f
    intro a b he
    have eq : a.val.1 = b.val.1 := congrArg (fun z : Z => (z : V)) he
    refine Subtype.ext (Prod.ext eq (hp.out_unique a.prop ?_))
    rw [eq]
    exact b.prop
  · let f (e : Arc H) : Z := ⟨e.val.2,(hs e.prop).2⟩
    apply Fintype.card_le_of_injective f
    intro a b he
    have eq : a.val.2 = b.val.2 := congrArg (fun z : Z => (z : V)) he
    refine Subtype.ext (Prod.ext (hp.in_unique a.prop ?_) eq)
    rw [eq]
    exact b.prop

end OverfullWork.DirectedRobustExpansion
