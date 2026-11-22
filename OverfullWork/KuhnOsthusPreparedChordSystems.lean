module

public import OverfullWork.KuhnOsthusChordRoundOwners

@[expose] public section


/-! The original path systems prepared for a phase of Lemma 9.7.
The arc partition is physical and the balance is checked in the
contracted digraph. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V I J R : Type*} [Fintype V]

/-- Original prescribed systems with exact support, and the balanced
free slots and footprint used by the Hamilton completion. -/
structure PreparedChordSystems (P : Digraph V) (Z : Finset V) (c : ↥Zᶜ → I)
    (s : Equiv.Perm I) (K : ℕ) (J : Type*) where
  system : J → Digraph V
  le : ∀ i, system i ≤ P
  owns : ∀ x y, P.Adj x y → ∃! i, (system i).Adj x y
  path : ∀ i, IsDirectedPathSystem (system i)
  covers : ∀ i, CoversExceptional (system i) Z
  no_internal : ∀ i x y, (system i).Adj x y → x ∈ Z → y ∉ Z
  balance : ∀ i j, (freeOut (basicExceptionalPathSystem (system i) Z) c j).card =
    (freeIn (basicExceptionalPathSystem (system i) Z) c (s j)).card
  footprint : ∀ i j, (finiteSatisfying (fun v => c v = j ∧
    IncidentTo (basicExceptionalPathSystem (system i) Z) v)).card ≤ K

/-- Change the labels of the path systems along a bijection. -/
def PreparedChordSystems.reindex {P : Digraph V} {Z : Finset V} {c : ↥Zᶜ → I}
    {s : Equiv.Perm I} {K : ℕ} (Q : PreparedChordSystems P Z c s K J) (e : R ≃ J) :
    PreparedChordSystems P Z c s K R where
  system i := Q.system (e i)
  le i := Q.le (e i)
  owns := by
    intro x y h
    obtain ⟨i,hi,hU⟩ := Q.owns x y h
    refine ⟨e.symm i,by simpa only [e.apply_symm_apply] using hi,?_⟩
    intro j hj
    exact e.injective ((hU (e j) hj).trans (e.apply_symm_apply _).symm)
  path i := Q.path (e i)
  covers i := Q.covers (e i)
  no_internal i := Q.no_internal (e i)
  balance i := Q.balance (e i)
  footprint i := Q.footprint (e i)

/-- Combine independently prepared rounds whose required physical
arcs have exactly one round owner. -/
def combine_prepared_chord_rounds (P : Digraph V) (W : R → Digraph V)
    (Z : Finset V) (c : ↥Zᶜ → I) (s : Equiv.Perm I) (K : ℕ)
    (Q : ∀ r, PreparedChordSystems (W r) Z c s K J)
    (hLe : ∀ r, W r ≤ P) (hOwn : ∀ x y, P.Adj x y → ∃! r, (W r).Adj x y) :
    PreparedChordSystems P Z c s K (R × J) where
  system i := (Q i.1).system i.2
  le i := ((Q i.1).le i.2).trans (hLe i.1)
  owns := by
    intro x y h
    obtain ⟨r,hr,hRound⟩ := hOwn x y h
    obtain ⟨j,hj,hSlot⟩ := (Q r).owns x y hr
    refine ⟨(r,j),hj,?_⟩
    rintro ⟨r',j'⟩ h'
    have he : r' = r := hRound r' ((Q r').le j' h')
    subst r'
    exact Prod.ext rfl (hSlot j' h')
  path i := (Q i.1).path i.2
  covers i := (Q i.1).covers i.2
  no_internal i := (Q i.1).no_internal i.2
  balance i := (Q i.1).balance i.2
  footprint i := (Q i.1).footprint i.2

/-- Construct the original prepared systems from the ordinary
matching pieces, the realized walk pieces, and the assigned
complete exceptional path systems. -/
theorem exists_prepared_chord_systems (Z : Finset V) (H U : Digraph ↥Zᶜ) (E : Digraph V)
    (M D : J → Digraph ↥Zᶜ) (C : J → Digraph V) (c : ↥Zᶜ → I) (s : Equiv.Perm I) (K : ℕ)
    (hDU : ∀ i, D i ≤ U) (hMH : ∀ i, M i ≤ H) (hCE : ∀ i, C i ≤ E)
    (hU : ∀ x y, U.Adj x y → ∃! i, (D i).Adj x y)
    (hH : ∀ x y, H.Adj x y → ∃! i, (M i).Adj x y)
    (hE : ∀ x y, E.Adj x y → ∃! i, (C i).Adj x y)
    (hUH : Disjoint U H)
    (hM : ∀ i, IsDirectedPathSystem (M i))
    (hC : ∀ i, IsDirectedPathSystem (C i) ∧ CoversExceptional (C i) Z)
    (hNo : ∀ i x y, (C i).Adj x y → x ∈ Z → y ∉ Z)
    (hApartD : ∀ i x, IncidentTo (D i) x → ¬ IncidentTo (M i ⊔ basicExceptionalPathSystem (C i) Z) x)
    (hApartM : ∀ i x, IncidentTo (M i) x → ¬ IncidentTo (basicExceptionalPathSystem (C i) Z) x)
    (hBasic : ∀ i, let W := D i ⊔ (M i ⊔ basicExceptionalPathSystem (C i) Z)
      IsDirectedPathSystem W ∧
      (∀ j, (freeOut W c j).card = (freeIn W c (s j)).card) ∧
      ∀ j, (finiteSatisfying (fun v => c v = j ∧ IncidentTo W v)).card ≤ K) :
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
    let P := liftDirectedPair e e (U ⊔ H) ⊔ E
    Disjoint (liftDirectedPair e e (U ⊔ H)) E →
    Nonempty (PreparedChordSystems P Z c s K J) := by
  intro e P hDis
  have hD (i : J) : IsDirectedPathSystem (D i) := by
    have h := (hBasic i).1
    exact ⟨fun x hx => h.acyclic x (Relation.TransGen.mono (fun _ _ he => Or.inl he) x x hx),
      fun a b => h.out_unique (Or.inl a) (Or.inl b),
      fun a b => h.in_unique (Or.inl a) (Or.inl b)⟩
  obtain ⟨Q,hLe,hOwn,hPath,hNo',hEq⟩ := assemble_original_chord_round Z H U E M D C
    hDU hMH hCE hU hH hE hUH hD hM hC hNo hApartD hApartM hDis
  refine ⟨⟨Q,hLe,hOwn,fun i => (hPath i).1,fun i => (hPath i).2,hNo',?_,?_⟩⟩
  · intro i
    rw [hEq]
    exact (hBasic i).2.1
  · intro i j
    rw [hEq]
    exact (hBasic i).2.2 j

end OverfullWork.DirectedRobustExpansion
