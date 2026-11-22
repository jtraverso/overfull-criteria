module

public import OverfullWork.DirectedSpanningConfiguration

@[expose] public section


/-! Edge-disjoint realizations on an arbitrary prefix of the layouts.
The graph subtraction uses host arcs and leaves fixed copies in their layout. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset
open scoped Classical
variable {V I J : Type*}

/-- Realizations of the processed layouts, with disjoint host arcs. -/
structure PackingPrefix (D : Digraph V) (L : J → Layout V I) (S : Finset J) where
  round : ∀ i : S, Realization D (L i.val)
  disjoint : Pairwise (fun i j => Disjoint (round i).used (round j).used)

def PackingPrefix.used {D : Digraph V} {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix D L S) : Digraph V :=
  ⨆ i : S, (P.round i).used

theorem PackingPrefix.used_le {D : Digraph V} {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix D L S) : P.used ≤ D :=
  iSup_le fun i => (P.round i).used_le

def PackingPrefix.empty (D : Digraph V) (L : J → Layout V I) : PackingPrefix D L ∅ where
  round i := (notMem_empty i.val i.prop).elim
  disjoint i := (notMem_empty i.val i.prop).elim

/-- An actual realization in the unused graph extends the prefix. -/
noncomputable def PackingPrefix.insert {D : Digraph V} {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix D L S) {i : J} (hi : i ∉ S)
    (R : Realization (D \ P.used) (L i)) : PackingPrefix D L (insert i S) where
  round j := if h : j.val ∈ S then P.round ⟨j.val,h⟩
    else
      have he : j.val = i := (mem_insert.mp j.prop).resolve_right h
      he.symm ▸ R.rehost sdiff_le
  disjoint := by
    intro j k hjk
    have hBetween (j : S) : Disjoint (P.round j).used R.used := by
      apply disjoint_iff_inf_le.mpr
      intro x y h
      have hP : P.used.Adj x y := le_iSup (fun a : S => (P.round a).used) j h.1
      exact (R.used_le h.2).2 hP
    by_cases hj : j.val ∈ S
    · by_cases hk : k.val ∈ S
      · simp only [dif_pos hj,dif_pos hk]
        exact P.disjoint (fun h => hjk (Subtype.ext
          (congrArg (fun a : S => a.val) h)))
      · have hk' : k = ⟨i,mem_insert_self _ _⟩ :=
          Subtype.ext ((mem_insert.mp k.prop).resolve_right hk)
        subst k
        simp only [dif_pos hj,dif_neg hi]
        exact hBetween ⟨j.val,hj⟩
    · have hj' : j = ⟨i,mem_insert_self _ _⟩ :=
        Subtype.ext ((mem_insert.mp j.prop).resolve_right hj)
      subst j
      by_cases hk : k.val ∈ S
      · simp only [dif_pos hk,dif_neg hi]
        exact (hBetween ⟨k.val,hk⟩).symm
      · exact (hjk (Subtype.ext ((mem_insert.mp k.prop).resolve_right hk).symm)).elim

theorem PackingPrefix.insert_round_old {D : Digraph V} {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix D L S) {i : J} (hi : i ∉ S)
    (R : Realization (D \ P.used) (L i)) (j : S) :
    (P.insert hi R).round ⟨j.val,mem_insert_of_mem j.prop⟩ = P.round j := by
  simp only [PackingPrefix.insert,dif_pos j.prop]

theorem PackingPrefix.insert_round_new {D : Digraph V} {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix D L S) {i : J} (hi : i ∉ S)
    (R : Realization (D \ P.used) (L i)) :
    (P.insert hi R).round ⟨i,mem_insert_self _ _⟩ = R.rehost sdiff_le := by
  simp only [PackingPrefix.insert,dif_neg hi]

/-- After an extension, the used graph is exactly the old used graph
together with the arcs of the new realization. -/
theorem PackingPrefix.used_insert {D : Digraph V} {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix D L S) {i : J} (hi : i ∉ S)
    (R : Realization (D \ P.used) (L i)) :
    (P.insert hi R).used = P.used ⊔ R.used := by
  ext x y
  simp only [PackingPrefix.used,Digraph.iSup_adj,Digraph.sup_adj]
  constructor
  · rintro ⟨⟨j,hj⟩,hxy⟩
    rcases mem_insert.mp hj with rfl | hj'
    · right
      rwa [P.insert_round_new hi R] at hxy
    · left
      exact ⟨⟨j,hj'⟩,by simpa only [P.insert_round_old hi R ⟨j,hj'⟩] using hxy⟩
  · rintro (⟨j,hj⟩ | hnew)
    · exact ⟨⟨j.val,mem_insert_of_mem j.prop⟩,by simpa only [P.insert_round_old hi R j] using hj⟩
    · refine ⟨⟨i,mem_insert_self _ _⟩,?_⟩
      rw [P.insert_round_new hi R]
      exact hnew

/-- The full edge-copy set, keeping a separate fixed namespace for each
round even when its endpoints or local index are repeated. -/
def PackingPrefix.copiesAt {D : Digraph V} {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix D L S) (i : S) : Set ((V × V) ⊕ (J × I)) :=
  {x | match x with
       | .inl (u,v) => (P.round i).used.Adj u v
       | .inr (j,k) => j = i.val ∧ k ∈ (L i.val).fixed}

/-- Distinct rounds have disjoint copies, including the fixed occurrences. -/
theorem PackingPrefix.copies_pairwise {D : Digraph V} {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix D L S) : Pairwise (fun i j => Disjoint (P.copiesAt i) (P.copiesAt j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  cases x with
  | inl e =>
    exact disjoint_iff_inf_le.mp (P.disjoint hij) (show
      ((P.round i).used ⊓ (P.round j).used).Adj e.1 e.2 from ⟨hi,hj⟩)
  | inr e =>
    have hi' : e.1 = i.val := hi.1
    have hj' : e.1 = j.val := hj.1
    exact hij (Subtype.ext (hi'.symm.trans hj'))

end OverfullWork.DirectedSpanningConfiguration
