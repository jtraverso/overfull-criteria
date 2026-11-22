module

public import OverfullWork.MaximumCoreDegree
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import OneFactor.Extend

@[expose] public section


/-! # An even augmentation for matching all maximum-degree vertices

Complete the vertices below maximum degree into a clique, and add one
extra low vertex exactly when the original order is odd. Every edge at
an original maximum-degree vertex remains an original graph edge.
Restricting a perfect matching therefore matches all maximum vertices.
-/
namespace OverfullWork.MaximumMatching
open SimpleGraph Finset
variable {V : Type*} [Fintype V]

/-- Zero or one extra vertex, so the augmented order is always even. -/
abbrev AugType (V : Type*) [Fintype V] := V ⊕ Fin (Fintype.card V%2)

def Low (G : SimpleGraph V) [DecidableRel G.Adj] : AugType V → Prop
  | .inl v => G.degree v<G.maxDegree
  | .inr _ => True

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidablePred (Low G) := fun z =>
  match z with
  | .inl _ => inferInstanceAs (Decidable (_<_))
  | .inr _ => inferInstanceAs (Decidable True)

def originalAdj (G : SimpleGraph V) : AugType V → AugType V → Prop
  | .inl u,.inl v => G.Adj u v
  | _,_ => False

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (originalAdj G) := fun x y =>
  match x,y with
  | .inl _,.inl _ => inferInstanceAs (Decidable (G.Adj _ _))
  | .inl _,.inr _ => inferInstanceAs (Decidable False)
  | .inr _,_ => inferInstanceAs (Decidable False)

def augmentation (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph (AugType V) where
  Adj x y := originalAdj G x y ∨ (x≠y ∧ Low G x ∧ Low G y)
  symm:=⟨by
    intro x y h
    rcases h with ho|⟨hne,hx,hy⟩
    · left
      cases x <;> cases y <;> simp only [originalAdj] at ho ⊢
      exact ho.symm
    · exact Or.inr ⟨Ne.symm hne,hy,hx⟩⟩
  loopless:=⟨by
    intro x h
    rcases h with ho|⟨hne,_,_⟩
    · cases x with
      | inl v => exact ho.ne rfl
      | inr _ => exact ho
    · exact hne rfl⟩

instance [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (augmentation G).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ (_∧_∧_)))

theorem card_augType : Fintype.card (AugType V)=Fintype.card V+Fintype.card V%2 := by
  simp only [AugType,Fintype.card_sum,Fintype.card_fin]

theorem even_card_augType : Even (Fintype.card (AugType V)) := by
  rw [card_augType]
  refine ⟨Fintype.card V/2+Fintype.card V%2,?_⟩
  have h:=Nat.mod_add_div (Fintype.card V) 2
  omega

theorem extra_card_le_one : Fintype.card (Fin (Fintype.card V%2))≤1 := by
  simp only [Fintype.card_fin]
  have h:=Nat.mod_lt (Fintype.card V) (by decide : 0<2)
  omega

theorem low_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : AugType V} (hxy : x≠y) (hx : Low G x) (hy : Low G y) :
    (augmentation G).Adj x y := Or.inr ⟨hxy,hx,hy⟩

theorem original_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (h : G.Adj u v) : (augmentation G).Adj (.inl u) (.inl v) := Or.inl h

/-- Every neighbour of a maximum-degree original vertex is original,
and its edge was already present before augmentation. -/
theorem high_adj_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hv : G.degree v=G.maxDegree) (z : AugType V) :
    (augmentation G).Adj (.inl v) z ↔ ∃w : V,z=.inl w ∧ G.Adj v w := by
  constructor
  · intro h
    rcases h with ho|⟨_,hlo,_⟩
    · cases z with
      | inl w => exact ⟨w,rfl,ho⟩
      | inr _ => exact False.elim ho
    · change G.degree v<G.maxDegree at hlo
      omega
  · rintro ⟨w,rfl,h⟩
    exact original_edge G h

/-- The original maximum-degree vertices are exactly the old nonlow vertices. -/
theorem not_low_inl_iff (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ¬Low G (.inl v) ↔ G.degree v=G.maxDegree := by
  change ¬G.degree v<G.maxDegree ↔ G.degree v=G.maxDegree
  have h:=G.degree_le_maxDegree v
  omega

/-- Discard both dummy edges and all new low-low clique edges from a
perfect-matching candidate. This is an actual simple graph below `G`. -/
def restriction (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : (augmentation G).Subgraph) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ P.Adj (.inl u) (.inl v)
  symm:=⟨fun _ _ h => ⟨h.1.symm,P.adj_symm h.2⟩⟩
  loopless:=⟨fun _ h => h.1.ne rfl⟩

theorem restriction_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : (augmentation G).Subgraph) : restriction G P≤G := fun _ _ h => h.1

theorem restriction_matching (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : (augmentation G).Subgraph) (hP : P.IsPerfectMatching) :
    OneFactor.IsMatchingGraph (restriction G P) := by
  intro v a b ha hb
  obtain ⟨z,_,huniq⟩:=(Subgraph.isPerfectMatching_iff.mp hP) (.inl v)
  exact Sum.inl.inj ((huniq (.inl a) ha.2).trans (huniq (.inl b) hb.2).symm)

theorem restriction_matches_maximum (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : (augmentation G).Subgraph) (hP : P.IsPerfectMatching)
    (v : V) (hv : G.degree v=G.maxDegree) : ∃! w, (restriction G P).Adj v w := by
  obtain ⟨z,hz,huniq⟩:=(Subgraph.isPerfectMatching_iff.mp hP) (.inl v)
  obtain ⟨w,hzw,hvw⟩:=(high_adj_iff G v hv z).mp (P.adj_sub hz)
  subst z
  refine ⟨w,⟨hvw,hz⟩,?_⟩
  intro a ha
  exact Sum.inl.inj (huniq (.inl a) ha.2)

/-- A perfect matching of the augmentation yields a genuine matching in
`G` saturating all vertices of actual maximum degree. -/
theorem exists_matching_covering_maximum_of_augmented_perfect (G : SimpleGraph V)
    [DecidableRel G.Adj] (hP : ∃P : (augmentation G).Subgraph,P.IsPerfectMatching) :
    ∃M : SimpleGraph V,M≤G ∧ OneFactor.IsMatchingGraph M ∧
      ∀v,G.degree v=G.maxDegree → ∃!w,M.Adj v w := by
  obtain ⟨P,hP⟩:=hP
  exact ⟨restriction G P,restriction_le G P,restriction_matching G P hP,
    restriction_matches_maximum G P hP⟩

end OverfullWork.MaximumMatching
