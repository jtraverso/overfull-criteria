module

public import OverfullWork.KuhnOsthusResidueAssignment

@[expose] public section


/-! The opening step of Kühn–Osthus Lemma 9.7. Each factor of
the ordinary residue gets its own ordered matching partition. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Factorize the entire regular residue and independently apply
Lemma 8.7 to its factors. The resulting matchings partition the
physical arcs with a unique pair of indices. -/
theorem partition_regular_residue_with_permutations (H : Digraph V) (r b : ℕ)
    (hReg : ∀ v, inDegree H v = r ∧ outDegree H v = r)
    (hLoop : ∀ v, ¬ H.Adj v v) {g : ℕ} [NeZero g] (coarse : V → Fin g)
    (hb : 0 < b) (hSize : 3*b ≤ Fintype.card V) (hLarge : 802 ≤ g) :
    let n := b*3*g.choose 2
    ∃ (σ : Fin r → Equiv.Perm V) (F : Fin r → Digraph V),
      ∃ P : ∀ a, OrderedResidueMatchings (F a) coarse n (b*3) (2*g^2*Fintype.card V/n) 10,
        (∀ a x y, (F a).Adj x y ↔ σ a x = y) ∧
        (∀ a, F a ≤ H) ∧ (∀ x y, H.Adj x y ↔ ∃! a, (F a).Adj x y) ∧
          ∀ x y, H.Adj x y ↔ ∃! p : Fin r × Fin n, ((P p.1).matching p.2).Adj x y := by
  intro n
  obtain ⟨σ,hσ,hDis⟩ := exists_permutation_factorization_of_regular H r hReg
  let F (a : Fin r) : Digraph V := matchingUnion (fun _ : Fin 1 => σ a)
  have hL (a : Fin r) (x y : V) : (F a).Adj x y ↔ σ a x = y :=
    ⟨fun ⟨_,h⟩ => h,fun h => ⟨0,h⟩⟩
  have hH (x y : V) : H.Adj x y ↔ ∃ a, σ a x = y := by rw [←hσ]; rfl
  have hLe (a : Fin r) : F a ≤ H :=
    fun x y h => (hH x y).mpr ⟨a,(hL a x y).mp h⟩
  have hOne (a : Fin r) := matchingUnion_exact_semidegrees (fun _ : Fin 1 => σ a)
    (fun i j h _ => (h (Subsingleton.elim i j)).elim)
  let P (a : Fin r) := Classical.choice (kuhn_osthus_lemma_8_7 (F a) (hOne a)
    (fun v h => hLoop v (hLe a h)) coarse b hb hSize (residue_spacing_ten_bound hLarge))
  have hFactor (x y : V) : H.Adj x y ↔ ∃! a, (F a).Adj x y := by
    constructor
    · intro h
      obtain ⟨a,ha⟩ := (hH x y).mp h
      refine ⟨a,(hL a x y).mpr ha,?_⟩
      intro a' ha'
      by_contra hn
      exact hDis a' a hn x (((hL a' x y).mp ha').trans ha.symm)
    · rintro ⟨a,ha,_⟩
      exact hLe a ha
  refine ⟨σ,F,P,hL,hLe,hFactor,?_⟩
  intro x y
  constructor
  · intro h
    obtain ⟨a,ha,hU⟩ := (hFactor x y).mp h
    obtain ⟨j,hj,hV⟩ := ((P a).partition x y).mp ha
    refine ⟨(a,j),hj,?_⟩
    rintro ⟨a',j'⟩ hp
    have he : a' = a := hU a' ((P a').matching_le j' hp)
    subst a'
    exact Prod.ext rfl (hV j' hp)
  · rintro ⟨⟨a,j⟩,hj,_⟩
    exact hLe a ((P a).matching_le j hj)

/-- Retain the ordered partition when no permutation witness is needed. -/
theorem partition_regular_residue_into_ordered_matchings (H : Digraph V) (r b : ℕ)
    (hReg : ∀ v, inDegree H v = r ∧ outDegree H v = r)
    (hLoop : ∀ v, ¬ H.Adj v v) {g : ℕ} [NeZero g] (coarse : V → Fin g)
    (hb : 0 < b) (hSize : 3*b ≤ Fintype.card V) (hLarge : 802 ≤ g) :
    let n := b*3*g.choose 2
    ∃ F : Fin r → Digraph V,
      ∃ P : ∀ a, OrderedResidueMatchings (F a) coarse n (b*3) (2*g^2*Fintype.card V/n) 10,
        (∀ a, F a ≤ H) ∧ (∀ x y, H.Adj x y ↔ ∃! a, (F a).Adj x y) ∧
          ∀ x y, H.Adj x y ↔ ∃! p : Fin r × Fin n, ((P p.1).matching p.2).Adj x y := by
  obtain ⟨_,F,P,_,hLe,hOwn,hParts⟩ :=
    partition_regular_residue_with_permutations H r b hReg hLoop coarse hb hSize hLarge
  exact ⟨F,P,hLe,hOwn,hParts⟩

end OverfullWork.DirectedRobustExpansion
