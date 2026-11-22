module

public import OverfullWork.OsthusStadenTrimmedCopies
public import OverfullWork.DirectedClusterQuotient
public import OverfullWork.RobustReducedFactorization

@[expose] public section


/-! Realize the floor multiplicities of the reduced multidigraph by
actual disjoint regular pairs, and allocate the reduced factors to
distinct physical copies as in Osthus–Staden §5.1. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion DirectedClusterQuotient
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] {I : Type v}

noncomputable def reducedMultiplicity (R : Digraph I) (d : I → I → ℝ) (β : ℝ)
    (i j : I) : ℕ :=
  if R.Adj i j then ⌊d i j / β⌋₊ else 0

abbrev ReducedCopy (M : I → I → ℕ) := Σ ij : I × I, Fin (M ij.1 ij.2)

private theorem uniform_of_cell_coordinates {m : ℕ} (D : Digraph V) (f : V → Option I)
    (a : I → Fin m ↪ V) (ha : ∀ i, (univ : Finset (Fin m)).map (a i) = cluster f i)
    (i j : I) (ε : ℝ) (h : IsUniform D ε (cluster f i) (cluster f j)) :
    IsUniform (pullDirectedPair (a i) (a j) D) ε univ univ := by
  intro A _ B _ hA hB
  rw [density_pullDirectedPair,density_pullDirectedPair,ha,ha]
  apply h
  · rw [←ha i]
    exact map_subset_map.mpr (subset_univ A)
  · rw [←ha j]
    exact map_subset_map.mpr (subset_univ B)
  · rw [←ha i,card_map,card_map]
    exact hA
  · rw [←ha j,card_map,card_map]
    exact hB

/-- The threshold is uniform over the densities and the reduced
digraph. The coordinates of a cluster are reused for every copy. -/
theorem exists_quotient_clone_pairs (K : ℕ) (β ε δ : ℝ)
    (hβ : 0 < β) (hK : 1 ≤ (K:ℝ)*β)
    (hε : 0 ≤ ε) (hSmall : ε ≤ δ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} (D : Digraph V)
      (f : V → Option I) (R : Digraph I) (m : ℕ) (d : I → I → ℝ),
      N ≤ m → (∀ i, (cluster f i).card = m) →
      (∀ i j, R.Adj i j → β ≤ d i j ∧ d i j ≤ 1 ∧
        IsUniform D ε (cluster f i) (cluster f j) ∧
        |density D (cluster f i) (cluster f j)-d i j| ≤ ε) →
      let M := reducedMultiplicity R d β
      ∃ a : I → Fin m ↪ V, ∃ F : ReducedCopy M → Digraph (Fin m),
        (∀ i, (univ : Finset (Fin m)).map (a i) = cluster f i) ∧
        (∀ i x, f (a i x) = some i) ∧
        (∀ e, IsCentredRegular (F e) δ β) ∧
        (∀ e, liftDirectedPair (a e.1.1) (a e.1.2) (F e) ≤ D) ∧
        (∀ e e', e ≠ e' → Disjoint (liftDirectedPair (a e.1.1) (a e.1.2) (F e))
          (liftDirectedPair (a e'.1.1) (a e'.1.2) (F e'))) := by
  obtain ⟨N,hN⟩ := exists_regular_clone_pairs.{0} K β ε δ hβ hK hε hSmall hδ hδ1
  refine ⟨N,?_⟩
  intro V _ I D f R m d hn hSize hR
  let M := reducedMultiplicity R d β
  let e (i : I) := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe,hSize i] :
    Fintype.card ↥(cluster f i) = m)).symm
  let a (i : I) : Fin m ↪ V := (e i).toEmbedding.trans (Function.Embedding.subtype _)
  have ha (i : I) : (univ : Finset (Fin m)).map (a i) = cluster f i := by
    ext x
    constructor
    · rintro hx
      obtain ⟨t,_,rfl⟩ := mem_map.mp hx
      exact (e i t).property
    · intro hx
      obtain ⟨t,ht⟩ := (e i).surjective ⟨x,hx⟩
      exact mem_map.mpr ⟨t,mem_univ _,congrArg Subtype.val ht⟩
  have hTag (i : I) (x : Fin m) : f (a i x) = some i := by
    have hx : a i x ∈ cluster f i := (e i x).property
    exact (mem_filter.mp hx).2
  let pair (i j : I) := pullDirectedPair (a i) (a j) D
  have hLocal (i j : I) : ∃ F : Fin (M i j) → Digraph (Fin m),
      (∀ e, IsCentredRegular (F e) δ β ∧ F e ≤ pair i j) ∧
      ∀ e e', e ≠ e' → Disjoint (F e) (F e') := by
    by_cases hij : R.Adj i j
    · have he : M i j = ⌊d i j / β⌋₊ := if_pos hij
      rw [he]
      obtain ⟨hmin,hmax,hu,hden⟩ := hR i j hij
      have hRegular : IsCentredRegular (pair i j) ε (d i j) := by
        refine ⟨uniform_of_cell_coordinates D f a ha i j ε hu,?_⟩
        change |density (pullDirectedPair (a i) (a j) D) univ univ-d i j| ≤ ε
        rwa [density_pullDirectedPair,ha,ha]
      obtain ⟨F,_,hF,hDis,_,hPart,_⟩ := hN (pair i j) (d i j)
        (by simpa only [Fintype.card_fin] using hn) hRegular hmin hmax
      exact ⟨F,fun e => ⟨hF e,fun x y h => (hPart x y).mpr (Or.inr ⟨e,h⟩)⟩,hDis⟩
    · have he : M i j = 0 := if_neg hij
      rw [he]
      exact ⟨Fin.elim0,fun e => e.elim0,fun e => e.elim0⟩
  choose F hF hDis using hLocal
  let copies (e : ReducedCopy M) := F e.1.1 e.1.2 e.2
  refine ⟨a,copies,ha,hTag,fun e => (hF _ _ _).1,?_,?_⟩
  · rintro e x y ⟨s,t,rfl,rfl,h⟩
    exact (hF _ _ _).2 h
  · rintro ⟨⟨i,j⟩,e⟩ ⟨⟨i',j'⟩,e'⟩ h
    rw [disjoint_iff_inf_le]
    rintro x y ⟨⟨s,t,hs,ht,hst⟩,⟨s',t',hs',ht',hst'⟩⟩
    have hi : i = i' := Option.some.inj
      ((hTag i s).symm.trans ((congrArg f (hs.trans hs'.symm)).trans (hTag i' s')))
    have hj : j = j' := Option.some.inj
      ((hTag j t).symm.trans ((congrArg f (ht.trans ht'.symm)).trans (hTag j' t')))
    subst i'
    subst j'
    have hs₀ := (a i).injective (hs.trans hs'.symm)
    have ht₀ := (a j).injective (ht.trans ht'.symm)
    subst s'
    subst t'
    exact disjoint_iff_inf_le.mp (hDis i j e e' (fun he => h (by subst e'; rfl))) ⟨hst,hst'⟩

/-- Assign one distinct copy to each use of a reduced arc by a factor. -/
theorem exists_factor_copy_assignment (M : I → I → ℕ) {k : ℕ}
    (σ : Fin k → Equiv.Perm I)
    (hCapacity : ∀ i j, ((univ : Finset (Fin k)).filter (fun t => σ t i = j)).card ≤ M i j) :
    ∃ copy : Fin k → I → ReducedCopy M,
      (∀ t i, (copy t i).1 = (i,σ t i)) ∧
      Function.Injective (fun q : Fin k × I => copy q.1 q.2) := by
  let J (i j : I) := (univ : Finset (Fin k)).filter (fun t => σ t i = j)
  let rank (i j : I) : ↥(J i j) ↪ Fin (M i j) :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe (J i j))).toEmbedding.trans (Fin.castLEEmb (hCapacity i j))
  let pick (t : Fin k) (i : I) : ReducedCopy M :=
    ⟨(i,σ t i),rank i (σ t i) ⟨t,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩⟩
  refine ⟨pick,fun _ _ => rfl,?_⟩
  rintro ⟨t,i⟩ ⟨u,j⟩ h
  have hPair : (i,σ t i) = (j,σ u j) := congrArg Sigma.fst h
  have hi : i = j := congrArg Prod.fst hPair
  subst j
  have he : σ t i = σ u i := congrArg Prod.snd hPair
  have hu (v : I) (hv : σ u i = v) :
      pick u i = ⟨(i,v),rank i v ⟨u,mem_filter.mpr ⟨mem_univ _,hv⟩⟩⟩ := by
    subst v
    rfl
  change pick t i = pick u i at h
  rw [hu (σ t i) he.symm] at h
  have hRank := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have ht := congrArg Subtype.val ((rank i (σ t i)).injective hRank)
  exact Prod.ext ht rfl

end OverfullWork.DirectedRegularPairs
