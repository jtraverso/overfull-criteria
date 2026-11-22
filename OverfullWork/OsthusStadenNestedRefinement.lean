module

public import OverfullWork.OsthusStadenAdaptedRefinement

@[expose] public section


/-! Assemble the refinements of §5.3 on the ambient vertex type. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset UniformSubsetSampling
open scoped Classical
universe u v

structure UniformRefinementOf {V : Type u} {J : Type v} {I : Type*} [Fintype I]
    (profiles : J → Finset V) (P : Finset V) (m : ℕ) (ε : ℝ) where
  cells : I → Finset V
  size : ∀ i, (cells i).card = m
  disjoint : ∀ i j, i ≠ j → Disjoint (cells i) (cells j)
  cover : univ.biUnion cells = P
  uniform : ∀ i, UniformProfileCell profiles P (cells i) (Fintype.card I) ε

theorem UniformRefinementOf.subset {V J I : Type*} [Fintype I]
    {profiles : J → Finset V} {P : Finset V} {m : ℕ} {ε : ℝ}
    (R : UniformRefinementOf (I := I) profiles P m ε) (i : I) : R.cells i ⊆ P := by
  intro v hv
  rw [← R.cover]
  exact mem_biUnion.mpr ⟨i,mem_univ _,hv⟩

theorem UniformRefinementOf.card_parent {V J I : Type*} [Fintype I]
    {profiles : J → Finset V} {P : Finset V} {m : ℕ} {ε : ℝ}
    (R : UniformRefinementOf (I := I) profiles P m ε) : P.card = Fintype.card I*m := by
  rw [← R.cover,card_biUnion (fun i _ j _ h => R.disjoint i j h)]
  simp [R.size]

/-- A profile refinement exists for each prescribed cluster, with a
threshold independent of the ambient vertex set and the profile values. -/
theorem exists_ambient_uniform_refinement (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ N : ℕ, ∀ {V : Type u} {J : Type v} [Fintype J]
      (profiles : J → Finset V) (P : Finset V) (m : ℕ), N ≤ P.card →
      P.card = ℓ*m → (Fintype.card J : ℝ) ≤ C*(P.card : ℝ) →
      Nonempty (UniformRefinementOf (I := Fin ℓ) profiles P m ε) := by
  obtain ⟨N,hN⟩ := exists_uniform_profile_refinement.{u,v} C ε hC hε ℓ hℓ
  refine ⟨N,?_⟩
  intro V J _ profiles P m hP hSize hProfiles
  let X := {v // v ∈ P}
  letI : DecidableEq X := Classical.decEq X
  let restrict (S : Finset V) : Finset X := univ.filter fun v => v.val ∈ S
  let emb : X ↪ V := Function.Embedding.subtype (· ∈ P)
  have hRestr (S : Finset V) : (restrict S).map emb = P ∩ S := by
    ext v
    simp only [restrict,mem_map,mem_filter,mem_univ,true_and,mem_inter]
    constructor
    · rintro ⟨w,hS,rfl⟩
      exact ⟨w.property,hS⟩
    · rintro ⟨hP,hS⟩
      exact ⟨⟨v,hP⟩,hS,rfl⟩
  have hX : Fintype.card X = P.card := Fintype.card_coe _
  obtain ⟨rank,hRank⟩ := hN (fun j => restrict (profiles j)) m
    (by rwa [hX]) (by rwa [hX]) (by rwa [hX])
  let cells (i : Fin ℓ) := (slice rank i).map emb
  have hMem (i : Fin ℓ) (v : V) : v ∈ cells i ↔ ∃ hv : v ∈ P, rank ⟨v,hv⟩ = i := by
    simp only [cells,mem_map,mem_slice]
    constructor
    · rintro ⟨w,hr,rfl⟩
      exact ⟨w.property,hr⟩
    · rintro ⟨hv,hr⟩
      exact ⟨⟨v,hv⟩,hr,rfl⟩
  refine ⟨⟨cells,fun i => (card_map _).trans (hRank i).1,?_,?_,?_⟩⟩
  · intro i j hij
    rw [disjoint_left]
    intro v hvi hvj
    exact hij (((hMem i v).mp hvi).choose_spec.symm.trans ((hMem j v).mp hvj).choose_spec)
  · ext v
    constructor
    · intro hv
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
      exact ((hMem i v).mp hi).choose
    · intro hv
      exact mem_biUnion.mpr ⟨rank ⟨v,hv⟩,mem_univ _,(hMem _ _).mpr ⟨hv,rfl⟩⟩
  · intro i j hj
    have hInter : (slice rank i ∩ restrict (profiles j)).map emb = cells i ∩ profiles j := by
      ext v
      simp only [mem_map,mem_inter,mem_slice,restrict,mem_filter,mem_univ,true_and,hMem]
      constructor
      · rintro ⟨w,⟨hr,hj⟩,rfl⟩
        exact ⟨⟨w.property,hr⟩,hj⟩
      · rintro ⟨⟨hv,hr⟩,hj⟩
        exact ⟨⟨v,hv⟩,⟨hr,hj⟩,rfl⟩
    have hEq : (restrict (profiles j)).card = (P ∩ profiles j).card := by
      rw [← hRestr,card_map]
    have hIR : (slice rank i ∩ restrict (profiles j)).card = (cells i ∩ profiles j).card := by
      rw [← hInter,card_map]
    have h := (hRank i).2 j (by simpa only [hX,hEq,profileCount] using hj)
    rw [hIR,hEq] at h
    simpa only [Fintype.card_fin,profileCount] using h

/-- Compose a uniform refinement with one of its cells at the next
level. The hypotheses explicitly cover the profile-size threshold used
by the second split. -/
theorem UniformRefinementOf.uniform_nested_cell {V J I K : Type*} [Fintype I] [Fintype K]
    {profiles : J → Finset V} {P : Finset V} {m n : ℕ} {ε δ τ : ℝ}
    (R : UniformRefinementOf (I := I) profiles P m ε)
    (i : I) (S : UniformRefinementOf (I := K) profiles (R.cells i) n δ) (j : K)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hτ : ε ≤ τ) (hThreshold : δ ≤ (1-ε)*τ) (hError : ε+δ*(1+ε) ≤ τ) :
    UniformProfileCell profiles P (S.cells j) (Fintype.card I*Fintype.card K) τ := by
  have hP := R.card_parent
  rw [← R.size i] at hP
  letI : Nonempty I := ⟨i⟩
  letI : Nonempty K := ⟨j⟩
  exact (R.uniform i).comp (S.uniform j) Fintype.card_pos Fintype.card_pos hε hε1 hδ
    hP hτ hThreshold hError

/-- Adapt all cells of a prepared refinement to a nearby parent of the
prescribed smaller size. -/
theorem UniformRefinementOf.exists_adapted {V J : Type*} {profiles : J → Finset V}
    {P P' : Finset V} {ℓ m₀ m D : ℕ} {ε ε' : ℝ}
    (R : UniformRefinementOf (I := Fin ℓ) profiles P m₀ ε)
    (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (hε' : 0 ≤ ε') (hGrowth : ε ≤ ε')
    (hSize : P'.card = ℓ*m) (hm : m ≤ m₀)
    (hParent : max (P \ P').card (P' \ P).card ≤ D)
    (hFloor : ε*(P.card : ℝ)+(D : ℝ) ≤ ε'*(P'.card : ℝ))
    (hError : ((D+(m₀-m):ℕ) : ℝ)+(1+ε)*(D : ℝ)/(ℓ : ℝ) ≤
      (ε'-ε)*(ε'*(P'.card : ℝ)/(ℓ : ℝ))) :
    ∃ S : UniformRefinementOf (I := Fin ℓ) profiles P' m ε',
      ∀ i, m-D ≤ (S.cells i ∩ R.cells i).card := by
  have hR (i : Fin ℓ) :
      R.cells i ⊆ P ∧ (R.cells i).card = m₀ ∧ UniformProfileCell profiles P (R.cells i) ℓ ε :=
    ⟨R.subset i,R.size i,by simpa only [Fintype.card_fin] using R.uniform i⟩
  obtain ⟨cells,hCells,hDis,hCover⟩ := exists_adapted_profile_refinement profiles P P'
    ℓ m₀ m D R.cells ε ε' hℓ hε hε' hGrowth hSize hm hParent hR R.disjoint hFloor hError
  refine ⟨⟨cells,fun i => (hCells i).1,hDis,hCover,?_⟩,fun i => (hCells i).2.1⟩
  intro i
  simpa only [Fintype.card_fin] using (hCells i).2.2

end OverfullWork.DirectedRobustExpansion
