module

public import OverfullWork.KuhnOsthusLemma97Assembly
public import OverfullWork.KuhnOsthusOriginalAbsorptionLink
public import OverfullWork.OsthusStadenTrimmedCopies

@[expose] public section


/-! Use the ordinary complement of the exceptional set as the vertex
type of the residue. The chord pack and the final Hamilton cycles stay
on the ambient vertex set. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling DirectedRegularPairs
open scoped Classical
universe u

/-- The ordinary-first coordinates of the original graph. -/
noncomputable def exceptionalCoordinates {W : Type*} [Fintype W] (Z : Finset W) : (↥Zᶜ ⊕ ↥Z) ≃ W :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun x => by simp))).trans
    (Equiv.sumCompl (fun x : W => x ∈ Zᶜ))

@[simp] theorem exceptionalCoordinates_inl {W : Type*} [Fintype W] (Z : Finset W) (x : ↥Zᶜ) :
    exceptionalCoordinates Z (.inl x) = x.val := rfl

@[simp] theorem exceptionalCoordinates_inr {W : Type*} [Fintype W] (Z : Finset W) (x : ↥Z) :
    exceptionalCoordinates Z (.inr x) = x.val := rfl

/-- Relabel a spanning permutation cycle by an equivalence. -/
theorem spanning_cycle_permCongr {X W : Type*} (e : X ≃ W) (f : Equiv.Perm X)
    (h : HasSpanningCycle (fun x y => f x = y)) :
    HasSpanningCycle (fun x y => (e.permCongr f) x = y) := by
  obtain ⟨T,z,hN,hAll,hHead,hCh⟩ := h
  refine ⟨T.map e,e z,hN.map e.injective,?_,?_,?_⟩
  · intro v
    exact List.mem_map.mpr ⟨e.symm v,hAll _,e.apply_symm_apply v⟩
  · rw [List.head?_map,hHead]
    rfl
  · rw [←List.map_singleton,←List.map_append]
    apply List.isChain_map_of_isChain e _ hCh
    intro a b h
    rw [Equiv.permCongr_apply,e.symm_apply_apply,h]

/-- A residue supported outside the exceptional set is exactly the
lift of its induced graph in the ordinary-first coordinates. -/
theorem pull_ordinary_residue {W : Type*} [Fintype W] (Z : Finset W) (D : Digraph W)
    (hSupp : ∀ x y, D.Adj x y → x ∉ Z ∧ y ∉ Z) :
    let e := (exceptionalCoordinates Z).toEmbedding
    pullDirectedPair e e D = liftOrdinaryCycleArcs (↥Z) (induced D Zᶜ) := by
  intro e
  ext x y
  rcases x with x | x <;> rcases y with y | y
  · rfl
  · exact iff_false_intro fun h => (hSupp x.val y.val h).2 y.prop
  · exact iff_false_intro fun h => (hSupp x.val y.val h).1 x.prop
  · exact iff_false_intro fun h => (hSupp x.val y.val h).1 x.prop

/-- Apply the final partition of Lemma 11.2 to the ambient chord output
of Lemma 9.7. The equality, support and regularity of the ordinary
residue are transferred internally. -/
theorem kuhn_osthus_lemma_11_2_of_ambient_chord_pack {W : Type*} [Fintype W] {k s t : ℕ}
    (Z : Finset W) (c : ↥Zᶜ → Fin k) (A : Digraph W) (C : Fin t → Equiv.Perm W)
    (hC : matchingUnion C ≤ A) (hCycle : ∀ i, HasSpanningCycle (fun x y => C i x = y))
    (hDisC : ∀ i j, i ≠ j → ∀ x, C i x ≠ C j x)
    (hSupport : ∀ x y, (A \ matchingUnion C).Adj x y →
      ∃ a b : ↥Zᶜ, a.val = x ∧ b.val = y ∧ c b = finRotate k (c a))
    (hReg : ∀ v ∉ Z, inDegree (A \ matchingUnion C) v = s ∧
      outDegree (A \ matchingUnion C) v = s)
    (P : Fin s → Digraph (↥Zᶜ ⊕ ↥Z)) (E : Fin s → Fin 7 → Digraph (↥Zᶜ ⊕ ↥Z)) :
    let e := exceptionalCoordinates Z
    let X (i : Fin k) := (univ : Finset ↥Zᶜ).filter (fun x => c x = i)
    (∀ a, AbsorbsWindingFactor X (P a) (E a)) →
    Pairwise (fun a b => Disjoint (P a) (P b)) →
    Disjoint (pullDirectedPair e.toEmbedding e.toEmbedding A) (⨆ a, P a) →
    ∃ F : Fin (t+s*7) → Equiv.Perm W,
      matchingUnion F = A ⊔ liftDirectedPair e.toEmbedding e.toEmbedding (⨆ a, P a) ∧
      (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
      (∀ i, HasSpanningCycle (fun v w => F i v = w)) ∧
      (∀ i : Fin t, F (i.castAdd (s*7)) = C i) ∧
      ∀ a i, liftDirectedPair e.toEmbedding e.toEmbedding (E a i) ≤
        ⟨fun v w => F ((finProdFinEquiv (a,i)).natAdd t) v = w⟩ := by
  intro e X hAbsorb hBlocks hApart
  let A' := pullDirectedPair e.toEmbedding e.toEmbedding A
  let C' (i : Fin t) := e.symm.permCongr (C i)
  let D := A \ matchingUnion C
  have hC' (i : Fin t) (x : ↥Zᶜ ⊕ ↥Z) : e (C' i x) = C i (e x) := e.apply_symm_apply _
  have hCGraph (x y : ↥Zᶜ ⊕ ↥Z) : (matchingUnion C').Adj x y ↔ (matchingUnion C).Adj (e x) (e y) := by
    exact ⟨fun ⟨i,h⟩ => ⟨i,(hC' i x).symm.trans (congrArg e h)⟩,
      fun ⟨i,h⟩ => ⟨i,e.injective ((hC' i x).trans h)⟩⟩
  have hD (x y : W) (h : D.Adj x y) : x ∉ Z ∧ y ∉ Z := by
    obtain ⟨a,b,rfl,rfl,_⟩ := hSupport x y h
    exact ⟨mem_compl.mp a.prop,mem_compl.mp b.prop⟩
  have hId : A' \ matchingUnion C' = liftOrdinaryCycleArcs (↥Z) (induced D Zᶜ) := by
    rw [← pull_ordinary_residue Z D hD]
    ext x y
    change (A.Adj (e x) (e y) ∧ ¬ (matchingUnion C').Adj x y) ↔
      A.Adj (e x) (e y) ∧ ¬ (matchingUnion C).Adj (e x) (e y)
    rw [hCGraph]
  have hNext (i x y) (hx : x ∈ X i) (h : (induced D Zᶜ).Adj x y) :
      y ∈ X (finRotate k i) := by
    obtain ⟨a,b,ha,hb,h⟩ := hSupport x.val y.val h
    rw [show a = x from Subtype.ext ha,show b = y from Subtype.ext hb] at h
    exact mem_filter.mpr ⟨mem_univ _,h.trans (congrArg _ (mem_filter.mp hx).2)⟩
  obtain ⟨F,hF,hDis,hHam,hOld,hKeep⟩ := kuhn_osthus_lemma_11_2_partition_of_original_blocks
    X A' C' (fun x y h => hC ((hCGraph x y).mp h))
    (fun i => spanning_cycle_permCongr e.symm _ (hCycle i))
    (fun i j hij x h => hDisC i j hij (e x) ((hC' i x).symm.trans ((congrArg e h).trans (hC' j x))))
    (induced D Zᶜ) hId (preprocessing_complement_factor D Z s hD hReg) hNext
    P E hAbsorb hBlocks hApart
  let F' (i : Fin (t+s*7)) := e.permCongr (F i)
  have hF' (i : Fin (t+s*7)) (x : ↥Zᶜ ⊕ ↥Z) : F' i (e x) = e (F i x) := by
    simp only [F',Equiv.permCongr_apply,e.symm_apply_apply]
  refine ⟨F',?_,?_,fun i => spanning_cycle_permCongr e _ (hHam i),?_,?_⟩
  · ext x y
    obtain ⟨x,rfl⟩ := e.surjective x
    obtain ⟨y,rfl⟩ := e.surjective y
    have hG : (matchingUnion F').Adj (e x) (e y) ↔ (matchingUnion F).Adj x y := by
      exact ⟨fun ⟨i,h⟩ => ⟨i,e.injective ((hF' i x).symm.trans h)⟩,
        fun ⟨i,h⟩ => ⟨i,(hF' i x).trans (congrArg e h)⟩⟩
    rw [hG,hF]
    constructor
    · rintro (h | h)
      · exact .inl h
      · exact .inr ⟨x,y,rfl,rfl,h⟩
    · rintro (h | ⟨a,b,ha,hb,h⟩)
      · exact .inl h
      · exact .inr ((e.injective ha : a = x) ▸ (e.injective hb : b = y) ▸ h)
  · intro i j hij x h
    obtain ⟨x,rfl⟩ := e.surjective x
    exact hDis i j hij x (e.injective ((hF' i x).symm.trans (h.trans (hF' j x))))
  · intro i
    ext x
    obtain ⟨x,rfl⟩ := e.surjective x
    rw [hF',hOld]
    exact hC' i x
  · rintro a i x y ⟨v,w,rfl,rfl,h⟩
    exact (hF' _ v).trans (congrArg e (hKeep a i h))

/-- Run Lemma 9.7 and then absorb its actual residue by Lemma 10.4.
The free-pair margins and prepared chord rounds are the inputs of
the existing constructive version of Lemma 9.7. -/
theorem kuhn_osthus_lemma_11_2_from_prepared_chord_rounds (ρ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {n : ℕ}
      (B H U E : Digraph W) (Z : Finset W) (c : ↥Zᶜ → Fin (n+1))
      (r f q r₁ r₂ r₃ m K : ℕ) (ε : ℝ),
      let t := r*(f*(n+1))
      let s := r₁+r₂+r-(q-1)*r₃
      let A := (H ⊔ U ⊔ E) ⊔ B
      let X (j : Fin (n+1)) := (univ : Finset ↥Zᶜ).filter (fun v => c v = j)
      let e := (exceptionalCoordinates Z).toEmbedding
      ∀ Q : PreparedChordSystems (H ⊔ U ⊔ E) Z c (finRotate (n+1)) K (Fin r × Fin (f*(n+1))),
      N ≤ m → 0 ≤ ε → ε ≤ ρ/512 → (K:ℝ) ≤ (ρ/512)*(m:ℝ) →
      r*(n+1)*f^2 ≤ m → (16:ℝ) ≤ (ρ/128)^2*(f:ℝ) →
      0 < q → t = q*r₃ →
      (∀ j, (X j).card = m) →
      (∀ j, IsSuperregularPair (induced B Zᶜ) ε ρ (X j) (X (finRotate (n+1) j))) →
      Disjoint (H ⊔ U ⊔ E) B →
      (∀ x y, B.Adj x y → ∃ a b : ↥Zᶜ, a.val = x ∧ b.val = y ∧ c b = finRotate (n+1) (c a)) →
      (∀ v, let d := if v ∈ Z then t else r₁+r₂+r+r₃
        inDegree A v = d ∧ outDegree A v = d) →
      ∀ (P : Fin s → Digraph (↥Zᶜ ⊕ ↥Z)) (L : Fin s → Fin 7 → Digraph (↥Zᶜ ⊕ ↥Z)),
      (∀ a, AbsorbsWindingFactor X (P a) (L a)) →
      Pairwise (fun a b => Disjoint (P a) (P b)) →
      Disjoint (pullDirectedPair e e A) (⨆ a, P a) →
      ∃ F : Fin (t+s*7) → Equiv.Perm W,
        matchingUnion F = A ⊔ liftDirectedPair e e (⨆ a, P a) ∧
        (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
        (∀ i, HasSpanningCycle (fun v w => F i v = w)) ∧
        (∀ i : Fin r × Fin (f*(n+1)), basicExceptionalPathSystem (Q.system i) Z ≤
          basicExceptionalPathSystem
            (matchingUnion (fun _ : Fin 1 => F ((finProdFinEquiv i).castAdd (s*7)))) Z) ∧
        ∀ a i, liftDirectedPair e e (L a i) ≤
          ⟨fun v w => F ((finProdFinEquiv (a,i)).natAdd t) v = w⟩ := by
  obtain ⟨N,hN⟩ := kuhn_osthus_lemma_9_7_of_prepared_rounds.{u} ρ hρ hρ1
  refine ⟨N,?_⟩
  intro W _ n B H U E Z c r f q r₁ r₂ r₃ m K ε t s A X e Q hm hε hη hK hSize hScale
    hq ht hCard hPairs hDis hSupp hDeg P L hAbsorb hBlocks hApart
  obtain ⟨C,hCycle,hDisC,_,hC,hBasic,hD,hNext,hDegree⟩ := hN B H U E Z c r f q r₁ r₂ r₃ m K ε
    Q hm hε hη hK hSize hScale hq ht hCard hPairs hDis hSupp hDeg
  rw [hD] at hNext hDegree
  obtain ⟨F,hF,hDisF,hCycleF,hLeft,hRight⟩ := kuhn_osthus_lemma_11_2_of_ambient_chord_pack
    Z c A C hC hCycle hDisC hNext
    (fun v hv => by simpa only [if_neg hv] using hDegree v) P L hAbsorb hBlocks hApart
  refine ⟨F,hF,hDisF,hCycleF,?_,hRight⟩
  intro i
  simpa only [hLeft] using hBasic i

end OverfullWork.DirectedRobustExpansion
