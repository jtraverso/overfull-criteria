module

public import OverfullWork.OsthusStadenAlignedPrimaryRefinements
public import OverfullWork.OsthusStadenAdaptedPrimaryFactors

@[expose] public section


/-! Turn the aligned p-cells into the physical slices of §5.3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u v

/-- Use one refinement for the host, its five thin reserves, and the
main pair of every primary factor. The last family supplies the
profiles needed to preserve superregularity in the slices. -/
def primarySliceGraphs {V I : Type*} {r : ℕ} (G : Digraph V) (thin : Fin 5 → Digraph V)
    (E : Fin r → I → Digraph V) : Option (Fin 5) ⊕ (Fin r × I) → Digraph V
  | .inl none => G
  | .inl (some j) => thin j
  | .inr (t,i) => E t i

noncomputable def primaryPCells {V I J : Type*} [Fintype V] [Fintype I]
    {profiles : J → Finset V} {g : V → Option I} {s p m : ℕ} [NeZero s] [NeZero p]
    {ε₁ ε₂ ε₃ : ℝ} (R : ∀ i, PrimaryNestedRefinement profiles (cluster g i) s p m ε₁ ε₂ ε₃)
    (a : RefinedVertex I s p) : Finset V :=
  ((R a.1.1).second ((ZMod.finEquiv s).symm a.1.2)).cells ((ZMod.finEquiv p).symm a.2)

theorem factor_has_no_fixed_points_of_loopless_multiplicity {I : Type*} {r : ℕ}
    (M : I → I → ℕ) (σ : Fin r → Equiv.Perm I)
    (pick : Fin r → I → ReducedCopy M)
    (hPick : ∀ t i, (pick t i).1 = (i,σ t i)) (hLoop : ∀ i, M i i = 0) :
    ∀ t i, σ t i ≠ i := by
  intro t i he
  have ht := (pick t i).2.isLt
  change (pick t i).2.val < M (pick t i).1.1 (pick t i).1.2 at ht
  have hz : M (pick t i).1.1 (pick t i).1.2 = 0 := by rw [hPick,he,hLoop]
  omega

/-- The combinatorial unwind and the resulting physical slices use
the same labelled p-cells. -/
structure UnwoundPrimarySlices {V : Type u} [Fintype V] {I : Type v} [Fintype I]
    {r s p m : ℕ} [NeZero s] [NeZero p]
    (G : Digraph V) (thin : Fin 5 → Digraph V) (E : Fin r → I → Digraph V)
    (g : Fin r → V → Option I) (σ : Fin r → Equiv.Perm I) (τ η d : ℝ)
    (R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) s p m τ τ τ) where
  first : Fin r → UnwindingLabel s → Equiv.Perm (I × ZMod s)
  coordinates : ∀ t a, FactorCycleCoordinates (first t a)
  factor : RefinedFactorIndex r s p → Equiv.Perm (RefinedVertex I s p)
  label : Fin r → V → Option (RefinedVertex I s p)
  first_proj : ∀ t a x, (first t a x).1 = σ t x.1
  factor_proj : ∀ t a b x, (factor (t,a,b) x).1 = first t a x.1
  separated : ∀ t a a' b b', (a,b) ≠ (a',b') → ∀ x, factor (t,a,b) x ≠ factor (t,a',b') x
  cycles : ∀ t a b x y, (factor (t,a,b)).SameCycle x y ↔ (σ t).SameCycle x.1.1 y.1.1
  distance : ∀ t a b i (x y : Fin ((coordinates t a).length i) × ZMod p) k, 0 < k →
    x.1.val < (coordinates t a).length i-2 → y.1.val < (coordinates t a).length i-2 → x.2 = y.2 →
    ((factor (t,a,b))^k) ((coordinates t a).order ⟨i,x.1⟩,x.2) =
      ((coordinates t a).order ⟨i,y.1⟩,y.2) → p ≤ k
  label_cell : ∀ t x a, label t x = some a ↔ x ∈ primaryPCells (R t) a
  label_exceptional : ∀ t x, label t x = none ↔ g t x = none
  slice_le : ∀ j, unwoundSlice E label factor j ≤ G
  slice_disjoint : ∀ j l, j ≠ l → Disjoint (unwoundSlice E label factor j) (unwoundSlice E label factor l)
  slice_thin_disjoint : ∀ j q, Disjoint (unwoundSlice E label factor j) (thin q)
  size_cells : ∀ t a, (primaryPCells (R t) a).card = 2*m
  superregular : ∀ j a, IsSuperregularPair (unwoundSlice E label factor j) η d
    (primaryPCells (R j.1) a) (primaryPCells (R j.1) (factor j a))

set_option maxHeartbeats 1200000 in
/-- Unwind the reduced factors on the adapted cells and retain the
cycle separation, arc disjointness, and all successor pairs. -/
theorem exists_unwound_primary_slices
    {V : Type u} [Fintype V] {I : Type v} [Fintype I] {r s p m : ℕ}
    (hs : 0 < s) (hp : p.Prime) (hp₂ : 2 < p) [NeZero p] [NeZero (2*s)]
    (G : Digraph V) (thin : Fin 5 → Digraph V) (E : Fin r → I → Digraph V)
    (g : Fin r → V → Option I) (σ : Fin r → Equiv.Perm I)
    (hFixed : ∀ t i, σ t i ≠ i)
    (ε τ η d : ℝ) (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1/8)
    (hFloor : 4*τ ≤ d-ε) (hη : max (2*ε) (ε+4*τ) ≤ η) (hη₁ : η ≤ 1)
    (hScale : (((2*s)*p:ℕ):ℝ)*ε ≤ η)
    (R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ)
    (hLe : ∀ t i, E t i ≤ G)
    (hDis : ∀ t t', t ≠ t' → ∀ i j, Disjoint (E t i) (E t' j))
    (hThin : ∀ t i j, Disjoint (E t i) (thin j))
    (hPair : ∀ t i, IsSuperregularPair (E t i) ε d (cluster (g t) i) (cluster (g t) (σ t i))) :
    Nonempty (UnwoundPrimarySlices G thin E g σ τ η d R) := by
  obtain ⟨F₁,C₂,F₂,hF₁,hF₂,hSep,hCycles,hDist⟩ :=
    exists_two_level_factor_unwinding σ hFixed s p hs hp hp₂
  choose label hLabels hExc using fun t => exists_p_cell_labels (g t) (R t)
  let cells (t : Fin r) (a : RefinedVertex I (2*s) p) := primaryPCells (R t) a
  have hCell (t : Fin r) (a : RefinedVertex I (2*s) p) :
      cells t a ⊆ cluster (g t) a.1.1 ∧
      (cluster (g t) a.1.1).card = ((2*s)*p)*(cells t a).card ∧
      UniformProfileCell (arcProfiles (primarySliceGraphs G thin E))
        (cluster (g t) a.1.1) (cells t a) ((2*s)*p) (4*τ) := by
    let B := R t a.1.1
    let i := (ZMod.finEquiv (2*s)).symm a.1.2
    let j := (ZMod.finEquiv p).symm a.2
    refine ⟨((B.second i).subset j).trans (B.first.subset i),?_,
      (B.uniform_p_and_half_cells hτ hτ₁ i j).1⟩
    change (cluster (g t) a.1.1).card = (2*s*p)*((B.second i).cells j).card
    rw [(B.second i).size j]
    have h := B.first.card_parent
    simpa only [Fintype.card_fin,Nat.mul_assoc] using h
  have hProj (j : RefinedFactorIndex r (2*s) p) (x : RefinedVertex I (2*s) p) :
      (F₂ j x).1.1 = σ j.1 x.1.1 := by
    rcases j with ⟨t,a,b⟩
    exact (congrArg Prod.fst (hF₂ t a b x)).trans (hF₁ t a x.1)
  obtain ⟨hDisjoint,hSuper⟩ := prepared_slices_are_disjoint_and_superregular
    (primarySliceGraphs G thin E) (fun t i => Sum.inr (t,i)) (fun t i => cluster (g t) i)
    cells label σ F₂ ((2*s)*p) ε (4*τ) η d hProj hSep
    hDis hPair hCell (fun t a x => (hLabels t x a).mpr)
    (Nat.mul_pos (by omega) hp.pos) (by positivity) hFloor hη hη₁ hScale
  refine ⟨⟨F₁,C₂,F₂,label,hF₁,hF₂,hSep,hCycles,hDist,hLabels,
    hExc,unwoundSlice_le G E label F₂ hLe,hDisjoint,?_,?_,hSuper⟩⟩
  · intro j q
    rw [disjoint_iff_inf_le]
    rintro x y ⟨⟨a,_,_,ha⟩,hq⟩
    exact disjoint_iff_inf_le.mp (hThin j.1 a.1.1 q) ⟨ha,hq⟩
  · intro t a
    exact ((R t a.1.1).second _).size _

end OverfullWork.DirectedRobustExpansion
