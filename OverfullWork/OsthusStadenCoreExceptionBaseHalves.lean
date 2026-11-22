module

public import OverfullWork.OsthusStadenCoreExceptionPhasePieces
public import OverfullWork.OsthusStadenPhysicalRedHalves

@[expose] public section


/-! Assign core exceptional arc pieces to the actual base red halves. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical
universe u

/-- A base half is identified by its primary cluster, intermediate
label, and red phase. -/
abbrev PrimaryHalfIndex (I : Type*) (s p : ℕ) := I × Fin s × (ZMod p × Bool)

noncomputable def primaryHalfOfIndex {V I J : Type*} [Fintype V] [Fintype I]
    {profiles : J → Finset V} {f : V → Option I} {s p m : ℕ} [NeZero s] [NeZero p]
    {ε₁ ε₂ ε₃ : ℝ} (R : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p m ε₁ ε₂ ε₃)
    (j : PrimaryHalfIndex I s p) : Finset V :=
  primaryHalfCell R ((j.1,ZMod.finEquiv s j.2.1),j.2.2.1) j.2.2.2

theorem primaryHalfOfIndex_disjoint {V I J : Type*} [Fintype V] [Fintype I]
    {profiles : J → Finset V} {f : V → Option I} {s p m : ℕ} [NeZero s] [NeZero p]
    {ε₁ ε₂ ε₃ : ℝ} (R : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p m ε₁ ε₂ ε₃)
    {i j : PrimaryHalfIndex I s p} (h : i ≠ j) :
    Disjoint (primaryHalfOfIndex R i) (primaryHalfOfIndex R j) := by
  obtain ⟨label,hLabel,_⟩ := exists_p_cell_labels f R
  let pCell (a : PrimaryHalfIndex I s p) : RefinedVertex I s p :=
    ((a.1,ZMod.finEquiv s a.2.1),a.2.2.1)
  by_cases hp : pCell i = pCell j
  · obtain ⟨u,c,k,b⟩ := i
    obtain ⟨v,c',k',b'⟩ := j
    have huv : u = v := congrArg (fun a => a.1.1) hp
    have hcc : c = c' := (ZMod.finEquiv s).injective (congrArg (fun a => a.1.2) hp)
    have hkk : k = k' := congrArg Prod.snd hp
    subst v
    subst c'
    subst k'
    have hb : b ≠ b' := fun he => h (by subst b'; rfl)
    change Disjoint
      (((R u).halves ((ZMod.finEquiv s).symm (ZMod.finEquiv s c)) ((ZMod.finEquiv p).symm k)).cells
        (if b then 1 else 0))
      (((R u).halves ((ZMod.finEquiv s).symm (ZMod.finEquiv s c)) ((ZMod.finEquiv p).symm k)).cells
        (if b' then 1 else 0))
    apply ((R u).halves _ _).disjoint
    cases b <;> cases b' <;> first | contradiction | decide
  · apply disjoint_left.mpr
    intro x hi hj
    have hI : x ∈ primaryPCells R (pCell i) := primaryHalfCell_subset R _ _ hi
    have hJ : x ∈ primaryPCells R (pCell j) := primaryHalfCell_subset R _ _ hj
    exact hp (Option.some.inj (((hLabel x _).mpr hI).symm.trans ((hLabel x _).mpr hJ)))

/-- On one direction, assign the split pieces to the actual red
requests of the base halves. For arcs directed toward the core,
apply this statement to the reversed graph. -/
theorem exists_core_exception_pieces_on_base_halves
    (ε : ℝ) (hε : 0 < ε) (r s p : ℕ) [NeZero (2*s)] [NeZero p]
    (hs : 0 < s) (hp : 3 ≤ p) (hpOdd : Odd p) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I J : Type*} [Fintype I]
      {profiles : J → Finset V} {f : V → Option I} {m : ℕ} {τ : ℝ}
      {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
      {C : ∀ t a, FactorCycleCoordinates (F t a)}
      (D : PrimaryRedSelection (p := p) C) (R : ∀ i,
        PrimaryNestedRefinement profiles (cluster f i) (2*s) p m τ τ τ)
      (G : Digraph V) (Z : Finset V) (dir : Bool), N ≤ Fintype.card V →
      let k := exceptionalPhaseBankSize r (2*s) p
      let half := primaryHalfOfIndex R
      let requested := fun (j : RefinedFactorIndex r (2*s) p) (i : PrimaryHalfIndex I (2*s) p) =>
        redPhase p j.1.val = i.2.2 ∧ i.2.1 ∈ D.select dir j i.1
      ∃ pieces : RefinedFactorIndex r (2*s) p → PrimaryHalfIndex I (2*s) p → Digraph V,
        (∀ j i x y, (pieces j i).Adj x y → requested j i ∧ G.Adj x y ∧ x ∈ Z ∧ y ∈ half i) ∧
        (∀ j i l q, (j,i) ≠ (l,q) → Disjoint (pieces j i) (pieces l q)) ∧
        (∀ j i, requested j i → ∀ x ∈ Z,
          profileCount (half i) (outProfile G x)/(k:ℝ)-ε*(Fintype.card V:ℝ) ≤ (outDegree (pieces j i) x:ℝ)) ∧
        ∀ j i, requested j i → ∀ y ∈ half i,
          (inDegree (pieces j i) y:ℝ) ≤ profileCount Z (inProfile G y)/(k:ℝ)+ε*(Fintype.card V:ℝ) := by
  let k := exceptionalPhaseBankSize r (2*s) p
  have hk : 0 < k := exceptionalPhaseBankSize_pos (by omega) hp
  obtain ⟨N,hN⟩ := exists_core_exception_phase_pieces.{u} ε hε k hk
  refine ⟨N,?_⟩
  intro V _ I J _ profiles f m τ F C D R G Z dir hSize
  let requests (i : PrimaryHalfIndex I (2*s) p) :=
    (univ : Finset (RefinedFactorIndex r (2*s) p)).filter
      (fun j => redPhase p j.1.val = i.2.2 ∧ i.2.1 ∈ D.select dir j i.1)
  obtain ⟨pieces,hSupport,hDis,hOut,hIn⟩ := hN G Z (primaryHalfOfIndex R) requests hSize
    (fun _ _ h => primaryHalfOfIndex_disjoint R h)
    (fun i => exists_exceptional_phase_slots D hpOdd dir i.1 i.2.1 i.2.2)
  refine ⟨pieces,?_,hDis,?_,?_⟩
  · intro j i x y h
    exact ⟨(mem_filter.mp (hSupport j i x y h).1).2,(hSupport j i x y h).2⟩
  · intro j i hr
    exact hOut j i (mem_filter.mpr ⟨mem_univ _,hr⟩)
  · intro j i hr
    exact hIn j i (mem_filter.mpr ⟨mem_univ _,hr⟩)

end OverfullWork.DirectedRobustExpansion
