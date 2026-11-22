module

public import OverfullWork.OsthusStadenExactCoreException
public import OverfullWork.OsthusStadenCoreSplitOnRetainedSets

@[expose] public section


/-! The core exceptional construction of §5.6 on the aligned, trimmed layers. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

/-- Only neighbours in the exceptional part are lost from the sum over
the primary cells. -/
theorem ordinary_out_profile_sum_lower
    {V I : Type*} [Fintype V] [Fintype I] (G : Digraph V) (f : V → Option I) (x : V) :
    (outDegree G x:ℝ)-((exceptional f).card:ℝ) ≤
      ∑ i,profileCount (cluster f i) (outProfile G x) := by
  let Q := outProfile G x
  have hSum : profileCount (lift f univ) Q = ∑ i,profileCount (cluster f i) Q :=
    profile_count_disjoint_union univ (cluster f) Q (fun _ _ _ _ h => clusters_disjoint f h)
  have hSub : Q \ exceptional f ⊆ lift f univ ∩ Q := by
    intro y hy
    obtain ⟨hyq,hy0⟩ := mem_sdiff.mp hy
    have hu : y ∈ exceptional f ∪ lift f univ := by rw [exceptional_union_lift]; exact mem_univ _
    exact mem_inter.mpr ⟨(mem_union.mp hu).resolve_left hy0,hyq⟩
  have h := card_le_card_sdiff_add_card (s := Q) (t := exceptional f)
  have h' : Q.card ≤ (lift f univ ∩ Q).card+(exceptional f).card :=
    h.trans (Nat.add_le_add_right (card_le_card hSub) _)
  have hR : (outDegree G x:ℝ) ≤ profileCount (lift f univ) Q+((exceptional f).card:ℝ) := by
    change (Q.card:ℝ) ≤ ((lift f univ ∩ Q).card:ℝ)+((exceptional f).card:ℝ)
    exact_mod_cast h'
  rw [hSum] at hR
  exact sub_le_iff_le_add.mpr hR

theorem half_loss_after_erase {V : Type*}
    (base adapted : Finset V) (x : V) (loss : ℕ)
    (h : (base \ adapted).card ≤ loss) :
    (base \ adapted.erase x).card ≤ loss+1 := by
  have hSub : base \ adapted.erase x ⊆ (base \ adapted) ∪ {x} := by
    intro y hy
    obtain ⟨hyb,hya⟩ := mem_sdiff.mp hy
    by_cases he : y = x
    · exact mem_union_right _ (mem_singleton.mpr he)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hyb,fun ha => hya (mem_erase.mpr ⟨he,ha⟩)⟩)
  exact (card_le_card hSub).trans ((card_union_le _ _).trans (by simpa using Nat.add_le_add_right h 1))

universe u

set_option maxHeartbeats 2400000 in
/-- Construct the core arcs from the base half requests and the actual
trimmed half geometry. Splitting on the retained targets improves the
loss in (26) by the reciprocal of the size of the bank. -/
theorem exists_core_exception_arcs_on_trimmed_layers
    (r s p : ℕ) [NeZero (2*s)] [NeZero p] (hs : 0 < s) (hp : 3 ≤ p) (hpOdd : Odd p)
    (split : ℝ) (hSplit : 0 < split) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type*} [Fintype I]
      {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
      {C : ∀ t a, FactorCycleCoordinates (F t a)}
      (D : PrimaryRedSelection (p := p) C) (G : Digraph V)
      (thin : Fin 5 → Digraph V) (ordinaryPairs : Fin r → I → Digraph V)
      (f : V → Option I) (g : Fin r → V → Option I) (mBase m : ℕ) (εBase τ : ℝ)
      (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin ordinaryPairs))
        (cluster f i) (2*s) p mBase εBase εBase εBase)
      (adapted : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin ordinaryPairs))
        (cluster (g t) i) (2*s) p m τ τ τ)
      (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
      (κ loss : ℕ) (A : ℝ),
      N ≤ Fintype.card V → 0 ≤ εBase → εBase ≤ 1/8 →
      (∀ t (i : PrimaryHalfIndex I (2*s) p),
        ((primaryHalfOfIndex base i) \ primaryHalfOfIndex (adapted t) i).card ≤ loss) →
      (∀ x, f x = none → A ≤ (inDegree G x:ℝ) ∧ A ≤ (outDegree G x:ℝ)) →
      let Z := exceptional f
      let k := exceptionalPhaseBankSize r (2*s) p
      let ℓ := (2*s)*p*2
      let M := ℓ*mBase
      let e := 8*εBase
      let cap := (Z.card:ℝ)/(k:ℝ)+split*(Fintype.card V:ℝ)
      let retained := fun (j : RefinedFactorIndex r (2*s) p) i (z : Fin (2*s)) =>
        (primaryHalfOfIndex (adapted j.1) (i,z,redPhase p j.1.val)).erase (erase j (redPLabel j.1.val i z))
      (κ:ℝ) ≤ ((s-1:ℕ):ℝ)*(1-e)*(A-(Z.card:ℝ)-e*((Fintype.card I:ℝ)*(M:ℝ)))/((ℓ:ℝ)*(k:ℝ)) -
        (Fintype.card I:ℝ)*((s-1:ℕ):ℝ)*(split*(Fintype.card V:ℝ)+((loss+1:ℕ):ℝ)/(k:ℝ)) →
      ∃ E : RefinedFactorIndex r (2*s) p → Digraph V,
        (∀ j, E j ≤ G) ∧ (∀ j j', j ≠ j' → Disjoint (E j) (E j')) ∧
        (∀ j x y, (E j).Adj x y →
          (x ∈ Z ∧ y ∉ Z ∧ ∃ i z, z ∈ D.select true j i ∧ y ∈ retained j i z) ∨
          (y ∈ Z ∧ x ∉ Z ∧ ∃ i z, z ∈ D.select false j i ∧ x ∈ retained j i z)) ∧
        (∀ j x, x ∈ Z → inDegree (E j) x = κ ∧ outDegree (E j) x = κ) ∧
        ∀ j x, x ∉ Z → (inDegree (E j) x:ℝ) ≤ cap ∧ (outDegree (E j) x:ℝ) ≤ cap := by
  have hk : 0 < exceptionalPhaseBankSize r (2*s) p := exceptionalPhaseBankSize_pos (by omega) hp
  obtain ⟨N,hN⟩ := exists_core_exception_phase_pieces_on_retained_sets.{u} split hSplit _ hk
  refine ⟨N,?_⟩
  intro V _ I _ F C D G thin ordinaryPairs f g mBase m εBase τ base adapted erase κ loss A
    hSize hεBase hεBaseOne hNear hDegree Z k ℓ M e cap retained hBudget
  let host (q : Bool) := if q then G else reverseArcs G
  let index (j : RefinedFactorIndex r (2*s) p) (i : I) (z : Fin (2*s)) :
      PrimaryHalfIndex I (2*s) p := (i,z,redPhase p j.1.val)
  let half (j : RefinedFactorIndex r (2*s) p) (i : I) (z : Fin (2*s)) := primaryHalfOfIndex base (index j i z)
  let requests (q : Bool) (i : PrimaryHalfIndex I (2*s) p) :=
    (univ : Finset (RefinedFactorIndex r (2*s) p)).filter
      (fun j => redPhase p j.1.val = i.2.2 ∧ i.2.1 ∈ D.select q j i.1)
  let keep (j : RefinedFactorIndex r (2*s) p) (i : PrimaryHalfIndex I (2*s) p) :=
    (primaryHalfOfIndex (adapted j.1) i).erase (erase j (redPLabel j.1.val i.1 i.2.1))
  have hRequest (q : Bool) (j : RefinedFactorIndex r (2*s) p) (i : I) (z : Fin (2*s))
      (hz : z ∈ D.select q j i) : j ∈ requests q (index j i z) :=
    mem_filter.mpr ⟨mem_univ _,rfl,hz⟩
  choose pieces hPieces hDis hLower hUpper using fun q => hN (host q) Z
    (primaryHalfOfIndex base) (requests q) keep hSize
    (fun _ _ h => primaryHalfOfIndex_disjoint base h)
    (fun i => exists_exceptional_phase_slots D hpOdd q i.1 i.2.1 i.2.2)
  have hHalf (j : RefinedFactorIndex r (2*s) p) (i : I) (z : Fin (2*s)) :
      half j i z ⊆ cluster f i := by
    let pLabel := redPLabel (p := p) j.1.val i z
    exact (primaryHalfCell_subset base pLabel _).trans
      ((((base i).second _).subset _).trans ((base i).first.subset _))
  have hZ (j : RefinedFactorIndex r (2*s) p) (i : I) (z : Fin (2*s))
      (y : V) (hy : y ∈ half j i z) : y ∉ Z := by
    intro h
    have he : (some i : Option I) = none := ((mem_cluster f i y).mp (hHalf j i z hy)).symm.trans
      ((mem_exceptional f y).mp h)
    cases he
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hℓ : 0 < ℓ := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by decide)
  have hcap : 0 ≤ cap := by dsimp only [cap]; positivity
  have hParent (i : I) : (cluster f i).card = M := by
    have h := (base i).first.card_parent
    simpa only [M,ℓ,Fintype.card_fin,Nat.mul_assoc] using h
  have hUniform (q : Bool) (j : RefinedFactorIndex r (2*s) p) (i : I) (z : Fin (2*s)) :
      UniformProfileCell (outProfile (host q)) (cluster f i) (half j i z) ℓ e := by
    let w := (ZMod.finEquiv p).symm (redPhase p j.1.val).1
    let b : Fin 2 := if (redPhase p j.1.val).2 then 1 else 0
    have hh := ((base i).uniform_p_and_half_cells hεBase hεBaseOne z w).2 b
    have he : half j i z = (((base i).halves z w).cells b) := by
      dsimp only [half,index,primaryHalfOfIndex,primaryHalfCell,w,b]
      rw [(ZMod.finEquiv (2*s)).symm_apply_apply]
    rw [he]
    cases q
    · exact hh.inProfile (Sum.inl none)
    · exact hh.outProfile (Sum.inl none)
  let red (q : Bool) (j : RefinedFactorIndex r (2*s) p) (y : V) :=
    ∃ i z, z ∈ D.select q j i ∧ y ∈ retained j i z
  have hLocal (q : Bool) (j : RefinedFactorIndex r (2*s) p) : ∃ E : Digraph V,
      (∀ x y, E.Adj x y → ∃ i z, z ∈ D.select q j i ∧ (pieces q j (index j i z)).Adj x y ∧
        y ∈ retained j i z) ∧
      (∀ x ∈ Z, κ ≤ outDegree E x) ∧ ∀ y, (inDegree E y:ℝ) ≤ cap := by
    obtain ⟨hArc,hLow,hCap⟩ := core_exception_outgoing_with_retained_degrees (host q) Z (cluster f)
      (half j) (retained j) (D.select q j) (fun i z => pieces q j (index j i z))
      (s-1) M ℓ k e (split*(Fintype.card V:ℝ)) (((loss+1:ℕ):ℝ)/(k:ℝ)) cap A
      hℓ hk (by dsimp only [e]; positivity) (by dsimp only [e]; linarith only [hεBaseOne]) hcap
      hParent (D.size q j) (fun i j' hne => by
        apply primaryHalfOfIndex_disjoint base
        intro he
        exact hne (Prod.ext
          (congrArg (fun a : PrimaryHalfIndex I (2*s) p => a.1) he)
          (congrArg (fun a : PrimaryHalfIndex I (2*s) p => a.2.1) he)))
      (fun i z _ => hUniform q j i z)
      (fun i z x y _ h => by
        obtain ⟨_,hG,hZ,hy⟩ := hPieces q j (index j i z) x y h
        exact ⟨hG,hZ,(mem_inter.mp hy).1⟩)
      (fun i z hz x hx => by
        have hDel : (((half j i z \ retained j i z).card):ℝ) ≤ ((loss+1:ℕ):ℝ) := by
          exact_mod_cast half_loss_after_erase _ _ _ loss (hNear j.1 (index j i z))
        have hOverlap := exceptional_overlap_loss (outProfile (host q) x) (half j i z) (retained j i z)
        have hShare := div_le_div_of_nonneg_right (show
          profileCount (half j i z) (outProfile (host q) x)-((loss+1:ℕ):ℝ) ≤
            profileCount (half j i z ∩ retained j i z) (outProfile (host q) x) by
          linarith only [hDel,hOverlap]) hkR.le
        have hP := hLower q j (index j i z) (hRequest q j i z hz) x hx
        change profileCount (half j i z ∩ retained j i z) (outProfile (host q) x)/(k:ℝ) -
          split*(Fintype.card V:ℝ) ≤ (outDegree (pieces q j (index j i z)) x:ℝ) at hP
        have hKeep : retainCoreTargets (pieces q j (index j i z)) (retained j i z) =
            pieces q j (index j i z) := by
          ext u v
          exact ⟨And.left,fun h => ⟨h,(mem_inter.mp (hPieces q j (index j i z) u v h).2.2.2).2⟩⟩
        rw [hKeep]
        rw [sub_div] at hShare
        linarith only [hP,hShare])
      (fun i z hz y hy => by
        by_cases hKeep : y ∈ retained j i z
        swap
        · have hZero : inDegree (pieces q j (index j i z)) y = 0 := by
            unfold inDegree inNeighbours
            apply card_eq_zero.mpr
            apply filter_eq_empty_iff.mpr
            intro x _ h
            exact hKeep (mem_inter.mp (hPieces q j (index j i z) x y h).2.2.2).2
          simpa only [hZero,Nat.cast_zero] using hcap
        have h := hUpper q j (index j i z) (hRequest q j i z hz) y (mem_inter.mpr ⟨hy,hKeep⟩)
        have hSub : profileCount Z (inProfile (host q) y) ≤ (Z.card:ℝ) := by
          unfold profileCount
          exact_mod_cast card_le_card (inter_subset_left)
        have hDiv := div_le_div_of_nonneg_right hSub (Nat.cast_nonneg k : (0:ℝ) ≤ k)
        exact h.trans (add_le_add hDiv le_rfl))
      (fun x hx => by
        have h := hDegree x ((mem_exceptional f x).mp hx)
        have hA : A ≤ (outDegree (host q) x:ℝ) := by cases q <;> first | exact h.1 | exact h.2
        exact (sub_le_sub_right hA _).trans (ordinary_out_profile_sum_lower (host q) f x))
    exact ⟨_,hArc,fun x hx => by exact_mod_cast hBudget.trans (hLow x hx),hCap⟩
  choose supplied hArcs hOut hCap using hLocal
  refine exists_exact_core_exception_arcs G Z red supplied κ cap ?_ hOut hCap ?_
  · intro q j x y h
    obtain ⟨i,z,hz,hP,hy⟩ := hArcs q j x y h
    have hs := (hPieces q j (index j i z) x y hP).2
    exact ⟨hs.2.1,hZ j i z y (mem_inter.mp hs.2.2).1,⟨i,z,hz,hy⟩,by cases q <;> exact hs.1⟩
  · intro q j j' hne
    rw [disjoint_iff_inf_le]
    rintro x y ⟨h,h'⟩
    obtain ⟨i,z,_,hP,_⟩ := hArcs q j x y h
    obtain ⟨i',z',_,hP',_⟩ := hArcs q j' x y h'
    exact disjoint_iff_inf_le.mp (hDis q j (index j i z) j' (index j' i' z')
      (fun he => hne (congrArg Prod.fst he))) ⟨hP,hP'⟩

end OverfullWork.DirectedRobustExpansion
