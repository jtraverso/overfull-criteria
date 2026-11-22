module

public import OverfullWork.KuhnOsthusTwoSwitchParity
public import OverfullWork.KuhnOsthusFirstParityPhysical

@[expose] public section


/-! The second and third physical reserves. The former keeps the
other triple matching and the other half of the new C₄ free. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V Z : Type*} [Fintype V]

omit [Fintype V] in
theorem liftOrdinaryCycleArcs_le_original_host {T : Digraph V} {D : Digraph (V ⊕ Z)}
    (hT : T ≤ ordinaryCycleHost D) : liftOrdinaryCycleArcs Z T ≤ D := by
  rintro (x | x) (y | y) h
  · exact hT h
  · exact h.elim
  · exact h.elim
  · exact h.elim

omit [Fintype V] in
private theorem ordinary_lift_disjoint {T : Digraph V} {D L : Digraph (V ⊕ Z)}
    (hT : T ≤ ordinaryCycleHost (D \ L)) :
    Disjoint (liftOrdinaryCycleArcs Z T) L := by
  rw [disjoint_iff_inf_le]
  intro x y h
  exact (liftOrdinaryCycleArcs_le_original_host hT h.1).2 h.2

/-- With one occurrence per exceptional vertex the two marked
bicycles survive the lift to the original graph. -/
theorem TwoSwitchParityFactor.restore_bicycles {D E : Digraph V} {S T U W : Finset V}
    {P : PrescribedSwitchMatching D S T} {Q : PrescribedSwitchMatching D U W}
    (B : TwoSwitchParityFactor (E := E) P Q) {G : Digraph (V ⊕ Z)}
    (L : ProjectedExceptionalArcs G E (id : Z → Z)) :
    let B₀ := liftOrdinaryCycleArcs Z B.factor.ordinary ⊔ L.original
    ∃ σ : Equiv.Perm (V ⊕ Z), (∀ x y, B₀.Adj x y ↔ σ x = y) ∧
      MarkedBicycle σ (.inl (P.source false).val) (.inl (P.source true).val) ∧
      MarkedBicycle σ (.inl (Q.source false).val) (.inl (Q.source true).val) := by
  intro B₀
  have he : restoreExceptionalFactor B.factor.permutation L.source id = B₀ :=
    L.restore_exact _ B.factor.exact_factor B.factor.ordinary_separate
  obtain ⟨σ,hσ⟩ := exists_restored_exceptional_permutation B.factor.permutation L.source
  exact ⟨σ,fun x y => he ▸ hσ x y,
    restoreExceptionallyMarkedBicycle L.source hσ B.triple_bicycle,
    restoreExceptionallyMarkedBicycle L.source hσ B.auxiliary_bicycle⟩

/-- The two reserves chosen after B₁, with their original arc sets
and with the marked cycles required for both exchanges. -/
structure RemainingParityReserves {G E₇ E₁ : Digraph V} {D : Digraph (V ⊕ Z)}
    {S T : Finset V} (K : ParityTripleSwitch G S T) (R : Digraph (V ⊕ Z)) (U W : Finset V)
    (P₇ : ProjectedExceptionalArcs D E₇ (id : Z → Z))
    (P₁ : ProjectedExceptionalArcs D E₁ (id : Z → Z)) where
  auxiliary : ParityAuxiliarySwitch (ordinaryCycleHost R) U W
  second : WindingParityFactor (ordinaryCycleHost R) E₇
  third : WindingParityFactor (ordinaryCycleHost (R \ (liftOrdinaryCycleArcs Z second.ordinary ⊔ P₇.original))) E₁
  second_le : (liftOrdinaryCycleArcs Z second.ordinary ⊔ P₇.original) ≤ D
  third_le : (liftOrdinaryCycleArcs Z third.ordinary ⊔ P₁.original) ≤ D
  disjoint : Disjoint (liftOrdinaryCycleArcs Z second.ordinary ⊔ P₇.original)
    (liftOrdinaryCycleArcs Z third.ordinary ⊔ P₁.original)
  triple_arcs : ∀ l, second.permutation (K.source l).val = ((K.matching 1).target l).val ∧
    third.permutation (K.source l).val = ((K.matching 2).target l).val
  auxiliary_arcs : ∀ l,
    second.permutation (auxiliary.diagonal.source l).val = (auxiliary.diagonal.target l).val ∧
    third.permutation (auxiliary.diagonal.source l).val = (auxiliary.diagonal.target (!l)).val
  triple_bicycles : MarkedBicycle second.permutation (K.source false).val (K.source true).val ∧
    MarkedBicycle third.permutation (K.source false).val (K.source true).val
  auxiliary_bicycles :
    MarkedBicycle second.permutation (auxiliary.diagonal.source false).val (auxiliary.diagonal.source true).val ∧
    MarkedBicycle third.permutation (auxiliary.diagonal.source false).val (auxiliary.diagonal.source true).val
  original_second :
    ∃ σ : Equiv.Perm (V ⊕ Z),
      (∀ x y, (liftOrdinaryCycleArcs Z second.ordinary ⊔ P₇.original).Adj x y ↔ σ x = y) ∧
      MarkedBicycle σ (.inl (K.source false).val) (.inl (K.source true).val) ∧
      MarkedBicycle σ (.inl (auxiliary.diagonal.source false).val) (.inl (auxiliary.diagonal.source true).val)
  original_third :
    ∃ σ : Equiv.Perm (V ⊕ Z),
      (∀ x y, (liftOrdinaryCycleArcs Z third.ordinary ⊔ P₁.original).Adj x y ↔ σ x = y) ∧
      MarkedBicycle σ (.inl (K.source false).val) (.inl (K.source true).val) ∧
      MarkedBicycle σ (.inl (auxiliary.diagonal.source false).val) (.inl (auxiliary.diagonal.source true).val)

/-- Construct B₂ and B₃ successively on the original host. The
coordinates may be rotated so both exceptional intervals end
before the last index of the unwrapped cluster cycle. -/
theorem ParityTripleSwitch.exists_remaining_parity_reserves {G H H' : Digraph V}
    {D R : Digraph (V ⊕ Z)} {k s a c t c' t' m r : ℕ}
    (X : Fin k → Finset V) (hk : 0 < k) (hm : 0 < m) (hRD : R ≤ D)
    (hsa : s+4 ≤ a) (hac : a+4 ≤ c) (hct : c ≤ t) (htt : t ≤ c')
    (hct' : c' ≤ t') (ht'k : t' < k) (hnt' : 3 ≤ k+s-t')
    (hCover : ∀ v, ∃ i, v ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (ε η d z : ℝ) (hε : 0 ≤ ε) (hη : 0 < η) (hη₁ : η ≤ 1) (hz : 0 ≤ z)
    (hGapε : 2*ε < d) (hGapη : 2*η < d) (hd : d ≤ 1)
    (hTol : 2*(ε+z) ≤ η) (hLoss : 1 ≤ z*(((2*m:ℕ):ℝ)*η))
    (hPair : ∀ i, IsLowerSuperregularPair (ordinaryCycleHost R) ε d (X i) (X (finRotate k i)))
    (hr : 0 < r) (hCutε : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ)) (hCutη : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRouteε : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ)))
    (hRouteη : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    let A := cyclicCluster X hk
    ∀ (K : ParityTripleSwitch G (A s) (A (s+1)))
      (E₇ : IntervalPathCover H (clusterIntervalVertices A c t) (A c) (A t))
      (E₁ : IntervalPathCover H' (clusterIntervalVertices A c' t') (A c') (A t'))
      (P₇ : ProjectedExceptionalArcs D E₇.digraph (id : Z → Z))
      (P₁ : ProjectedExceptionalArcs D E₁.digraph (id : Z → Z)),
      (∀ i : Fin 3, i ≠ 0 → ∀ l, R.Adj (.inl (K.source l).val)
        (.inl ((K.matching i).target l).val)) →
      Disjoint R P₁.original →
      Nonempty (RemainingParityReserves K R (A a) (A (a+1)) P₇ P₁) := by
  intro A K E₇ E₁ P₇ P₁ hKeep hReserved
  have hAux : IsLowerSuperregularPair (ordinaryCycleHost R) ε d (A a) (A (a+1)) := by
    change IsLowerSuperregularPair (ordinaryCycleHost R) ε d (A a) (cyclicCluster X hk (a+1))
    rw [cyclicCluster_successor]
    exact hPair _
  obtain ⟨C⟩ := hAux.exists_parity_auxiliary_switch (hSize _) (hSize _) hm hε hGapε hd hr hCutε hRouteε
  let K₂ := (K.matching 1).inHost (G := ordinaryCycleHost R) (fun l => hKeep 1 (by decide) l)
  obtain ⟨Q₂⟩ := exists_two_switch_parity_factor (r := r) X hk hm hsa hac hct
    (by omega) (by omega) hCover hDis hSize hPair hε hGapε hd hr hCutε hRouteε K₂ C.diagonal E₇
  let F₂ := Q₂.factor
  let B₂ := liftOrdinaryCycleArcs Z F₂.ordinary ⊔ P₇.original
  have hExact₂ : restoreExceptionalFactor F₂.permutation P₇.source id = B₂ :=
    P₇.restore_exact _ F₂.exact_factor F₂.ordinary_separate
  let R₂ := R \ B₂
  have hPair₂ (i : Fin k) :
      IsLowerSuperregularPair (ordinaryCycleHost R₂) η d (X i) (X (finRotate k i)) :=
    F₂.residual_pair_after_restore P₇ R _ _ hm (hSize _) (hSize _) ε η d z
      hη hη₁ hz (by linarith) hTol hLoss (hPair i)
  have hUnused {x y : V} (he : R.Adj (.inl x) (.inl y)) (hn : F₂.permutation x ≠ y) :
      (ordinaryCycleHost R₂).Adj x y := by
    refine ⟨he,?_⟩
    intro h
    change B₂.Adj (.inl x) (.inl y) at h
    rw [←hExact₂] at h
    exact hn h.1
  let K₃ := (K.matching 2).inHost (G := ordinaryCycleHost R₂) (fun l => hUnused (hKeep 2 (by decide) l) (by
    have h : F₂.permutation (K.source l).val = ((K.matching 1).target l).val := Q₂.triple_arcs l
    change F₂.permutation (K.source l).val ≠ ((K.matching 2).target l).val
    rw [h]
    intro he
    have h₀ : (K.matching 1).target l = (K.matching 2).target l := Subtype.ext he
    have h₁ := K.target.injective h₀
    cases l
    · exact (by decide : (1 : Fin 3) ≠ 2) h₁
    · exact (by decide : finRotate 3 (1 : Fin 3) ≠ finRotate 3 (2 : Fin 3)) h₁))
  let C₃ : PrescribedSwitchMatching (ordinaryCycleHost R₂) (A a) (A (a+1)) :=
    ⟨C.diagonal.source,⟨fun l => C.diagonal.target (!l),fun l l' he => by
      have h := C.diagonal.target.injective he
      cases l <;> cases l' <;> cases h <;> rfl⟩,fun l => hUnused (C.crossed l) (by
        rw [Q₂.auxiliary_arcs l]
        intro he
        have h := C.diagonal.target.injective (Subtype.ext he)
        cases l <;> cases h)⟩
  obtain ⟨Q₃⟩ := exists_two_switch_parity_factor (r := r) X hk hm hsa (by omega) hct'
    ht'k hnt' hCover hDis hSize hPair₂ hη.le hGapη hd hr hCutη hRouteη K₃ C₃ E₁
  let F₃ := Q₃.factor
  let B₃ := liftOrdinaryCycleArcs Z F₃.ordinary ⊔ P₁.original
  obtain ⟨hOut,hIn⟩ := E₇.disjoint_cyclic_slots hk hDis (by omega) ht'k htt E₁
  have hExc : Disjoint P₇.original P₁.original := P₇.original_disjoint_of_slots P₁ hOut hIn
  have hD₂ : B₂ ≤ D := sup_le ((liftOrdinaryCycleArcs_le_original_host F₂.ordinary_le).trans hRD) P₇.original_le
  have hD₃ : B₃ ≤ D :=
    sup_le ((liftOrdinaryCycleArcs_le_original_host F₃.ordinary_le).trans (fun _ _ h => hRD h.1)) P₁.original_le
  have hDis' : Disjoint B₃ B₂ := disjoint_sup_left.mpr ⟨
    ordinary_lift_disjoint F₃.ordinary_le,
    (disjoint_sup_left.mpr ⟨hReserved.mono_left (liftOrdinaryCycleArcs_le_original_host F₂.ordinary_le),hExc⟩).symm⟩
  exact ⟨⟨C,F₂,F₃,hD₂,hD₃,hDis'.symm,fun l => ⟨Q₂.triple_arcs l,Q₃.triple_arcs l⟩,
    fun l => ⟨Q₂.auxiliary_arcs l,Q₃.auxiliary_arcs l⟩,
    ⟨Q₂.triple_bicycle,Q₃.triple_bicycle⟩,⟨Q₂.auxiliary_bicycle,Q₃.auxiliary_bicycle⟩,
    Q₂.restore_bicycles P₇,Q₃.restore_bicycles P₁⟩⟩

end OverfullWork.DirectedRobustExpansion
