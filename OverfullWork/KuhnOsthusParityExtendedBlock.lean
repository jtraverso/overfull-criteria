module

public import OverfullWork.KuhnOsthusOriginalParityRound

@[expose] public section


/-! A physical parity extension of a constructed cycle absorber,
including the original exceptional covers of I₆, I₇, and I₁. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V Z : Type*}

/-- The original ordinary edges of a restored cover are among the
arcs of its projected permutation. -/
theorem ProjectedExceptionalArcs.ordinary_projection_le
    {D : Digraph (V ⊕ Z)} {E O : Digraph V} (P : ProjectedExceptionalArcs D E (id : Z → Z))
    (σ : Equiv.Perm V) (hσ : ∀ x y, (O ⊔ E).Adj x y ↔ σ x = y)
    (hSep : ∀ {x y}, O.Adj x y → ¬ E.Adj x y) :
    ∀ {x y : V}, (liftOrdinaryCycleArcs Z O ⊔ P.original).Adj (.inl x) (.inl y) → σ x = y := by
  intro x y h
  rw [← P.restore_exact σ hσ hSep] at h
  exact h.1

/-- Assemble a physical parity block from the original cycle absorber
and its three reserves. The six projected factors bound the ordinary
arcs used by the whole block. -/
theorem RemainingParityReserves.assemble_original_parity_block
    {D R L : Digraph (V ⊕ Z)} {E₆ E₇ E₁ : Digraph V} {S T U W : Finset V}
    (Q : FirstParityReserve (ordinaryCycleHost R) E₆ S T)
    (P₆ : ProjectedExceptionalArcs D E₆ (id : Z → Z))
    (P₇ : ProjectedExceptionalArcs D E₇ (id : Z → Z))
    (P₁ : ProjectedExceptionalArcs D E₁ (id : Z → Z))
    (F : Fin 3 → Equiv.Perm V) (hL : L ≤ D) (hProj : ordinaryCycleHost L ≤ matchingUnion F)
    (hR : R ≤ D) (hRL : Disjoint R L) (h₆ : Disjoint P₆.original L)
    (h₇ : Disjoint P₇.original L) (h₁ : Disjoint P₁.original L) :
    let B₁ := liftOrdinaryCycleArcs Z Q.factor.ordinary ⊔ P₆.original
    ∀ (B : RemainingParityReserves Q.triple (R \ B₁) U W P₇ P₁),
      let B₂ := liftOrdinaryCycleArcs Z B.second.ordinary ⊔ P₇.original
      let B₃ := liftOrdinaryCycleArcs Z B.third.ordinary ⊔ P₁.original
      Disjoint (B₂ ⊔ B₃) B₁ →
      let M : Fin 6 → Equiv.Perm V :=
        ![F 0,F 1,F 2,Q.factor.permutation,B.second.permutation,B.third.permutation]
      (L ⊔ B₁ ⊔ B₂ ⊔ B₃) ≤ D ∧
      Disjoint (B₁ ⊔ B₂ ⊔ B₃) L ∧ Disjoint B₁ B₂ ∧ Disjoint B₁ B₃ ∧ Disjoint B₂ B₃ ∧
      ordinaryCycleHost (L ⊔ B₁ ⊔ B₂ ⊔ B₃) ≤ matchingUnion M := by
  intro B₁ B B₂ B₃ hLater M
  have hOrd : liftOrdinaryCycleArcs Z Q.factor.ordinary ≤ R := liftOrdinaryCycleArcs_le_original_host Q.factor.ordinary_le
  have hB₁ : B₁ ≤ D := sup_le (hOrd.trans hR) P₆.original_le
  have hRest := B.disjoint_used (hRL.mono_left (fun _ _ h => h.1)) h₇ h₁
  have hB₁L : Disjoint B₁ L := disjoint_sup_left.mpr ⟨hRL.mono_left hOrd,h₆⟩
  have hProj' : ordinaryCycleHost (L ⊔ B₁ ⊔ B₂ ⊔ B₃) ≤ matchingUnion M := by
    intro x y h
    change (L ⊔ B₁ ⊔ B₂ ⊔ B₃).Adj (.inl x) (.inl y) at h
    rcases h with ((h | h) | h) | h
    · obtain ⟨i,hi⟩ := hProj h
      fin_cases i
      · exact ⟨0,hi⟩
      · exact ⟨1,hi⟩
      · exact ⟨2,hi⟩
    · exact ⟨3,P₆.ordinary_projection_le _ Q.factor.exact_factor Q.factor.ordinary_separate h⟩
    · exact ⟨4,P₇.ordinary_projection_le _ B.second.exact_factor B.second.ordinary_separate h⟩
    · exact ⟨5,P₁.ordinary_projection_le _ B.third.exact_factor B.third.ordinary_separate h⟩
  obtain ⟨hB₂L,hB₃L⟩ := disjoint_sup_left.mp hRest
  exact ⟨sup_le (sup_le (sup_le hL hB₁) B.second_le) B.third_le,
    disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨hB₁L,hB₂L⟩,hB₃L⟩,
    (disjoint_sup_left.mp hLater).1.symm,(disjoint_sup_left.mp hLater).2.symm,B.disjoint,hProj'⟩

/-- The original parity extension of a fixed projected cycle absorber.
Its original parts are edge-disjoint, and the ordinary projection
of the entire block is covered by its six permutation factors. -/
theorem NormalizedCycleAbsorber.exists_original_parity_extension_with_absorption
    {D R : Digraph (V ⊕ Z)} {H H₆ H₇ H₁ : Digraph V} [Fintype V] {q m r : ℕ}
    (X : Fin (14*q) → Finset V) (hq : 15 ≤ q) (hm : 0 < m) (hRD : R ≤ D)
    (hCover : ∀ v, ∃ i, v ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (ε₀ ε₁ ε₂ ε₃ d z : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hε₃ : 0 < ε₃)
    (h₁ : ε₁ ≤ 1) (h₂ : ε₂ ≤ 1) (h₃ : ε₃ ≤ 1) (hz : 0 ≤ z)
    (hG₁ : 2*ε₁ < d) (hG₂ : 2*ε₂ < d) (hG₃ : 2*ε₃ < d) (hd : d ≤ 1)
    (hT₁ : 2*(ε₀+z) ≤ ε₁) (hL₁ : 3 ≤ z*(((2*m:ℕ):ℝ)*ε₁))
    (hT₂ : 2*(ε₁+z) ≤ ε₂) (hL₂ : 1 ≤ z*(((2*m:ℕ):ℝ)*ε₂))
    (hT₃ : 2*(ε₂+z) ≤ ε₃) (hL₃ : 1 ≤ z*(((2*m:ℕ):ℝ)*ε₃))
    (hPair : ∀ i, IsLowerSuperregularPair (ordinaryCycleHost R) ε₀ d (X i) (X (finRotate (14*q) i)))
    (hr : 0 < r) (hCut₁ : ((2*m:ℕ):ℝ)*ε₁ ≤ (r:ℝ))
    (hCut₂ : ((2*m:ℕ):ℝ)*ε₂ ≤ (r:ℝ)) (hCut₃ : ((2*m:ℕ):ℝ)*ε₃ ≤ (r:ℝ))
    (hRoute₁ : 28*((r:ℝ)+1) < (d-2*ε₁)^14*((d-ε₁)*((2*m:ℕ):ℝ)))
    (hRoute₂ : 28*((r:ℝ)+1) < (d-2*ε₂)^14*((d-ε₂)*((2*m:ℕ):ℝ)))
    (hRoute₃ : 28*((r:ℝ)+1) < (d-2*ε₃)^14*((d-ε₃)*((2*m:ℕ):ℝ))) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
    ∀ {E : CycleAbsorberExceptionalCovers H A q}
      {eTop : Fin (2*m) ≃ A 0} {eLow : Fin (2*m) ≃ B 0}
      (N : NormalizedCycleAbsorber (G := ordinaryCycleHost R \ E.arcs) E eTop eLow)
      {P₂ : ProjectedExceptionalArcs D E.second.digraph (id : Z → Z)}
      {P₃ : ProjectedExceptionalArcs D E.third.digraph (id : Z → Z)}
      {P₄ : ProjectedExceptionalArcs D E.fourth.digraph (id : Z → Z)}
      {P₅ : ProjectedExceptionalArcs D E.fifth.digraph (id : Z → Z)}
      (_hC : CycleAbsorberOriginalConclusion N D P₂ P₃ P₄ P₅)
      (E₆ : IntervalPathCover H₆ (clusterIntervalVertices A (10*q) (12*q)) (A (10*q)) (A (12*q)))
      (E₇ : IntervalPathCover H₇ (clusterIntervalVertices A (12*q) (14*q)) (A (12*q)) (A (14*q)))
      (E₁ : IntervalPathCover H₁ (clusterIntervalVertices A 0 (2*q)) (A 0) (A (2*q)))
      (P₆ : ProjectedExceptionalArcs D E₆.digraph (id : Z → Z))
      (P₇ : ProjectedExceptionalArcs D E₇.digraph (id : Z → Z))
      (P₁ : ProjectedExceptionalArcs D E₁.digraph (id : Z → Z)),
      Disjoint R P₆.original → Disjoint R P₇.original → Disjoint R P₁.original →
      let F := liftOrdinaryCycleArcs Z N.mainOrdinary ⊔ (P₃.original ⊔ P₅.original)
      let U := liftOrdinaryCycleArcs Z N.upper.ordinary ⊔ P₄.original
      let W := liftOrdinaryCycleArcs Z N.lower.ordinary ⊔ P₂.original
      let L := F ⊔ U ⊔ W
      let R' := R \ L
      ∃ (B₁ B₂ B₃ : Digraph (V ⊕ Z)) (M : Fin 6 → Equiv.Perm V),
        (L ⊔ B₁ ⊔ B₂ ⊔ B₃) ≤ D ∧
        Disjoint (B₁ ⊔ B₂ ⊔ B₃) L ∧ Disjoint B₁ B₂ ∧ Disjoint B₁ B₃ ∧ Disjoint B₂ B₃ ∧
        P₆.original ≤ B₁ ∧ P₇.original ≤ B₂ ∧ P₁.original ≤ B₃ ∧
        (B₁ ⊔ B₂ ⊔ B₃) ≤ liftOrdinaryCycleArcs Z (ordinaryCycleHost R') ⊔
          (P₆.original ⊔ P₇.original ⊔ P₁.original) ∧
        ordinaryCycleHost (L ⊔ B₁ ⊔ B₂ ⊔ B₃) ≤ matchingUnion M ∧
        (∀ T₀ T₁ : Equiv.Perm V, Nonempty (ParityRepairConfiguration
          ![T₀,T₁,M 1,M 2,M 3,M 4,M 5])) ∧
        AbsorbsWindingFactor X (L ⊔ B₁ ⊔ B₂ ⊔ B₃)
          ![P₃.original,P₅.original,P₄.original,P₂.original,P₆.original,P₇.original,P₁.original] := by
  intro hk A B E eTop eLow N P₂ P₃ P₄ P₅ hC E₆ E₇ E₁ P₆ P₇ P₁ hR₆ hR₇ hR₁ F U W L R'
  obtain ⟨Q,hQ,hQDis,hQ₀,hQ₁,_,_⟩ := NormalizedCycleAbsorber.exists_first_parity_reserve
    (r := r) X hq hm hRD hCover hDis hSize hPair hε₁ h₁ hz hG₁ hd hT₁ hL₁
    hr hCut₁ hRoute₁ N hC E₆ P₆ hR₆
  have hR' : R' ≤ R := fun _ _ he => he.1
  have hPair' (i : Fin (14*q)) :
      IsLowerSuperregularPair (ordinaryCycleHost R') ε₁ d (X i) (X (finRotate (14*q) i)) :=
    hC.residual_pair R _ _ hm (hSize _) (hSize _) ε₀ ε₁ d z hε₁ h₁ hz (by linarith) hT₁ hL₁ (hPair i)
  obtain ⟨T,hTDis⟩ := FirstParityReserve.exists_remaining_after_original (r := r)
    X hq hm (hR'.trans hRD) hCover hDis hSize ε₁ ε₂ ε₃ d z hε₂ h₂ hε₃ h₃ hz
    hG₂ hG₃ hd hT₂ hL₂ hT₃ hL₃ hPair' hr hCut₂ hCut₃ hRoute₂ hRoute₃
    E₆ Q E₇ E₁ P₆ P₇ P₁ (hR₇.mono_left hR') (hR₁.mono_left hR')
  let B₁ := liftOrdinaryCycleArcs Z Q.factor.ordinary ⊔ P₆.original
  let B₂ := liftOrdinaryCycleArcs Z T.second.ordinary ⊔ P₇.original
  let B₃ := liftOrdinaryCycleArcs Z T.third.ordinary ⊔ P₁.original
  let M : Fin 6 → Equiv.Perm V := ![N.mainPermutation,N.upper.permutation,N.lower.permutation,
    Q.factor.permutation,T.second.permutation,T.third.permutation]
  have hR'Dis : Disjoint R' L := by
    rw [disjoint_iff_inf_le]
    intro x y h
    exact h.1.2 h.2
  have hF : N.mainOrdinary ≤ ordinaryCycleHost R :=
    sup_le (sup_le N.top.paths.unionPaths_le N.topTail.unionPaths_le)
      (sup_le N.low.paths.unionPaths_le N.lowTail.unionPaths_le) |>.trans (fun _ _ h => h.1)
  have hU : N.upper.ordinary ≤ ordinaryCycleHost R :=
    N.upper.ordinary_le.trans (fun _ _ h => h.1.1)
  have hW : N.lower.ordinary ≤ ordinaryCycleHost R := N.lower_le.trans (fun _ _ h => h.1)
  have exc₇ {b c : ℕ} (J : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c))
      (P : ProjectedExceptionalArcs D J.digraph (id : Z → Z)) (hc : c ≤ 12*q) :
      Disjoint P.original P₇.original := by
    obtain ⟨hOut,hIn⟩ := J.disjoint_cyclic_slots_at_wrap hk hDis (by omega) le_rfl hc E₇
    exact P.original_disjoint_of_slots P₇ hOut hIn
  have exc₁ {b c : ℕ} (J : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c))
      (P : ProjectedExceptionalArcs D J.digraph (id : Z → Z)) (hb : 2*q ≤ b) (hc : c < 14*q) :
      Disjoint P.original P₁.original := by
    obtain ⟨hOut,hIn⟩ := E₁.disjoint_cyclic_slots hk hDis (by omega) hc hb J
    exact (P₁.original_disjoint_of_slots P hOut hIn).symm
  have hL₇ : Disjoint P₇.original L := (disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨
      disjoint_sup_left.mpr ⟨hR₇.mono_left (liftOrdinaryCycleArcs_le_original_host hF),
        disjoint_sup_left.mpr ⟨exc₇ E.third P₃ (by omega),exc₇ E.fifth P₅ (by omega)⟩⟩,
      disjoint_sup_left.mpr ⟨hR₇.mono_left (liftOrdinaryCycleArcs_le_original_host hU),exc₇ E.fourth P₄ (by omega)⟩⟩,
    disjoint_sup_left.mpr ⟨hR₇.mono_left (liftOrdinaryCycleArcs_le_original_host hW),exc₇ E.second P₂ (by omega)⟩⟩).symm
  have hL₁ : Disjoint P₁.original L := (disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨
      disjoint_sup_left.mpr ⟨hR₁.mono_left (liftOrdinaryCycleArcs_le_original_host hF),
        disjoint_sup_left.mpr ⟨exc₁ E.third P₃ (by omega) (by omega),exc₁ E.fifth P₅ (by omega) (by omega)⟩⟩,
      disjoint_sup_left.mpr ⟨hR₁.mono_left (liftOrdinaryCycleArcs_le_original_host hU),exc₁ E.fourth P₄ (by omega) (by omega)⟩⟩,
    disjoint_sup_left.mpr ⟨hR₁.mono_left (liftOrdinaryCycleArcs_le_original_host hW),exc₁ E.second P₂ le_rfl (by omega)⟩⟩).symm
  have hL₆ : Disjoint P₆.original L := hQDis.mono_left (show P₆.original ≤ B₁ from le_sup_right)
  let F₀ : Fin 3 → Equiv.Perm V := ![N.mainPermutation,N.upper.permutation,N.lower.permutation]
  have hOld : ordinaryCycleHost L ≤ matchingUnion F₀ := by
    intro x y h
    have hp := hC.2.2.2.2.2.2.1 x y h
    rcases hp with (hf | hu) | hw
    · exact ⟨0,(N.exact_main _ _).mp hf⟩
    · exact ⟨1,(N.upper.exact_factor _ _).mp hu⟩
    · rw [←N.second_arcs] at hw
      exact ⟨2,(N.lower.exact_factor _ _).mp hw⟩
  have hL : L ≤ D := sup_le (sup_le hC.1 hC.2.1) hC.2.2.1
  obtain ⟨hAll,hLD,h12,h13,h23,hBound⟩ := RemainingParityReserves.assemble_original_parity_block Q
    P₆ P₇ P₁ F₀ hL hOld (hR'.trans hRD) hR'Dis hL₆ hL₇ hL₁ T hTDis
  have hO₁ : Q.factor.ordinary ≤ ordinaryCycleHost R' := Q.factor.ordinary_le
  have hO₂ : T.second.ordinary ≤ ordinaryCycleHost R' :=
    T.second.ordinary_le.trans (fun _ _ h => h.1)
  have hO₃ : T.third.ordinary ≤ ordinaryCycleHost R' :=
    T.third.ordinary_le.trans (fun _ _ h => h.1.1)
  have hOrdLift {A : Digraph V} (hA : A ≤ ordinaryCycleHost R') :
      liftOrdinaryCycleArcs Z A ≤ liftOrdinaryCycleArcs Z (ordinaryCycleHost R') := by
    rintro (x | x) (y | y) h
    · exact hA h
    · exact h.elim
    · exact h.elim
    · exact h.elim
  have hSupport : (B₁ ⊔ B₂ ⊔ B₃) ≤ liftOrdinaryCycleArcs Z (ordinaryCycleHost R') ⊔
      (P₆.original ⊔ P₇.original ⊔ P₁.original) := by
    intro x y h
    rcases h with ((h | h) | (h | h)) | (h | h)
    · exact .inl (hOrdLift hO₁ h)
    · exact .inr (.inl (.inl h))
    · exact .inl (hOrdLift hO₂ h)
    · exact .inr (.inl (.inr h))
    · exact .inl (hOrdLift hO₃ h)
    · exact .inr (.inr h)
  refine ⟨B₁,B₂,B₃,M,hAll,hLD,h12,h13,h23,le_sup_right,le_sup_right,le_sup_right,hSupport,hBound,?_,?_⟩
  · intro T₀ T₁
    apply T.parity_repair_configuration Q T₀ T₁ N.upper.permutation N.lower.permutation
    · intro l
      rw [(hQ₀ l).2,(hQ₀ (!l)).1]
    · intro l
      rw [(hQ₁ l).2,(hQ₁ (!l)).1]
  · intro inst σ hNext Rσ hSep
    have he : L ⊔ B₁ ⊔ B₂ ⊔ B₃ = L ⊔ (B₁ ⊔ B₂ ⊔ B₃) := by ac_rfl
    rw [he] at hSep ⊢
    exact NormalizedCycleAbsorber.absorb_winding_factor X hq hm hCover hDis hSize σ hNext
      N P₂ P₃ P₄ P₅ hC E₆ E₇ E₁ P₆ P₇ P₁ Q T hQ₀ hQ₁ hLD h12 h13 hSep

/-- The original construction, with the six projected factors and the
parity configuration for arbitrary primary factors. -/
theorem NormalizedCycleAbsorber.exists_original_parity_extension
    {D R : Digraph (V ⊕ Z)} {H H₆ H₇ H₁ : Digraph V} [Fintype V] {q m r : ℕ}
    (X : Fin (14*q) → Finset V) (hq : 15 ≤ q) (hm : 0 < m) (hRD : R ≤ D)
    (hCover : ∀ v, ∃ i, v ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (ε₀ ε₁ ε₂ ε₃ d z : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hε₃ : 0 < ε₃)
    (h₁ : ε₁ ≤ 1) (h₂ : ε₂ ≤ 1) (h₃ : ε₃ ≤ 1) (hz : 0 ≤ z)
    (hG₁ : 2*ε₁ < d) (hG₂ : 2*ε₂ < d) (hG₃ : 2*ε₃ < d) (hd : d ≤ 1)
    (hT₁ : 2*(ε₀+z) ≤ ε₁) (hL₁ : 3 ≤ z*(((2*m:ℕ):ℝ)*ε₁))
    (hT₂ : 2*(ε₁+z) ≤ ε₂) (hL₂ : 1 ≤ z*(((2*m:ℕ):ℝ)*ε₂))
    (hT₃ : 2*(ε₂+z) ≤ ε₃) (hL₃ : 1 ≤ z*(((2*m:ℕ):ℝ)*ε₃))
    (hPair : ∀ i, IsLowerSuperregularPair (ordinaryCycleHost R) ε₀ d (X i) (X (finRotate (14*q) i)))
    (hr : 0 < r) (hCut₁ : ((2*m:ℕ):ℝ)*ε₁ ≤ (r:ℝ))
    (hCut₂ : ((2*m:ℕ):ℝ)*ε₂ ≤ (r:ℝ)) (hCut₃ : ((2*m:ℕ):ℝ)*ε₃ ≤ (r:ℝ))
    (hRoute₁ : 28*((r:ℝ)+1) < (d-2*ε₁)^14*((d-ε₁)*((2*m:ℕ):ℝ)))
    (hRoute₂ : 28*((r:ℝ)+1) < (d-2*ε₂)^14*((d-ε₂)*((2*m:ℕ):ℝ)))
    (hRoute₃ : 28*((r:ℝ)+1) < (d-2*ε₃)^14*((d-ε₃)*((2*m:ℕ):ℝ))) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
    ∀ {E : CycleAbsorberExceptionalCovers H A q}
      {eTop : Fin (2*m) ≃ A 0} {eLow : Fin (2*m) ≃ B 0}
      (N : NormalizedCycleAbsorber (G := ordinaryCycleHost R \ E.arcs) E eTop eLow)
      {P₂ : ProjectedExceptionalArcs D E.second.digraph (id : Z → Z)}
      {P₃ : ProjectedExceptionalArcs D E.third.digraph (id : Z → Z)}
      {P₄ : ProjectedExceptionalArcs D E.fourth.digraph (id : Z → Z)}
      {P₅ : ProjectedExceptionalArcs D E.fifth.digraph (id : Z → Z)}
      (_hC : CycleAbsorberOriginalConclusion N D P₂ P₃ P₄ P₅)
      (E₆ : IntervalPathCover H₆ (clusterIntervalVertices A (10*q) (12*q)) (A (10*q)) (A (12*q)))
      (E₇ : IntervalPathCover H₇ (clusterIntervalVertices A (12*q) (14*q)) (A (12*q)) (A (14*q)))
      (E₁ : IntervalPathCover H₁ (clusterIntervalVertices A 0 (2*q)) (A 0) (A (2*q)))
      (P₆ : ProjectedExceptionalArcs D E₆.digraph (id : Z → Z))
      (P₇ : ProjectedExceptionalArcs D E₇.digraph (id : Z → Z))
      (P₁ : ProjectedExceptionalArcs D E₁.digraph (id : Z → Z)),
      Disjoint R P₆.original → Disjoint R P₇.original → Disjoint R P₁.original →
      let F := liftOrdinaryCycleArcs Z N.mainOrdinary ⊔ (P₃.original ⊔ P₅.original)
      let U := liftOrdinaryCycleArcs Z N.upper.ordinary ⊔ P₄.original
      let W := liftOrdinaryCycleArcs Z N.lower.ordinary ⊔ P₂.original
      let L := F ⊔ U ⊔ W
      let R' := R \ L
      ∃ (B₁ B₂ B₃ : Digraph (V ⊕ Z)) (M : Fin 6 → Equiv.Perm V),
        (L ⊔ B₁ ⊔ B₂ ⊔ B₃) ≤ D ∧
        Disjoint (B₁ ⊔ B₂ ⊔ B₃) L ∧ Disjoint B₁ B₂ ∧ Disjoint B₁ B₃ ∧ Disjoint B₂ B₃ ∧
        P₆.original ≤ B₁ ∧ P₇.original ≤ B₂ ∧ P₁.original ≤ B₃ ∧
        (B₁ ⊔ B₂ ⊔ B₃) ≤ liftOrdinaryCycleArcs Z (ordinaryCycleHost R') ⊔
          (P₆.original ⊔ P₇.original ⊔ P₁.original) ∧
        ordinaryCycleHost (L ⊔ B₁ ⊔ B₂ ⊔ B₃) ≤ matchingUnion M ∧
        ∀ T₀ T₁ : Equiv.Perm V, Nonempty (ParityRepairConfiguration
          ![T₀,T₁,M 1,M 2,M 3,M 4,M 5]) := by
  intro hk A B E eTop eLow N P₂ P₃ P₄ P₅ hC E₆ E₇ E₁ P₆ P₇ P₁ hR₆ hR₇ hR₁ F U W L R'
  obtain ⟨B₁,B₂,B₃,M,hD,hL,h₁₂,h₁₃,h₂₃,h₆,h₇,h₁,hSupport,hBound,hConfig,_⟩ :=
    NormalizedCycleAbsorber.exists_original_parity_extension_with_absorption
      (r := r) X hq hm hRD hCover hDis hSize ε₀ ε₁ ε₂ ε₃ d z
      hε₁ hε₂ hε₃ h₁ h₂ h₃ hz hG₁ hG₂ hG₃ hd hT₁ hL₁ hT₂ hL₂ hT₃ hL₃
      hPair hr hCut₁ hCut₂ hCut₃ hRoute₁ hRoute₂ hRoute₃ N hC E₆ E₇ E₁ P₆ P₇ P₁ hR₆ hR₇ hR₁
  exact ⟨B₁,B₂,B₃,M,hD,hL,h₁₂,h₁₃,h₂₃,h₆,h₇,h₁,hSupport,hBound,hConfig⟩

end OverfullWork.DirectedRobustExpansion
