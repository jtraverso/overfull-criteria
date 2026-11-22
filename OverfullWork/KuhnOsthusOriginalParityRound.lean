module

public import OverfullWork.KuhnOsthusRestoredParityRepair
public import OverfullWork.KuhnOsthusParityCompletion

@[expose] public section


/-! A winding residue factor is absorbed by the constructed physical
block, with the seven exceptional systems kept in their own cycles. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V Z : Type*} [Fintype V] [Fintype Z]

/-- Concatenate two disjoint indexed permutation partitions. -/
theorem matchingUnion_addCases_of_disjoint {W : Type*} {s t : ℕ}
    (A : Fin s → Equiv.Perm W) (B : Fin t → Equiv.Perm W)
    (hA : ∀ i j, i ≠ j → ∀ x, A i x ≠ A j x)
    (hB : ∀ i j, i ≠ j → ∀ x, B i x ≠ B j x)
    (hMix : Disjoint (matchingUnion A) (matchingUnion B)) :
    let F : Fin (s+t) → Equiv.Perm W := Fin.addCases A B
    matchingUnion F = matchingUnion A ⊔ matchingUnion B ∧
    ∀ i j, i ≠ j → ∀ x, F i x ≠ F j x := by
  intro F
  have hL (i : Fin s) : F (i.castAdd t) = A i := Fin.addCases_left i
  have hR (i : Fin t) : F (i.natAdd s) = B i := Fin.addCases_right i
  constructor
  · ext x y
    constructor
    · rintro ⟨i,hi⟩
      cases i using Fin.addCases with
      | left i => exact .inl ⟨i,hL i ▸ hi⟩
      | right i => exact .inr ⟨i,hR i ▸ hi⟩
    · rintro (⟨i,hi⟩ | ⟨i,hi⟩)
      · exact ⟨i.castAdd t,(hL i).symm ▸ hi⟩
      · exact ⟨i.natAdd s,(hR i).symm ▸ hi⟩
  · intro i j hij x
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j => rw [hL,hL]; exact hA i j (fun h => hij (congrArg (Fin.castAdd t) h)) x
      | right j =>
        rw [hL,hR]
        intro he
        exact (disjoint_iff_inf_le.mp hMix) ⟨⟨i,he⟩,⟨j,rfl⟩⟩
    | right i =>
      cases j using Fin.addCases with
      | left j =>
        rw [hR,hL]
        intro he
        exact (disjoint_iff_inf_le.mp hMix) ⟨⟨j,he.symm⟩,⟨i,rfl⟩⟩
      | right j => rw [hR,hR]; exact hB i j (fun h => hij (congrArg (Fin.natAdd s) h)) x

/-- The one-factor case of Lemma 10.4, with the actual cycle absorber
and its three physical parity reserves as input. -/
theorem NormalizedCycleAbsorber.absorb_winding_factor
    {D R' : Digraph (V ⊕ Z)} {G H H₆ H₇ H₁ J : Digraph V} {q m : ℕ}
    (X : Fin (14*q) → Finset V) (hq : 15 ≤ q) (hm : 0 < m)
    (hCover : ∀ x, ∃ i, x ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m) (σ : Equiv.Perm V)
    (hNext : ∀ i x, x ∈ X i → σ x ∈ X (finRotate (14*q) i)) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
    ∀ {E : CycleAbsorberExceptionalCovers H A q} {eTop : Fin (2*m) ≃ A 0}
      {eLow : Fin (2*m) ≃ B 0}
      (N : NormalizedCycleAbsorber (G := G \ E.arcs) E eTop eLow)
      (P₂ : ProjectedExceptionalArcs D E.second.digraph (id : Z → Z))
      (P₃ : ProjectedExceptionalArcs D E.third.digraph (id : Z → Z))
      (P₄ : ProjectedExceptionalArcs D E.fourth.digraph (id : Z → Z))
      (P₅ : ProjectedExceptionalArcs D E.fifth.digraph (id : Z → Z)),
      CycleAbsorberOriginalConclusion N D P₂ P₃ P₄ P₅ →
      ∀ (E₆ : IntervalPathCover H₆ (clusterIntervalVertices A (10*q) (12*q)) (A (10*q)) (A (12*q)))
        (E₇ : IntervalPathCover H₇ (clusterIntervalVertices A (12*q) (14*q)) (A (12*q)) (A (14*q)))
        (E₁ : IntervalPathCover H₁ (clusterIntervalVertices A 0 (2*q)) (A 0) (A (2*q)))
        (P₆ : ProjectedExceptionalArcs D E₆.digraph (id : Z → Z))
        (P₇ : ProjectedExceptionalArcs D E₇.digraph (id : Z → Z))
        (P₁ : ProjectedExceptionalArcs D E₁.digraph (id : Z → Z))
        (Q : FirstParityReserve J E₆.digraph (A (7*q+15)) (A (7*q+16)))
        (T : RemainingParityReserves Q.triple R' (A (7*q+19)) (A (7*q+20)) P₇ P₁),
        (∀ l, Q.factor.mark (l,0) = N.upper.rows.mark (l,Fin.last (2*m)) ∧
          Q.factor.permutation (Q.factor.mark (l,0)) =
            N.upper.permutation (N.upper.rows.mark (!l,Fin.last (2*m)))) →
        (∀ l, Q.factor.mark (l,1) = N.lower.rows.mark (l,Fin.last (2*m)) ∧
          Q.factor.permutation (Q.factor.mark (l,1)) =
            N.lower.permutation (N.lower.rows.mark (!l,Fin.last (2*m)))) →
        let W := liftOrdinaryCycleArcs Z N.mainOrdinary ⊔ (P₃.original ⊔ P₅.original)
        let U₀ := liftOrdinaryCycleArcs Z N.upper.ordinary ⊔ P₄.original
        let U₁ := liftOrdinaryCycleArcs Z N.lower.ordinary ⊔ P₂.original
        let L := W ⊔ U₀ ⊔ U₁
        let L₁ := liftOrdinaryCycleArcs Z Q.factor.ordinary ⊔ P₆.original
        let L₂ := liftOrdinaryCycleArcs Z T.second.ordinary ⊔ P₇.original
        let L₃ := liftOrdinaryCycleArcs Z T.third.ordinary ⊔ P₁.original
        let R := liftOrdinaryCycleArcs Z (⟨fun x y => σ x = y⟩ : Digraph V)
        Disjoint (L₁ ⊔ L₂ ⊔ L₃) L → Disjoint L₁ L₂ → Disjoint L₁ L₃ →
        Disjoint R (L ⊔ (L₁ ⊔ L₂ ⊔ L₃)) →
        ∃ F : Fin 7 → Equiv.Perm (V ⊕ Z),
          matchingUnion F = R ⊔ (L ⊔ (L₁ ⊔ L₂ ⊔ L₃)) ∧
          (∀ a b, a ≠ b → ∀ v, F a v ≠ F b v) ∧
          (∀ a, HasSpanningCycle (fun v w => F a v = w)) ∧
          ∀ a : Fin 7, (![P₃.original,P₅.original,P₄.original,P₂.original,
            P₆.original,P₇.original,P₁.original] a) ≤ ⟨fun v w => F a v = w⟩ := by
  intro hk A B E eTop eLow N P₂ P₃ P₄ P₅ hC E₆ E₇ E₁ P₆ P₇ P₁ Q T hQ₀ hQ₁
    W U₀ U₁ L L₁ L₂ L₃ R hB hB₁₂ hB₁₃ hR
  obtain ⟨F,hF,hDisF,hHam₀,hHam₁,hMode₀,hMode₁,hE₃,hE₅,hE₄,hE₂,hLast₀,hLast₁⟩ :=
    NormalizedCycleAbsorber.kuhn_osthus_lemma_10_2 X hq hm hCover hDis hSize σ hNext
      N P₂ P₃ P₄ P₅ hC (hR.mono_right le_sup_left)
  obtain ⟨f₁,hf₁,⟨S₁⟩,hOrd₁⟩ := P₆.exists_restored_factor Q.factor.permutation
    Q.factor.exact_factor Q.factor.ordinary_separate
  obtain ⟨f₂,hf₂,⟨S₂⟩,hOrd₂⟩ := P₇.exists_restored_factor T.second.permutation
    T.second.exact_factor T.second.ordinary_separate
  obtain ⟨f₃,hf₃,⟨S₃⟩,hOrd₃⟩ := P₁.exists_restored_factor T.third.permutation
    T.third.exact_factor T.third.ordinary_separate
  let U : Fin 3 → Equiv.Perm (V ⊕ Z) := ![f₁,f₂,f₃]
  let K : Fin 3 → Digraph (V ⊕ Z) := ![L₁,L₂,L₃]
  have hU (a : Fin 3) (v w : V ⊕ Z) : (K a).Adj v w ↔ U a v = w := by
    fin_cases a
    · exact hf₁ v w
    · exact hf₂ v w
    · exact hf₃ v w
  have hApart : Pairwise (fun a b => Disjoint (K a) (K b)) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> first
    | exact (hab rfl).elim
    | exact hB₁₂
    | exact hB₁₂.symm
    | exact hB₁₃
    | exact hB₁₃.symm
    | exact T.disjoint
    | exact T.disjoint.symm
  have hDisU : ∀ a b, a ≠ b → ∀ v, U a v ≠ U b v := by
    intro a b hab v he
    exact (disjoint_iff_inf_le.mp (hApart hab)) ⟨(hU a _ _).mpr he,(hU b _ _).mpr rfl⟩
  have hUnionU : matchingUnion U = L₁ ⊔ L₂ ⊔ L₃ := by
    ext v w
    constructor
    · rintro ⟨a,ha⟩
      have h := (hU a _ _).mpr ha
      fin_cases a
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact ⟨0,(hf₁ _ _).mp h⟩
      · exact ⟨1,(hf₂ _ _).mp h⟩
      · exact ⟨2,(hf₃ _ _).mp h⟩
  have hMix : Disjoint (matchingUnion F) (matchingUnion U) := by
    rw [hF,hUnionU]
    exact disjoint_sup_left.mpr ⟨hR.mono_right le_sup_right,hB.symm⟩
  obtain ⟨hUnion,hDisG⟩ := matchingUnion_addCases_of_disjoint F U hDisF hDisU hMix
  let G' : Fin 7 → Equiv.Perm (V ⊕ Z) := ![F 0,F 1,F 2,F 3,f₁,f₂,f₃]
  have hG' : G' = (fun a => Fin.addCases F U a) := by
    funext a
    fin_cases a <;> rfl
  rw [← hG',hF,hUnionU] at hUnion
  rw [← hG'] at hDisG
  let P : Fin 7 → Equiv.Perm V := ![σ,σ,N.upper.permutation,N.lower.permutation,
    Q.factor.permutation,T.second.permutation,T.third.permutation]
  have hCross₀ (l : Bool) : Q.factor.permutation (Q.factor.mark (l,0)) =
      N.upper.permutation (Q.factor.mark (!l,0)) := by rw [(hQ₀ l).2,(hQ₀ (!l)).1]
  have hCross₁ (l : Bool) : Q.factor.permutation (Q.factor.mark (l,1)) =
      N.lower.permutation (Q.factor.mark (!l,1)) := by rw [(hQ₁ l).2,(hQ₁ (!l)).1]
  let C : ParityRepairConfiguration P := T.repairConfiguration Q σ σ _ _ hCross₀ hCross₁
  have hMark (l : Bool) (c : Fin 3) : C.mark (l,c) = Q.factor.mark (l,c) := rfl
  have hAux₀ : C.auxLeft = (T.auxiliary.diagonal.source false).val := rfl
  have hAux₁ : C.auxRight = (T.auxiliary.diagonal.source true).val := rfl
  have hRotate (i : ℕ) : B i = A (7*q+i) := cyclicCluster_rotateClusterArray X hk _ _
  have hMark₀ (l : Bool) : C.mark (l,0) ∈ A 11 := (hQ₀ l).1.symm ▸ N.upper.repair_start l
  have hMark₁ (l : Bool) : C.mark (l,1) ∈ A (7*q+11) := by
    rw [hMark,(hQ₁ l).1,← hRotate]
    exact N.lower.repair_start l
  have hMark₂ (l : Bool) : C.mark (l,2) ∈ A (7*q+15) :=
    (Q.triple_arcs l).1.symm ▸ (Q.triple.source l).prop
  have hAux (l : Bool) : (T.auxiliary.diagonal.source l).val ∈ A (7*q+19) :=
    (T.auxiliary.diagonal.source l).prop
  have hNo₄ {x y : V} (he : E.fourth.digraph.Adj x y) (l : Bool) : x ≠ C.mark (l,0) := by
    rintro rfl
    exact E.fourth.no_source_outside_cyclic_interval hk hDis (by omega) (by omega)
      (.inl (by omega)) (hMark₀ l) he
  have hNo₂ {x y : V} (he : E.second.digraph.Adj x y) (l : Bool) : x ≠ C.mark (l,1) := by
    rintro rfl
    exact E.second.no_source_outside_cyclic_interval hk hDis (by omega) (by omega)
      (.inr (by omega)) (hMark₁ l) he
  have hBefore₆ {i : ℕ} (hi : i < 10*q) {x y : V} (hx : x ∈ A i) : ¬ E₆.digraph.Adj x y :=
    E₆.no_source_outside_cyclic_interval hk hDis (by omega) (by omega) (.inl hi) hx
  have hNo₆ {x y : V} (he : E₆.digraph.Adj x y) (l : Bool) (c : Fin 3) : x ≠ C.mark (l,c) := by
    rintro rfl
    fin_cases c
    · exact hBefore₆ (by omega) (hMark₀ l) he
    · exact hBefore₆ (by omega) (hMark₁ l) he
    · exact hBefore₆ (by omega) (hMark₂ l) he
  have hBefore₇ {i : ℕ} (hi : 0 < i) (hb : i < 12*q) {x y : V} (hx : x ∈ A i) :
      ¬ E₇.digraph.Adj x y := by
    apply E₇.no_source_at_distinct_cyclic_slot hk hDis _ hx
    intro j hj hj'
    rw [Nat.mod_eq_of_lt (by omega : i < 14*q)]
    by_cases hj'' : j < 14*q
    · rw [Nat.mod_eq_of_lt hj'']
      omega
    · have hjEq : j = 14*q := by omega
      rw [hjEq,Nat.mod_self]
      omega
  have hAfter₁ {i : ℕ} (hi : 2*q < i) (hb : i < 14*q) {x y : V} (hx : x ∈ A i) :
      ¬ E₁.digraph.Adj x y :=
    E₁.no_source_outside_cyclic_interval hk hDis (by omega) hb (.inr hi) hx
  have hNo₇ {x y : V} (he : E₇.digraph.Adj x y) :
      (x ≠ C.auxLeft ∧ x ≠ C.auxRight) ∧ (x ≠ C.mark (false,2) ∧ x ≠ C.mark (true,2)) := by
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
    · rw [hAux₀]
      rintro rfl
      exact hBefore₇ (by omega) (by omega) (hAux false) he
    · rw [hAux₁]
      rintro rfl
      exact hBefore₇ (by omega) (by omega) (hAux true) he
    · rintro rfl
      exact hBefore₇ (by omega) (by omega) (hMark₂ false) he
    · rintro rfl
      exact hBefore₇ (by omega) (by omega) (hMark₂ true) he
  have hNo₁ {x y : V} (he : E₁.digraph.Adj x y) :
      (x ≠ C.auxLeft ∧ x ≠ C.auxRight) ∧ (x ≠ C.mark (false,2) ∧ x ≠ C.mark (true,2)) := by
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
    · rw [hAux₀]
      rintro rfl
      exact hAfter₁ (by omega) (by omega) (hAux false) he
    · rw [hAux₁]
      rintro rfl
      exact hAfter₁ (by omega) (by omega) (hAux true) he
    · rintro rfl
      exact hAfter₁ (by omega) (by omega) (hMark₂ false) he
    · rintro rfl
      exact hAfter₁ (by omega) (by omega) (hMark₂ true) he
  have hProtected₂ {x : V} (h : x ≠ C.mark (false,0) ∧ x ≠ C.mark (true,0)) : C.Protected 2 x :=
    ⟨.inr h,.inl (by decide),.inl (by decide),.inl (by decide)⟩
  have hProtected₃ {x : V} (h : x ≠ C.mark (false,1) ∧ x ≠ C.mark (true,1)) : C.Protected 3 x :=
    ⟨.inl (by decide),.inr h,.inl (by decide),.inl (by decide)⟩
  let E' : Fin 7 → Digraph V := ![E.third.digraph,E.fifth.digraph,E.fourth.digraph,E.second.digraph,
    E₆.digraph,E₇.digraph,E₁.digraph]
  have hGuard (i : Fin 7) {x y : V} (h : (E' i).Adj x y) : C.Protected i x := by
    fin_cases i
    · exact ⟨.inl (by decide),.inl (by decide),.inl (by decide),.inl (by decide)⟩
    · exact ⟨.inl (by decide),.inl (by decide),.inl (by decide),.inl (by decide)⟩
    · exact hProtected₂ ⟨hNo₄ h false,hNo₄ h true⟩
    · exact hProtected₃ ⟨hNo₂ h false,hNo₂ h true⟩
    · exact ⟨.inr ⟨hNo₆ h false 0,hNo₆ h true 0⟩,.inr ⟨hNo₆ h false 1,hNo₆ h true 1⟩,
        .inl (by decide),.inr ⟨hNo₆ h false 2,hNo₆ h true 2⟩⟩
    · exact ⟨.inl (by decide),.inl (by decide),.inr (hNo₇ h).1,.inr (hNo₇ h).2⟩
    · exact ⟨.inl (by decide),.inl (by decide),.inr (hNo₁ h).1,.inr (hNo₁ h).2⟩
  have hLastC₀ (l : Bool) : G' 2 (.inl (C.mark (l,0))) = .inl (P 2 (C.mark (l,0))) := by
    change F 2 (.inl (C.mark (l,0))) = .inl (N.upper.permutation (C.mark (l,0)))
    rw [hMark,(hQ₀ l).1]
    exact hLast₀ l
  have hLastC₁ (l : Bool) : G' 3 (.inl (C.mark (l,1))) = .inl (P 3 (C.mark (l,1))) := by
    change F 3 (.inl (C.mark (l,1))) = .inl (N.lower.permutation (C.mark (l,1)))
    rw [hMark,(hQ₁ l).1]
    exact hLast₁ l
  have hOrd (a : Fin 7) (x : V) (hn : ¬ C.Protected a x) : G' a (.inl x) = .inl (P a x) := by
    fin_cases a
    · exact (hn ⟨.inl (by decide),.inl (by decide),.inl (by decide),.inl (by decide)⟩).elim
    · exact (hn ⟨.inl (by decide),.inl (by decide),.inl (by decide),.inl (by decide)⟩).elim
    · by_cases h₀ : x = C.mark (false,0)
      · exact h₀.symm ▸ hLastC₀ false
      by_cases h₁ : x = C.mark (true,0)
      · exact h₁.symm ▸ hLastC₀ true
      exact (hn (hProtected₂ ⟨h₀,h₁⟩)).elim
    · by_cases h₀ : x = C.mark (false,1)
      · exact h₀.symm ▸ hLastC₁ false
      by_cases h₁ : x = C.mark (true,1)
      · exact h₁.symm ▸ hLastC₁ true
      exact (hn (hProtected₃ ⟨h₀,h₁⟩)).elim
    · apply hOrd₁
      rintro ⟨z,rfl⟩
      exact hn (hGuard 4 (P₆.shortcut z))
    · apply hOrd₂
      rintro ⟨z,rfl⟩
      exact hn (hGuard 5 (P₇.shortcut z))
    · apply hOrd₃
      rintro ⟨z,rfl⟩
      exact hn (hGuard 6 (P₁.shortcut z))
  have hModeC₀ : (∀ v, (G' 2).SameCycle (.inl (C.mark (false,0))) v) ∨
      MarkedBicycle (G' 2) (.inl (C.mark (false,0))) (.inl (C.mark (true,0))) := by
    rw [hMark,hMark,(hQ₀ false).1,(hQ₀ true).1]
    exact hMode₀
  have hModeC₁ : (∀ v, (G' 3).SameCycle (.inl (C.mark (false,1))) v) ∨
      MarkedBicycle (G' 3) (.inl (C.mark (false,1))) (.inl (C.mark (true,1))) := by
    rw [hMark,hMark,(hQ₁ false).1,(hQ₁ true).1]
    exact hMode₁
  obtain ⟨F',hF',hDis',hHam',hKeep,hKeepExc⟩ := parity_repair_after_original_sweeps C G'
    S₁ S₂ S₃ hOrd hDisG hHam₀ hHam₁ hModeC₀ hModeC₁
  have hUnion' : matchingUnion F' = R ⊔ (L ⊔ (L₁ ⊔ L₂ ⊔ L₃)) := by
    rw [hF',hUnion]
    change (R ⊔ L) ⊔ (L₁ ⊔ L₂ ⊔ L₃) = R ⊔ (L ⊔ (L₁ ⊔ L₂ ⊔ L₃))
    ac_rfl
  refine ⟨F',hUnion',hDis',hHam',?_⟩
  intro a
  fin_cases a
  · exact P₃.keep_original (G' 0) (F' 0) hE₃ (fun h => hKeep 0 _ (hGuard 0 h)) (hKeepExc 0)
  · exact P₅.keep_original (G' 1) (F' 1) hE₅ (fun h => hKeep 1 _ (hGuard 1 h)) (hKeepExc 1)
  · exact P₄.keep_original (G' 2) (F' 2) hE₄ (fun h => hKeep 2 _ (hGuard 2 h)) (hKeepExc 2)
  · exact P₂.keep_original (G' 3) (F' 3) hE₂ (fun h => hKeep 3 _ (hGuard 3 h)) (hKeepExc 3)
  · exact P₆.keep_original (G' 4) (F' 4) (fun v w h => (hf₁ v w).mp (.inr h))
      (fun h => hKeep 4 _ (hGuard 4 h)) (hKeepExc 4)
  · exact P₇.keep_original (G' 5) (F' 5) (fun v w h => (hf₂ v w).mp (.inr h))
      (fun h => hKeep 5 _ (hGuard 5 h)) (hKeepExc 5)
  · exact P₁.keep_original (G' 6) (F' 6) (fun v w h => (hf₃ v w).mp (.inr h))
      (fun h => hKeep 6 _ (hGuard 6 h)) (hKeepExc 6)

/-- The absorption conclusion retained when the construction forgets
the internal routes of a physical parity block. -/
def AbsorbsWindingFactor {k : ℕ} (X : Fin k → Finset V)
    (P : Digraph (V ⊕ Z)) (E : Fin 7 → Digraph (V ⊕ Z)) : Prop :=
  ∀ [Fintype Z] (σ : Equiv.Perm V),
    (∀ i x, x ∈ X i → σ x ∈ X (finRotate k i)) →
    let R := liftOrdinaryCycleArcs Z (⟨fun x y => σ x = y⟩ : Digraph V)
    Disjoint R P →
    ∃ F : Fin 7 → Equiv.Perm (V ⊕ Z),
      matchingUnion F = R ⊔ P ∧
      (∀ a b, a ≠ b → ∀ v, F a v ≠ F b v) ∧
      (∀ a, HasSpanningCycle (fun v w => F a v = w)) ∧
      ∀ a, E a ≤ ⟨fun v w => F a v = w⟩

end OverfullWork.DirectedRobustExpansion
