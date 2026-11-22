module

public import OverfullWork.KuhnOsthusRestoredCycleSweep
public import OverfullWork.KuhnOsthusCycleAbsorberPhysical

@[expose] public section


/-! The physical cycle-absorber step of Kühn–Osthus Lemma 10.2.
Split and splice the winding residue, then run both ordered sweeps
on the original factors with their exceptional paths restored. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V Z : Type*} [Fintype V] [Fintype Z]

omit [Fintype V] [Fintype Z] in
/-- Restore the exact arc set and the segments between ordinary vertices. -/
theorem ProjectedExceptionalArcs.exists_restored_factor
    {D : Digraph (V ⊕ Z)} {E O : Digraph V} (P : ProjectedExceptionalArcs D E (id : Z → Z))
    (σ : Equiv.Perm V) (hσ : ∀ x y, (O ⊔ E).Adj x y ↔ σ x = y)
    (hSep : ∀ {x y}, O.Adj x y → ¬ E.Adj x y) :
    ∃ τ : Equiv.Perm (V ⊕ Z),
      (∀ x y, (liftOrdinaryCycleArcs Z O ⊔ P.original).Adj x y ↔ τ x = y) ∧
      Nonempty (MarkedCycleSegments τ Embedding.inl σ) ∧
      ∀ x, x ∉ Set.range P.source → τ (.inl x) = .inl (σ x) := by
  obtain ⟨τ,hτ⟩ := exists_restored_exceptional_permutation σ P.source
  exact ⟨τ,fun x y => by rw [← P.restore_exact σ hσ hSep]; exact hτ x y,
    ⟨restoredExceptionalSegments P.source hτ⟩,fun x hx => (hτ _ _).mp ⟨rfl,hx⟩⟩

omit [Fintype V] [Fintype Z] in
private theorem liftOrdinaryCycleArcs_sup (O P : Digraph V) :
    liftOrdinaryCycleArcs Z (O ⊔ P) = liftOrdinaryCycleArcs Z O ⊔ liftOrdinaryCycleArcs Z P := by
  ext x y
  cases x <;> cases y
  · rfl
  all_goals change False ↔ False ∨ False; simp

omit [Fintype V] [Fintype Z] in
private theorem original_halves_disjoint
    {D : Digraph (V ⊕ Z)} {E K O P : Digraph V}
    (A : ProjectedExceptionalArcs D E (id : Z → Z)) (B : ProjectedExceptionalArcs D K (id : Z → Z))
    (hOut : ∀ {x a y z}, (O ⊔ E).Adj x y → (P ⊔ K).Adj a z → x ≠ a)
    (hIn : ∀ {x a y z}, (O ⊔ E).Adj x y → (P ⊔ K).Adj a z → y ≠ z) :
    Disjoint (liftOrdinaryCycleArcs Z O ⊔ A.original) (liftOrdinaryCycleArcs Z P ⊔ B.original) := by
  rw [disjoint_iff_inf_le]
  rintro (x | z) (y | w) ⟨h,h'⟩
  · have h₁ : (O ⊔ E).Adj x y := h.imp_right And.left
    have h₂ : (P ⊔ K).Adj x y := h'.imp_right And.left
    exact hOut h₁ h₂ rfl
  · obtain ⟨a,ha,_⟩ := h.resolve_left id
    obtain ⟨b,hb,_⟩ := h'.resolve_left id
    exact hOut (.inr (A.shortcut a)) (.inr (B.shortcut b)) (ha.trans hb.symm)
  · obtain ⟨a,_,ha⟩ := h.resolve_left id
    obtain ⟨b,_,hb⟩ := h'.resolve_left id
    exact hIn (.inr (A.shortcut a)) (.inr (B.shortcut b)) (ha.trans hb.symm)
  · exact h.elim id id

omit [Fintype Z] in
/-- A cluster disjoint from all the occupied slots contains no source
of the cover, including for intervals ending at the cyclic wrap. -/
theorem IntervalPathCover.no_source_at_distinct_cyclic_slot
    {H : Digraph V} {k b c : ℕ} {X : Fin k → Finset V} (hk : 0 < k)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (E : IntervalPathCover H (clusterIntervalVertices (cyclicCluster X hk) b c)
      (cyclicCluster X hk b) (cyclicCluster X hk c))
    {i : ℕ} (hOut : ∀ j, b ≤ j → j ≤ c → i%k ≠ j%k) {x y : V}
    (hx : x ∈ cyclicCluster X hk i) : ¬ E.digraph.Adj x y := by
  intro h
  have hV := (mem_sdiff.mp ((E.slots x).1.mp ⟨_,h⟩)).1
  obtain ⟨j,hj,hjc,hjv⟩ := (mem_clusterIntervalVertices _ _ _ _).mp hV
  exact disjoint_left.mp (cyclicCluster_distinct hk hDis (hOut j hj hjc)) hx hjv

omit [Fintype Z] in
/-- No outgoing arc of the cover starts in a cluster outside its interval. -/
theorem IntervalPathCover.no_source_outside_cyclic_interval
    {H : Digraph V} {k b c : ℕ} {X : Fin k → Finset V} (hk : 0 < k)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j)) (hc : c < k)
    (E : IntervalPathCover H (clusterIntervalVertices (cyclicCluster X hk) b c)
      (cyclicCluster X hk b) (cyclicCluster X hk c))
    {i : ℕ} (hi : i < k) (hOut : i < b ∨ c < i) {x y : V}
    (hx : x ∈ cyclicCluster X hk i) : ¬ E.digraph.Adj x y := by
  apply E.no_source_at_distinct_cyclic_slot hk hDis _ hx
  intro j hj hjc
  rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (hjc.trans_lt hc)]
  rcases hOut with h | h <;> omega

omit [Fintype V] [Fintype Z] in
/-- The original exceptional system survives any change fixing its outgoing slots. -/
theorem ProjectedExceptionalArcs.keep_original {D : Digraph (V ⊕ Z)} {E : Digraph V}
    (P : ProjectedExceptionalArcs D E (id : Z → Z))
    (F G : Equiv.Perm (V ⊕ Z)) (hF : ∀ x y, P.original.Adj x y → F x = y)
    (hOrd : ∀ {x y}, E.Adj x y → G (.inl x) = F (.inl x))
    (hExc : ∀ z, G (.inr z) = F (.inr z)) : P.original ≤ ⟨fun x y => G x = y⟩ := by
  rintro (x | z) (y | w) h
  · exact (hOrd h.1).trans (hF _ _ h)
  · have hf := hF _ _ h
    obtain ⟨j,hj,_⟩ := h
    exact (hj ▸ hOrd (P.shortcut j)).trans hf
  · exact (hExc z).trans (hF _ _ h)
  · exact h.elim

/-- The two actual sweeps produce the four factors of Lemma 10.2.
The two primary factors are Hamiltonian. Each auxiliary factor is
Hamiltonian or a bicycle separated by its designated repair pair. -/
theorem NormalizedCycleAbsorber.kuhn_osthus_lemma_10_2
    {D : Digraph (V ⊕ Z)} {G H : Digraph V} {q m : ℕ}
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
      let W := liftOrdinaryCycleArcs Z N.mainOrdinary ⊔ (P₃.original ⊔ P₅.original)
      let U₀ := liftOrdinaryCycleArcs Z N.upper.ordinary ⊔ P₄.original
      let U₁ := liftOrdinaryCycleArcs Z N.lower.ordinary ⊔ P₂.original
      let R := liftOrdinaryCycleArcs Z (⟨fun x y => σ x = y⟩ : Digraph V)
      Disjoint R (W ⊔ U₀ ⊔ U₁) →
      ∃ F : Fin 4 → Equiv.Perm (V ⊕ Z),
        matchingUnion F = R ⊔ (W ⊔ U₀ ⊔ U₁) ∧
        (∀ a b, a ≠ b → ∀ z, F a z ≠ F b z) ∧
        HasSpanningCycle (fun x y => F 0 x = y) ∧
        HasSpanningCycle (fun x y => F 1 x = y) ∧
        ((∀ v, (F 2).SameCycle (.inl (N.upper.rows.mark (false,Fin.last (2*m)))) v) ∨
          MarkedBicycle (F 2) (.inl (N.upper.rows.mark (false,Fin.last (2*m))))
            (.inl (N.upper.rows.mark (true,Fin.last (2*m))))) ∧
        ((∀ v, (F 3).SameCycle (.inl (N.lower.rows.mark (false,Fin.last (2*m)))) v) ∨
          MarkedBicycle (F 3) (.inl (N.lower.rows.mark (false,Fin.last (2*m))))
            (.inl (N.lower.rows.mark (true,Fin.last (2*m))))) ∧
        P₃.original ≤ ⟨fun x y => F 0 x = y⟩ ∧ P₅.original ≤ ⟨fun x y => F 1 x = y⟩ ∧
        P₄.original ≤ ⟨fun x y => F 2 x = y⟩ ∧ P₂.original ≤ ⟨fun x y => F 3 x = y⟩ ∧
        (∀ b, F 2 (.inl (N.upper.rows.mark (b,Fin.last (2*m)))) =
          .inl (N.upper.permutation (N.upper.rows.mark (b,Fin.last (2*m))))) ∧
        (∀ b, F 3 (.inl (N.lower.rows.mark (b,Fin.last (2*m)))) =
          .inl (N.lower.permutation (N.lower.rows.mark (b,Fin.last (2*m))))) := by
  intro hk A B E eTop eLow N P₂ P₃ P₄ P₅ hC W U₀ U₁ R hRDis
  obtain ⟨P,Q,τ₀,τ₁,hR,hτ₀,hτ₁,hPQ,hOut,hIn,hQTop,hPLow,hCover₀,hCover₁⟩ :=
    NormalizedCycleAbsorber.exists_residue_half_splices_with_roots X (by omega) hCover hDis hSize σ hNext N
  let O₀ := N.top.paths.unionPaths ⊔ N.topTail.unionPaths
  let O₁ := N.low.paths.unionPaths ⊔ N.lowTail.unionPaths
  have hO₀ : O₀ ≤ G \ E.arcs := sup_le N.top.paths.unionPaths_le N.topTail.unionPaths_le
  have hO₁ : O₁ ≤ G \ E.arcs := sup_le N.low.paths.unionPaths_le N.lowTail.unionPaths_le
  have hU₀ : N.upper.ordinary ≤ G \ E.arcs := N.upper.ordinary_le.trans (fun _ _ h => h.1)
  have hLow := N.lower.exact_factor
  rw [N.second_arcs] at hLow
  have hTopSlot {x y : V} : (O₀ ⊔ E.third.digraph).Adj x y →
      ((N.top.paths.unionPaths ⊔ E.third.digraph) ⊔ N.topTail.unionPaths).Adj x y := by
    change ((_ ∨ _) ∨ _) → (_ ∨ _) ∨ _
    tauto
  have hLowSlot {x y : V} : (O₁ ⊔ E.fifth.digraph).Adj x y →
      ((N.low.paths.unionPaths ⊔ E.fifth.digraph) ⊔ N.lowTail.unionPaths).Adj x y := by
    change ((_ ∨ _) ∨ _) → (_ ∨ _) ∨ _
    tauto
  have hT₀ : ∀ x y, ((O₀ ⊔ Q) ⊔ E.third.digraph).Adj x y ↔ τ₀ x = y := by
    intro x y
    rw [← hτ₀]
    simp only [O₀,Digraph.sup_adj]
    tauto
  have hT₁ : ∀ x y, ((O₁ ⊔ P) ⊔ E.fifth.digraph).Adj x y ↔ τ₁ x = y := by
    intro x y
    rw [← hτ₁]
    simp only [O₁,Digraph.sup_adj]
    tauto
  have hS₀ : ∀ {x y}, (O₀ ⊔ Q).Adj x y → ¬ E.third.digraph.Adj x y := by
    rintro x y (ho | hq') he
    · exact (hO₀ ho).2 (.inl (.inl (.inl he)))
    · exact hQTop (.inl (.inr he)) hq'
  have hS₁ : ∀ {x y}, (O₁ ⊔ P).Adj x y → ¬ E.fifth.digraph.Adj x y := by
    rintro x y (ho | hp) he
    · exact (hO₁ ho).2 (.inl (.inl (.inr he)))
    · exact hPLow hp (.inl (.inr he))
  obtain ⟨f₀,hf₀,⟨S₀⟩,hOrd₀⟩ := P₃.exists_restored_factor τ₀ hT₀ hS₀
  obtain ⟨f₁,hf₁,⟨S₁⟩,hOrd₁⟩ := P₅.exists_restored_factor τ₁ hT₁ hS₁
  obtain ⟨f₂,hf₂,⟨S₂⟩,hOrd₂⟩ := P₄.exists_restored_factor N.upper.permutation N.upper.exact_factor
    (fun ho he => (hU₀ ho).2 (.inl (.inr he)))
  obtain ⟨f₃,hf₃,⟨S₃⟩,hOrd₃⟩ := P₂.exists_restored_factor N.lower.permutation hLow
    (fun ho he => (N.lower_le ho).2 (.inr he))
  let W₀ := liftOrdinaryCycleArcs Z O₀ ⊔ P₃.original
  let W₁ := liftOrdinaryCycleArcs Z O₁ ⊔ P₅.original
  let R₀ := liftOrdinaryCycleArcs Z Q
  let R₁ := liftOrdinaryCycleArcs Z P
  let L₀ := W₀ ⊔ R₀
  let L₁ := W₁ ⊔ R₁
  have hW : W₀ ⊔ W₁ = W := by
    change _ = liftOrdinaryCycleArcs Z (O₀ ⊔ O₁) ⊔ _
    unfold W₀ W₁
    rw [liftOrdinaryCycleArcs_sup (Z := Z) O₀ O₁]
    ac_rfl
  have hResidue : R₀ ⊔ R₁ = R := by
    unfold R₀ R₁
    rw [sup_comm,← liftOrdinaryCycleArcs_sup,hR]
  have h₀ : ∀ x y, L₀.Adj x y ↔ f₀ x = y := by
    have he : liftOrdinaryCycleArcs Z (O₀ ⊔ Q) ⊔ P₃.original = L₀ := by
      unfold L₀ W₀ R₀
      rw [liftOrdinaryCycleArcs_sup]
      ac_rfl
    rwa [he] at hf₀
  have h₁ : ∀ x y, L₁.Adj x y ↔ f₁ x = y := by
    have he : liftOrdinaryCycleArcs Z (O₁ ⊔ P) ⊔ P₅.original = L₁ := by
      unfold L₁ W₁ R₁
      rw [liftOrdinaryCycleArcs_sup]
      ac_rfl
    rwa [he] at hf₁
  have h₂ : ∀ x y, U₀.Adj x y ↔ f₂ x = y := hf₂
  have h₃ : ∀ x y, U₁.Adj x y ↔ f₃ x = y := hf₃
  have hW₀₁ : Disjoint W₀ W₁ := original_halves_disjoint P₃ P₅
    (fun hu hv => hOut (hTopSlot hu) (hLowSlot hv))
    (fun hu hv => hIn (hTopSlot hu) (hLowSlot hv))
  have hR₀₁ : Disjoint R₀ R₁ := by
    rw [disjoint_iff_inf_le]
    rintro (x | z) (y | w) ⟨hu,hv⟩
    · exact (disjoint_iff_inf_le.mp hPQ) ⟨hv,hu⟩
    all_goals exact hu
  have hDW₀ : W₀ ≤ W := hW ▸ le_sup_left
  have hDW₁ : W₁ ≤ W := hW ▸ le_sup_right
  have hDR₀ : R₀ ≤ R := hResidue ▸ le_sup_left
  have hDR₁ : R₁ ≤ R := hResidue ▸ le_sup_right
  have hR_W : Disjoint R W := hRDis.mono_right (le_sup_left.trans le_sup_left)
  have hR_U₀ : Disjoint R U₀ := hRDis.mono_right (le_sup_right.trans le_sup_left)
  have hR_U₁ : Disjoint R U₁ := hRDis.mono_right le_sup_right
  have hC₀ : Disjoint W U₀ := hC.2.2.2.1
  have hC₁ : Disjoint W U₁ := hC.2.2.2.2.1
  have hC₂ : Disjoint U₀ U₁ := hC.2.2.2.2.2.1
  let T : Fin 4 → Equiv.Perm (V ⊕ Z) := ![f₀,f₁,f₂,f₃]
  let K : Fin 4 → Digraph (V ⊕ Z) := ![L₀,L₁,U₀,U₁]
  have hExact (i : Fin 4) (x y : V ⊕ Z) : (K i).Adj x y ↔ T i x = y := by
    fin_cases i
    · exact h₀ x y
    · exact h₁ x y
    · exact h₂ x y
    · exact h₃ x y
  have hDis₀₁ : Disjoint L₀ L₁ := disjoint_sup_left.mpr
    ⟨disjoint_sup_right.mpr ⟨hW₀₁,(hR_W.mono hDR₁ hDW₀).symm⟩,
      disjoint_sup_right.mpr ⟨hR_W.mono hDR₀ hDW₁,hR₀₁⟩⟩
  have hDisL₀U₀ : Disjoint L₀ U₀ := disjoint_sup_left.mpr ⟨hC₀.mono_left hDW₀,hR_U₀.mono_left hDR₀⟩
  have hDisL₁U₀ : Disjoint L₁ U₀ := disjoint_sup_left.mpr ⟨hC₀.mono_left hDW₁,hR_U₀.mono_left hDR₁⟩
  have hDisL₀U₁ : Disjoint L₀ U₁ := disjoint_sup_left.mpr ⟨hC₁.mono_left hDW₀,hR_U₁.mono_left hDR₀⟩
  have hDisL₁U₁ : Disjoint L₁ U₁ := disjoint_sup_left.mpr ⟨hC₁.mono_left hDW₁,hR_U₁.mono_left hDR₁⟩
  have hK : Pairwise (fun i j => Disjoint (K i) (K j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | exact hDis₀₁
    | exact hDis₀₁.symm
    | exact hDisL₀U₀
    | exact hDisL₀U₀.symm
    | exact hDisL₀U₁
    | exact hDisL₀U₁.symm
    | exact hDisL₁U₀
    | exact hDisL₁U₀.symm
    | exact hDisL₁U₁
    | exact hDisL₁U₁.symm
    | exact hC₂
    | exact hC₂.symm
  have hTDis : ∀ a b, a ≠ b → ∀ z, T a z ≠ T b z := by
    intro a b hab z he
    exact (disjoint_iff_inf_le.mp (hK hab)) ⟨(hExact a _ _).mpr he,(hExact b _ _).mpr rfl⟩
  have hUnion : matchingUnion T = R ⊔ (W ⊔ U₀ ⊔ U₁) := by
    have he : (L₀ ⊔ L₁ ⊔ U₀ ⊔ U₁) = R ⊔ (W ⊔ U₀ ⊔ U₁) := by
      rw [← hResidue,← hW]
      unfold L₀ L₁
      ac_rfl
    rw [← he]
    ext x y
    constructor
    · rintro ⟨i,hi⟩
      have h := (hExact i _ _).mpr hi
      fin_cases i
      · exact .inl (.inl (.inl h))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h
    · rintro (((h | h) | h) | h)
      · exact ⟨0,(h₀ _ _).mp h⟩
      · exact ⟨1,(h₁ _ _).mp h⟩
      · exact ⟨2,(h₂ _ _).mp h⟩
      · exact ⟨3,(h₃ _ _).mp h⟩
  let J : Fin 4 → Equiv.Perm V := ![τ₀,τ₁,N.upper.permutation,N.lower.permutation]
  have hPath₀ {x y : V} (h : N.top.paths.unionPaths.Adj x y) : J 0 x = y :=
    (hτ₀ _ _).mp (.inl (.inl (.inl h)))
  have hPath₁ {x y : V} (h : N.low.paths.unionPaths.Adj x y) : J 1 x = y :=
    (hτ₁ _ _).mp (.inr (.inl (.inl h)))
  let M₀ := N.upper.sweepData hm (by omega) J 0 2 hPath₀ hCover₀ rfl
  let M₁ := N.lower.sweepData hm (by omega) J 1 3 hPath₁ hCover₁ rfl
  have hSlots₀ := N.upper.sweepData_source_slots hm (by omega) J 0 2 hPath₀ hCover₀ rfl
  have hSlots₁ := N.lower.sweepData_source_slots hm (by omega) J 1 3 hPath₁ hCover₁ rfl
  have hRotate (i : ℕ) : B i = A (7*q+i) := cyclicCluster_rotateClusterArray X hk _ _
  have hAway₀ {b c : ℕ}
      (C : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c))
      (hc : c < 14*q) (hb : 7 < b) {x y : V} (hx : x ∈ A 3 ∨ x ∈ A 7) :
      ¬ C.digraph.Adj x y := by
    rcases hx with hx | hx
    · exact C.no_source_outside_cyclic_interval hk hDis hc (by omega) (.inl (by omega)) hx
    · exact C.no_source_outside_cyclic_interval hk hDis hc (by omega) (.inl hb) hx
  have hAway₁ {b c : ℕ}
      (C : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c))
      (hc : c < 14*q) (hb : 7*q+7 < b ∨ c < 7*q+3) {x y : V} (hx : x ∈ B 3 ∨ x ∈ B 7) :
      ¬ C.digraph.Adj x y := by
    rcases hx with hx | hx
    · rw [hRotate] at hx
      exact C.no_source_outside_cyclic_interval hk hDis hc (by omega) (hb.imp (by omega) id) hx
    · rw [hRotate] at hx
      exact C.no_source_outside_cyclic_interval hk hDis hc (by omega) (hb.imp id (by omega)) hx
  let M₀' := M₀.liftSubdivision T S₀ S₂ (by
    intro i p hi hp x hx
    have hs := hSlots₀ p hp x hx
    rcases hi with rfl | rfl
    · apply hOrd₀
      rintro ⟨z,rfl⟩
      exact hAway₀ E.third (by omega) (by omega) hs (P₃.shortcut z)
    · apply hOrd₂
      rintro ⟨z,rfl⟩
      exact hAway₀ E.fourth (by omega) (by omega) hs (P₄.shortcut z))
  let M₁' := M₁.liftSubdivision T S₁ S₃ (by
    intro i p hi hp x hx
    have hs := hSlots₁ p hp x hx
    rcases hi with rfl | rfl
    · apply hOrd₁
      rintro ⟨z,rfl⟩
      exact hAway₁ E.fifth (by omega) (.inl (by omega)) hs (P₅.shortcut z)
    · apply hOrd₃
      rintro ⟨z,rfl⟩
      exact hAway₁ E.second (by omega) (.inr (by omega)) hs (P₂.shortcut z))
  obtain ⟨F,hF,hFDis,hHam₀,hHam₁,hB₀,hB₁,hLast₀,hLast₁,hKeep⟩ :=
    cycle_absorber_pair_sweep T M₀' M₁' hTDis
  have hProtect₀ {b c : ℕ}
      (C : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c))
      (hc : c < 14*q) (hb : 7 < b) {x y : V} (he : C.digraph.Adj x y) (i : Fin 4) :
      M₀'.Protected i (.inl x) := by
    right
    intro p hp
    constructor
    · intro h
      have hs := hSlots₀ p hp x (.inl (Sum.inl.inj h))
      exact hAway₀ C hc hb hs he
    · intro h
      have hs := hSlots₀ p hp x (.inr (Sum.inl.inj h))
      exact hAway₀ C hc hb hs he
  have hProtect₁ {b c : ℕ}
      (C : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c))
      (hc : c < 14*q) (hb : 7*q+7 < b ∨ c < 7*q+3)
      {x y : V} (he : C.digraph.Adj x y) (i : Fin 4) :
      M₁'.Protected i (.inl x) := by
    right
    intro p hp
    constructor
    · intro h
      have hs := hSlots₁ p hp x (.inl (Sum.inl.inj h))
      exact hAway₁ C hc hb hs he
    · intro h
      have hs := hSlots₁ p hp x (.inr (Sum.inl.inj h))
      exact hAway₁ C hc hb hs he
  have hKeepExc (i : Fin 4) (z : Z) : F i (.inr z) = T i (.inr z) := by
    apply hKeep
    all_goals
      right
      intro p hp
      exact ⟨Sum.inr_ne_inl,Sum.inr_ne_inl⟩
  have hKeep₃ : P₃.original ≤ ⟨fun x y => F 0 x = y⟩ := P₃.keep_original (T 0) (F 0)
    (fun x y h => (h₀ x y).mp (.inl (.inr h))) (fun he =>
      hKeep 0 _ (hProtect₀ E.third (by omega) (by omega) he 0) (.inl (by decide))) (hKeepExc 0)
  have hKeep₅ : P₅.original ≤ ⟨fun x y => F 1 x = y⟩ := P₅.keep_original (T 1) (F 1)
    (fun x y h => (h₁ x y).mp (.inl (.inr h))) (fun he =>
      hKeep 1 _ (.inl (by decide)) (hProtect₁ E.fifth (by omega) (.inl (by omega)) he 1)) (hKeepExc 1)
  have hKeep₄ : P₄.original ≤ ⟨fun x y => F 2 x = y⟩ := P₄.keep_original (T 2) (F 2)
    (fun x y h => (h₂ x y).mp (.inr h)) (fun he =>
      hKeep 2 _ (hProtect₀ E.fourth (by omega) (by omega) he 2) (.inl (by decide))) (hKeepExc 2)
  have hKeep₂ : P₂.original ≤ ⟨fun x y => F 3 x = y⟩ := P₂.keep_original (T 3) (F 3)
    (fun x y h => (h₃ x y).mp (.inr h)) (fun he =>
      hKeep 3 _ (.inl (by decide)) (hProtect₁ E.second (by omega) (.inr (by omega)) he 3)) (hKeepExc 3)
  refine ⟨F,hF.trans hUnion,hFDis,hHam₀,hHam₁,hB₀,hB₁,hKeep₃,hKeep₅,hKeep₄,hKeep₂,?_,?_⟩
  · intro l
    refine (hLast₀ l).trans (hOrd₂ _ ?_)
    rintro ⟨z,hz⟩
    change P₄.source z = N.upper.rows.mark (l,Fin.last (2*m)) at hz
    have hx := N.upper.repair_start l
    rw [← hz] at hx
    exact E.fourth.no_source_outside_cyclic_interval hk hDis (by omega)
      (by omega) (.inl (by omega)) hx (P₄.shortcut z)
  · intro l
    refine (hLast₁ l).trans (hOrd₃ _ ?_)
    rintro ⟨z,hz⟩
    change P₂.source z = N.lower.rows.mark (l,Fin.last (2*m)) at hz
    have hx := N.lower.repair_start l
    rw [← hz,hRotate] at hx
    exact E.second.no_source_outside_cyclic_interval hk hDis (by omega)
      (by omega) (.inr (by omega)) hx (P₂.shortcut z)

end OverfullWork.DirectedRobustExpansion
