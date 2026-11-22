module

public import OverfullWork.KuhnOsthusLemma102
public import OverfullWork.KuhnOsthusParityRepair

@[expose] public section


/-! The parity repair of Lemma 10.4 on original vertices. The three
reserve cycles are lifted through their own exceptional systems. -/
namespace OverfullWork.DirectedRobustExpansion

open Function
open scoped Classical
variable {V Z : Type*}

/-- The lifted marks of a bicycle remain on different cycles, and
these two cycles cover the entire subdivided graph. -/
theorem MarkedCycleSegments.liftBicycle [Finite V] [Finite Z]
    {σ : Equiv.Perm V} {τ : Equiv.Perm Z} {mark : V ↪ Z}
    (S : MarkedCycleSegments τ mark σ) {x y : V} (B : MarkedBicycle σ x y) :
    MarkedBicycle τ (mark x) (mark y) := by
  refine ⟨fun h => B.1 ((S.sameCycle _ _).mp h),?_⟩
  intro z
  obtain ⟨v,hv⟩ := S.cycle_meets_mark z
  exact (B.2 v).imp (fun h => ((S.sameCycle _ _).mpr h).trans hv)
    (fun h => ((S.sameCycle _ _).mpr h).trans hv)

/-- Only the switch successors must be carried without subdivision.
The projected permutations can have coincident arcs elsewhere. -/
noncomputable def ParityRepairConfiguration.liftSubdivision [Finite V] [Finite Z]
    {F : Fin 7 → Equiv.Perm V} (C : ParityRepairConfiguration F)
    (G : Fin 7 → Equiv.Perm (V ⊕ Z))
    (S₄ : MarkedCycleSegments (G 4) Embedding.inl (F 4))
    (S₅ : MarkedCycleSegments (G 5) Embedding.inl (F 5))
    (S₆ : MarkedCycleSegments (G 6) Embedding.inl (F 6))
    (hOrd : ∀ a x, ¬ C.Protected a x → G a (.inl x) = .inl (F a x)) :
    ParityRepairConfiguration G := by
  have hFirst (a : Fin 7) (ha : a ∈ ({2,4} : Finset (Fin 7))) (b : Bool) :
      G a (.inl (C.mark (b,0))) = .inl (F a (C.mark (b,0))) := by
    apply hOrd
    intro h
    have h' := h.1.resolve_left (fun he => he ha)
    cases b
    · exact h'.1 rfl
    · exact h'.2 rfl
  have hSecond (a : Fin 7) (ha : a ∈ ({3,4} : Finset (Fin 7))) (b : Bool) :
      G a (.inl (C.mark (b,1))) = .inl (F a (C.mark (b,1))) := by
    apply hOrd
    intro h
    have h' := h.2.1.resolve_left (fun he => he ha)
    cases b
    · exact h'.1 rfl
    · exact h'.2 rfl
  have hAux (a : Fin 7) (ha : a ∈ ({5,6} : Finset (Fin 7))) :
      G a (.inl C.auxLeft) = .inl (F a C.auxLeft) ∧
      G a (.inl C.auxRight) = .inl (F a C.auxRight) :=
    ⟨hOrd _ _ (fun h => (h.2.2.1.resolve_left (fun he => he ha)).1 rfl),
      hOrd _ _ (fun h => (h.2.2.1.resolve_left (fun he => he ha)).2 rfl)⟩
  have hTriple (a : Fin 7) (ha : a ∈ ({4,5,6} : Finset (Fin 7))) (b : Bool) :
      G a (.inl (C.mark (b,2))) = .inl (F a (C.mark (b,2))) := by
    apply hOrd
    intro h
    have h' := h.2.2.2.resolve_left (fun he => he ha)
    cases b
    · exact h'.1 rfl
    · exact h'.2 rfl
  refine {
    mark := C.mark.trans Embedding.inl
    order := S₄.compose C.order
    auxLeft := .inl C.auxLeft
    auxRight := .inl C.auxRight
    crossFirst := ?_
    crossSecond := ?_
    crossAux := ?_
    crossTriple := ?_
    auxBicycles := ⟨S₅.liftBicycle C.auxBicycles.1,S₆.liftBicycle C.auxBicycles.2⟩
    tripleBicycles := ⟨S₅.liftBicycle C.tripleBicycles.1,S₆.liftBicycle C.tripleBicycles.2⟩ }
  · change G 2 (.inl (C.mark (false,0))) = G 4 (.inl (C.mark (true,0))) ∧
      G 2 (.inl (C.mark (true,0))) = G 4 (.inl (C.mark (false,0)))
    rw [hFirst 2 (by decide) false,hFirst 4 (by decide) true,
      hFirst 2 (by decide) true,hFirst 4 (by decide) false]
    exact ⟨congrArg Sum.inl C.crossFirst.1,congrArg Sum.inl C.crossFirst.2⟩
  · change G 3 (.inl (C.mark (false,1))) = G 4 (.inl (C.mark (true,1))) ∧
      G 3 (.inl (C.mark (true,1))) = G 4 (.inl (C.mark (false,1)))
    rw [hSecond 3 (by decide) false,hSecond 4 (by decide) true,
      hSecond 3 (by decide) true,hSecond 4 (by decide) false]
    exact ⟨congrArg Sum.inl C.crossSecond.1,congrArg Sum.inl C.crossSecond.2⟩
  · rw [(hAux 5 (by decide)).1,(hAux 6 (by decide)).2,
      (hAux 5 (by decide)).2,(hAux 6 (by decide)).1]
    exact ⟨congrArg Sum.inl C.crossAux.1,congrArg Sum.inl C.crossAux.2⟩
  · change G 4 (.inl (C.mark (true,2))) = G 5 (.inl (C.mark (false,2))) ∧
      G 5 (.inl (C.mark (true,2))) = G 6 (.inl (C.mark (false,2))) ∧
      G 6 (.inl (C.mark (true,2))) = G 4 (.inl (C.mark (false,2)))
    rw [hTriple 4 (by decide) true,hTriple 5 (by decide) false,hTriple 5 (by decide) true,
      hTriple 6 (by decide) false,hTriple 6 (by decide) true,hTriple 4 (by decide) false]
    exact ⟨congrArg Sum.inl C.crossTriple.1,congrArg Sum.inl C.crossTriple.2.1,
      congrArg Sum.inl C.crossTriple.2.2⟩

/-- Once the two original sweeps have run, the four parity cases
give seven Hamilton cycles with the exact original arc union. -/
theorem parity_repair_after_original_sweeps [Fintype V] [Fintype Z]
    {F : Fin 7 → Equiv.Perm V} (C : ParityRepairConfiguration F)
    (G : Fin 7 → Equiv.Perm (V ⊕ Z))
    (S₄ : MarkedCycleSegments (G 4) Embedding.inl (F 4))
    (S₅ : MarkedCycleSegments (G 5) Embedding.inl (F 5))
    (S₆ : MarkedCycleSegments (G 6) Embedding.inl (F 6))
    (hOrd : ∀ a x, ¬ C.Protected a x → G a (.inl x) = .inl (F a x))
    (hDis : ∀ a b, a ≠ b → ∀ z, G a z ≠ G b z)
    (h0 : HasSpanningCycle (fun v w => G 0 v = w)) (h1 : HasSpanningCycle (fun v w => G 1 v = w))
    (h₂ : (∀ v, (G 2).SameCycle (.inl (C.mark (false,0))) v) ∨
      MarkedBicycle (G 2) (.inl (C.mark (false,0))) (.inl (C.mark (true,0))))
    (h₃ : (∀ v, (G 3).SameCycle (.inl (C.mark (false,1))) v) ∨
      MarkedBicycle (G 3) (.inl (C.mark (false,1))) (.inl (C.mark (true,1)))) :
    ∃ H : Fin 7 → Equiv.Perm (V ⊕ Z),
      matchingUnion H = matchingUnion G ∧ (∀ a b, a ≠ b → ∀ v, H a v ≠ H b v) ∧
      (∀ i, HasSpanningCycle (fun v w => H i v = w)) ∧
      (∀ i v, C.Protected i v → H i (.inl v) = G i (.inl v)) ∧
      ∀ i z, H i (.inr z) = G i (.inr z) := by
  let D := C.liftSubdivision G S₄ S₅ S₆ hOrd
  have mode (p : Equiv.Perm (V ⊕ Z)) (x y : V ⊕ Z)
      (h : (∀ v, p.SameCycle x v) ∨ MarkedBicycle p x y) :
      ∃ b : Bool, if b then MarkedBicycle p x y else ∀ v, p.SameCycle x v := by
    exact h.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  obtain ⟨b₀,hMode₀⟩ := mode _ _ _ h₂
  obtain ⟨b₁,hMode₁⟩ := mode _ _ _ h₃
  obtain ⟨H,hH,hDisH,hHam,hKeep⟩ := parity_repair_seven_factors G D hDis h0 h1 b₀ b₁ hMode₀ hMode₁
  refine ⟨H,hH,hDisH,hHam,?_,?_⟩
  · intro i v h
    apply hKeep
    exact ⟨h.1.imp_right (fun h => ⟨fun e => h.1 (Sum.inl.inj e),fun e => h.2 (Sum.inl.inj e)⟩),
      h.2.1.imp_right (fun h => ⟨fun e => h.1 (Sum.inl.inj e),fun e => h.2 (Sum.inl.inj e)⟩),
      h.2.2.1.imp_right (fun h => ⟨fun e => h.1 (Sum.inl.inj e),fun e => h.2 (Sum.inl.inj e)⟩),
      h.2.2.2.imp_right (fun h => ⟨fun e => h.1 (Sum.inl.inj e),fun e => h.2 (Sum.inl.inj e)⟩)⟩
  · intro i z
    apply hKeep
    exact ⟨.inr ⟨Sum.inr_ne_inl,Sum.inr_ne_inl⟩,.inr ⟨Sum.inr_ne_inl,Sum.inr_ne_inl⟩,
      .inr ⟨Sum.inr_ne_inl,Sum.inr_ne_inl⟩,.inr ⟨Sum.inr_ne_inl,Sum.inr_ne_inl⟩⟩

end OverfullWork.DirectedRobustExpansion
