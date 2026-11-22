module

public import OverfullWork.KuhnOsthusPhysicalCycleSweep
public import OverfullWork.KuhnOsthusRestoredSegments

@[expose] public section


/-! The sweeps take place on the original vertex set. Parallel
shortcut occurrences in the projection need no arc-disjointness
assumption there. -/
namespace OverfullWork.DirectedRobustExpansion

open Function
open scoped Classical
variable {V Z I : Type*} [Fintype V] [Fintype Z] {t : ℕ}

/-- The cross matchings, the order on the reserve, and the covering
property survive restoration. The switch arcs themselves are ordinary. -/
noncomputable def CycleAbsorberSweepData.liftSubdivision
    {F : Fin t → Equiv.Perm V} {i j : Fin t}
    (D : CycleAbsorberSweepData I F i j) (G : Fin t → Equiv.Perm (V ⊕ Z))
    (P : MarkedCycleSegments (G i) Embedding.inl (F i))
    (Q : MarkedCycleSegments (G j) Embedding.inl (F j))
    (hOrd : ∀ a p, (a = i ∨ a = j) → p < D.size → ∀ x, x = D.left p ∨ x = D.right p →
      G a (.inl x) = .inl (F a x)) :
    CycleAbsorberSweepData I G i j where
  size := D.size
  root p := .inl (D.root p)
  left p := .inl (D.left p)
  right p := .inl (D.right p)
  sources p hp he := D.sources p hp (Sum.inl.inj he)
  distinct p q hp hq := by
    obtain ⟨h₁,h₂,h₃,h₄⟩ := D.distinct p q hp hq
    exact ⟨fun h => h₁ (Sum.inl.inj h),fun h => h₂ (Sum.inl.inj h),
      fun h => h₃ (Sum.inl.inj h),fun h => h₄ (Sum.inl.inj h)⟩
  roots p hp :=
    ⟨(P.sameCycle _ _).mpr (D.roots p hp).1,(P.sameCycle _ _).mpr (D.roots p hp).2⟩
  cover z := by
    obtain ⟨v,hv⟩ := P.cycle_meets_mark z
    obtain ⟨p,hp,h⟩ := D.cover v
    exact ⟨p,hp,((P.sameCycle _ _).mpr h).trans hv⟩
  cross p hp := by
    rw [hOrd i p (.inl rfl) hp _ (.inl rfl),hOrd j p (.inr rfl) hp _ (.inr rfl),
      hOrd i p (.inl rfl) hp _ (.inr rfl),hOrd j p (.inr rfl) hp _ (.inl rfl)]
    exact ⟨congrArg Sum.inl (D.cross p hp).1,congrArg Sum.inl (D.cross p hp).2⟩
  mark := D.mark.trans Embedding.inl
  step := D.step
  col := D.col
  final := D.final
  reaches := D.reaches
  unused := D.unused
  marks p hp := ⟨congrArg Sum.inl (D.marks p hp).1,congrArg Sum.inl (D.marks p hp).2⟩
  order := by
    obtain ⟨ρ,⟨S⟩,hρ⟩ := D.order
    exact ⟨ρ,⟨Q.compose S⟩,hρ⟩

omit [Fintype Z] in
/-- Apply the two independent sweeps, retaining the original union of
arcs and the two reserved pairs of repair successors. -/
theorem cycle_absorber_pair_sweep [Finite I] {J : Type*} [Finite J]
    (F : Fin 4 → Equiv.Perm V)
    (D : CycleAbsorberSweepData I F 0 2) (E : CycleAbsorberSweepData J F 1 3)
    (hDis : ∀ a b, a ≠ b → ∀ z, F a z ≠ F b z) :
    ∃ G : Fin 4 → Equiv.Perm V,
      matchingUnion G = matchingUnion F ∧
      (∀ a b, a ≠ b → ∀ z, G a z ≠ G b z) ∧
      HasSpanningCycle (fun x y => G 0 x = y) ∧ HasSpanningCycle (fun x y => G 1 x = y) ∧
      ((∀ v, (G 2).SameCycle (D.mark (false,D.final)) v) ∨
        MarkedBicycle (G 2) (D.mark (false,D.final)) (D.mark (true,D.final))) ∧
      ((∀ v, (G 3).SameCycle (E.mark (false,E.final)) v) ∨
        MarkedBicycle (G 3) (E.mark (false,E.final)) (E.mark (true,E.final))) ∧
      (∀ b, G 2 (D.mark (b,D.final)) = F 2 (D.mark (b,D.final))) ∧
      (∀ b, G 3 (E.mark (b,E.final)) = F 3 (E.mark (b,E.final))) ∧
      ∀ a x, D.Protected a x → E.Protected a x → G a x = F a x := by
  obtain ⟨A,hA,hDisA,hHamA,hAuxA,hFinalA,hKeepA⟩ := D.sweep (by decide) hDis
  have hAoff (a : Fin 4) (ha : a ≠ 0 ∧ a ≠ 2) : A a = F a := by
    ext z
    exact hKeepA a z (.inl ha)
  let E' := E.transport (hAoff 1 (by decide)) (hAoff 3 (by decide))
  obtain ⟨G,hG,hDisG,hHamG,hAuxG,hFinalG,hKeepG⟩ := E'.sweep (by decide) hDisA
  have hGoff (a : Fin 4) (ha : a ≠ 1 ∧ a ≠ 3) : G a = A a := by
    ext z
    exact hKeepG a z (.inl ha)
  have h₀ := hGoff 0 (by decide)
  have h₂ := hGoff 2 (by decide)
  refine ⟨G,hG.trans hA,hDisG,?_,hHamG,?_,hAuxG,?_,?_,
    fun a x hd he => (hKeepG a x he).trans (hKeepA a x hd)⟩
  · rwa [h₀]
  · rwa [h₂]
  · rw [h₂]
    exact hFinalA
  · intro b
    exact (hFinalG b).trans (congrArg (fun p : Equiv.Perm V => p (E.mark (b,E.final))) (hAoff 3 (by decide)))

end OverfullWork.DirectedRobustExpansion
