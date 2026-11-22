module

public import OverfullWork.KuhnOsthusParityReserveOrder

@[expose] public section


/-! The four cases in the proof of Kühn–Osthus Lemma 10.4, given the
four factors from the cycle absorber and the three parity reserves. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*}

/-- Switch geometry and the order of the three pairs of marks on B₁.
The factors are F₁, F₂, F₃, F₄, B₁, B₂, B₃ in this order. -/
structure ParityRepairConfiguration (F : Fin 7 → Equiv.Perm V) where
  mark : Bool × Fin 3 ↪ V
  order : MarkedCycleSegments (F 4) mark (Equiv.prodCongr (Equiv.refl Bool) (finRotate 3))
  auxLeft : V
  auxRight : V
  crossFirst :
    F 2 (mark (false,0)) = F 4 (mark (true,0)) ∧
    F 2 (mark (true,0)) = F 4 (mark (false,0))
  crossSecond :
    F 3 (mark (false,1)) = F 4 (mark (true,1)) ∧
    F 3 (mark (true,1)) = F 4 (mark (false,1))
  crossAux : F 5 auxLeft = F 6 auxRight ∧ F 5 auxRight = F 6 auxLeft
  crossTriple :
    F 4 (mark (true,2)) = F 5 (mark (false,2)) ∧
    F 5 (mark (true,2)) = F 6 (mark (false,2)) ∧
    F 6 (mark (true,2)) = F 4 (mark (false,2))
  auxBicycles : MarkedBicycle (F 5) auxLeft auxRight ∧ MarkedBicycle (F 6) auxLeft auxRight
  tripleBicycles :
    MarkedBicycle (F 5) (mark (false,2)) (mark (true,2)) ∧
    MarkedBicycle (F 6) (mark (false,2)) (mark (true,2))

/-- At a protected source, none of the possible exchanges changes the
outgoing arc in the specified factor. -/
def ParityRepairConfiguration.Protected {F : Fin 7 → Equiv.Perm V}
    (C : ParityRepairConfiguration F) (i : Fin 7) (v : V) : Prop :=
  (i ∉ ({2,4} : Finset (Fin 7)) ∨ v ≠ C.mark (false,0) ∧ v ≠ C.mark (true,0)) ∧
  (i ∉ ({3,4} : Finset (Fin 7)) ∨ v ≠ C.mark (false,1) ∧ v ≠ C.mark (true,1)) ∧
  (i ∉ ({5,6} : Finset (Fin 7)) ∨ v ≠ C.auxLeft ∧ v ≠ C.auxRight) ∧
  (i ∉ ({4,5,6} : Finset (Fin 7)) ∨ v ≠ C.mark (false,2) ∧ v ≠ C.mark (true,2))

private noncomputable def repairIf (F : Fin 7 → Equiv.Perm V) (b : Bool)
    (i j : Fin 7) (x y : V) : Fin 7 → Equiv.Perm V :=
  if b then switchFactors F {i,j} x y else F

private theorem repair_if_at (F : Fin 7 → Equiv.Perm V) (b : Bool)
    (i j : Fin 7) (x y : V) {a : Fin 7} (ha : a ∈ ({i,j} : Finset (Fin 7))) :
    repairIf F b i j x y a = if b then switchSuccessors (F a) x y else F a := by
  cases b <;> simp [repairIf,switchFactors,ha]

private theorem repair_if_protects (F : Fin 7 → Equiv.Perm V) (b : Bool)
    (i j : Fin 7) (x y : V) {a : Fin 7} {z : V}
    (h : a ∉ ({i,j} : Finset (Fin 7)) ∨ z ≠ x ∧ z ≠ y) :
    repairIf F b i j x y a z = F a z := by
  cases b
  · rfl
  · exact switchFactors_protects F {i,j} h

private theorem repair_if_off (F : Fin 7 → Equiv.Perm V) (b : Bool)
    (i j : Fin 7) (x y : V) {a : Fin 7} (ha : a ∉ ({i,j} : Finset (Fin 7))) :
    repairIf F b i j x y a = F a := by
  ext z
  exact repair_if_protects F b i j x y (.inl ha)

variable [Fintype V]

private theorem repair_if_hamilton (F : Fin 7 → Equiv.Perm V) (b : Bool)
    (i j : Fin 7) (x y : V)
    (hMode : if b then MarkedBicycle (F i) x y else ∀ v, (F i).SameCycle x v)
    (hCross : F i x = F j y ∧ F i y = F j x)
    (hDis : ∀ a b, a ≠ b → ∀ v, F a v ≠ F b v) :
    let G := repairIf F b i j x y
    matchingUnion G = matchingUnion F ∧ (∀ a b, a ≠ b → ∀ v, G a v ≠ G b v) ∧
      HasSpanningCycle (fun v w => G i v = w) := by
  cases b
  · exact ⟨rfl,hDis,spanning_cycle_of_single_orbit (F i) x hMode⟩
  · obtain ⟨hUnion,hDis'⟩ := c4_exchange_conserves F hCross.1 hCross.2 hDis
    exact ⟨hUnion,hDis', by
      simpa [repairIf,switchFactors] using switchSuccessors_hamilton_of_markedBicycle (F i) hMode⟩

/-- Local conclusion of Lemma 10.4. The inputs record the structural
conditions of the cycle and parity absorbers on seven physical factors. -/
theorem parity_repair_seven_factors (F : Fin 7 → Equiv.Perm V)
    (C : ParityRepairConfiguration F)
    (hDis : ∀ a b, a ≠ b → ∀ v, F a v ≠ F b v)
    (h0 : HasSpanningCycle (fun v w => F 0 v = w))
    (h1 : HasSpanningCycle (fun v w => F 1 v = w))
    (b₀ b₁ : Bool)
    (hMode₀ : if b₀ then MarkedBicycle (F 2) (C.mark (false,0)) (C.mark (true,0))
      else ∀ v, (F 2).SameCycle (C.mark (false,0)) v)
    (hMode₁ : if b₁ then MarkedBicycle (F 3) (C.mark (false,1)) (C.mark (true,1))
      else ∀ v, (F 3).SameCycle (C.mark (false,1)) v) :
    ∃ G : Fin 7 → Equiv.Perm V,
      matchingUnion G = matchingUnion F ∧ (∀ a b, a ≠ b → ∀ v, G a v ≠ G b v) ∧
      (∀ i, HasSpanningCycle (fun v w => G i v = w)) ∧
      ∀ i v, C.Protected i v → G i v = F i v := by
  let x (c : Fin 3) := C.mark (false,c)
  let y (c : Fin 3) := C.mark (true,c)
  let A := repairIf F b₀ 2 4 (x 0) (y 0)
  let B := repairIf A b₁ 3 4 (x 1) (y 1)
  obtain ⟨hA,hDisA,hHam2⟩ := repair_if_hamilton F b₀ 2 4 (x 0) (y 0) hMode₀ C.crossFirst hDis
  have hA3 : A 3 = F 3 := repair_if_off F b₀ 2 4 (x 0) (y 0) (by decide)
  have hInj (a b : Bool × Fin 3) (h : a ≠ b) : C.mark a ≠ C.mark b := C.mark.injective.ne h
  have hAx : A 4 (x 1) = F 4 (x 1) :=
    repair_if_protects F b₀ 2 4 (x 0) (y 0) (.inr ⟨hInj _ _ (by decide),hInj _ _ (by decide)⟩)
  have hAy : A 4 (y 1) = F 4 (y 1) :=
    repair_if_protects F b₀ 2 4 (x 0) (y 0) (.inr ⟨hInj _ _ (by decide),hInj _ _ (by decide)⟩)
  have hModeB : if b₁ then MarkedBicycle (A 3) (x 1) (y 1)
      else ∀ v, (A 3).SameCycle (x 1) v := hA3.symm ▸ hMode₁
  have hCrossB : A 3 (x 1) = A 4 (y 1) ∧ A 3 (y 1) = A 4 (x 1) := by
    rw [hA3,hAx,hAy]
    exact C.crossSecond
  obtain ⟨hBA,hDisB,hHam3⟩ := repair_if_hamilton A b₁ 3 4 (x 1) (y 1) hModeB hCrossB hDisA
  have hB : matchingUnion B = matchingUnion F := hBA.trans hA
  have hBoff {a : Fin 7} (ha : a ∉ ({3,4} : Finset (Fin 7)))
      (hb : a ∉ ({2,4} : Finset (Fin 7))) : B a = F a :=
    (repair_if_off A b₁ 3 4 (x 1) (y 1) ha).trans (repair_if_off F b₀ 2 4 (x 0) (y 0) hb)
  have hB0 : HasSpanningCycle (fun v w => B 0 v = w) := by
    rw [hBoff (a := 0) (by decide) (by decide)]
    exact h0
  have hB1 : HasSpanningCycle (fun v w => B 1 v = w) := by
    rw [hBoff (a := 1) (by decide) (by decide)]
    exact h1
  have hBA2 : B 2 = A 2 := repair_if_off A b₁ 3 4 (x 1) (y 1) (by decide)
  have hB2 : HasSpanningCycle (fun v w => B 2 v = w) := by
    rw [hBA2]
    exact hHam2
  have hB5 : B 5 = F 5 := hBoff (by decide) (by decide)
  have hB6 : B 6 = F 6 := hBoff (by decide) (by decide)
  have hB4at {z : V} (h₀ : z ≠ x 0 ∧ z ≠ y 0) (h₁ : z ≠ x 1 ∧ z ≠ y 1) :
      B 4 z = F 4 z :=
    (repair_if_protects A b₁ 3 4 (x 1) (y 1) (.inr h₁)).trans
      (repair_if_protects F b₀ 2 4 (x 0) (y 0) (.inr h₀))
  have hB4x : B 4 (x 2) = F 4 (x 2) :=
    hB4at ⟨hInj _ _ (by decide),hInj _ _ (by decide)⟩ ⟨hInj _ _ (by decide),hInj _ _ (by decide)⟩
  have hB4y : B 4 (y 2) = F 4 (y 2) :=
    hB4at ⟨hInj _ _ (by decide),hInj _ _ (by decide)⟩ ⟨hInj _ _ (by decide),hInj _ _ (by decide)⟩
  have hProtectB (a : Fin 7) (v : V) (h : C.Protected a v) : B a v = F a v :=
    (repair_if_protects A b₁ 3 4 (x 1) (y 1) h.2.1).trans
      (repair_if_protects F b₀ 2 4 (x 0) (y 0) h.1)
  have hA4 : A 4 = if b₀ then switchSuccessors (F 4) (x 0) (y 0) else F 4 :=
    repair_if_at F b₀ 2 4 (x 0) (y 0) (by decide)
  have hB4 : B 4 = if b₁ then switchSuccessors (A 4) (x 1) (y 1) else A 4 :=
    repair_if_at A b₁ 3 4 (x 1) (y 1) (by decide)
  have finishTriple (hMarked : MarkedBicycle (B 4) (x 2) (y 2)) :
      ∃ G : Fin 7 → Equiv.Perm V,
        matchingUnion G = matchingUnion F ∧ (∀ a b, a ≠ b → ∀ v, G a v ≠ G b v) ∧
        (∀ i, HasSpanningCycle (fun v w => G i v = w)) ∧
        ∀ i v, C.Protected i v → G i v = F i v := by
    let G := switchFactors B {4,5,6} (x 2) (y 2)
    have hc : B 4 (y 2) = B 5 (x 2) ∧ B 5 (y 2) = B 6 (x 2) ∧ B 6 (y 2) = B 4 (x 2) := by
      rw [hB4y,hB5,hB6,hB4x]
      exact C.crossTriple
    obtain ⟨hGB,hDisG,hHam,hKeep⟩ := k23_exchange_hamilton_of_markedBicycles B
      (show (4 : Fin 7) ≠ 5 by decide) (show (4 : Fin 7) ≠ 6 by decide) (show (5 : Fin 7) ≠ 6 by decide)
      hMarked (hB5 ▸ C.tripleBicycles.1) (hB6 ▸ C.tripleBicycles.2) hc.1 hc.2.1 hc.2.2 hDisB
    refine ⟨G,hGB.trans hB,hDisG,?_,fun a v h => (hKeep a v h.2.2.2).trans (hProtectB a v h)⟩
    intro a
    by_cases ha : a ∈ ({4,5,6} : Finset (Fin 7))
    · exact hHam a ha
    simp only [G,switchFactors,if_neg ha]
    fin_cases a <;> first | assumption | exact False.elim (ha (by decide))
  have finishPair (hHam4 : HasSpanningCycle (fun v w => B 4 v = w)) :
      ∃ G : Fin 7 → Equiv.Perm V,
        matchingUnion G = matchingUnion F ∧ (∀ a b, a ≠ b → ∀ v, G a v ≠ G b v) ∧
        (∀ i, HasSpanningCycle (fun v w => G i v = w)) ∧
        ∀ i v, C.Protected i v → G i v = F i v := by
    let G := switchFactors B {5,6} C.auxLeft C.auxRight
    have hc : B 5 C.auxLeft = B 6 C.auxRight ∧ B 5 C.auxRight = B 6 C.auxLeft := by
      rw [hB5,hB6]
      exact C.crossAux
    obtain ⟨hGB,hDisG,hHam5,hHam6⟩ := c4_exchange_hamilton_of_markedBicycles B
      (hB5 ▸ C.auxBicycles.1) (hB6 ▸ C.auxBicycles.2) hc.1 hc.2 hDisB
    refine ⟨G,hGB.trans hB,hDisG,?_,fun a v h =>
      (switchFactors_protects B {5,6} h.2.2.1).trans (hProtectB a v h)⟩
    intro a
    fin_cases a
    · simpa [G,switchFactors] using hB0
    · simpa [G,switchFactors] using hB1
    · simpa [G,switchFactors] using hB2
    · simpa [G,switchFactors] using hHam3
    · simpa [G,switchFactors] using hHam4
    · exact hHam5
    · exact hHam6
  rw [hA4] at hB4
  cases b₀ <;> cases b₁
  · apply finishTriple
    rw [hB4]
    exact pca6_initial_markedBicycle (F 4) C.mark C.order 2
  · apply finishPair
    simp only [hB4,Bool.false_eq_true,if_false,if_true]
    exact switchSuccessors_hamilton_of_markedBicycle (F 4)
      (pca6_initial_markedBicycle (F 4) C.mark C.order 1)
  · apply finishPair
    simp only [hB4,Bool.false_eq_true,if_false,if_true]
    exact switchSuccessors_hamilton_of_markedBicycle (F 4)
      (pca6_initial_markedBicycle (F 4) C.mark C.order 0)
  · apply finishTriple
    rw [hB4]
    exact pca6_double_exchange_markedBicycle (F 4) C.mark C.order

end OverfullWork.DirectedRobustExpansion
