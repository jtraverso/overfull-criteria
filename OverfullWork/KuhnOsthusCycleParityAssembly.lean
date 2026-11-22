module

public import OverfullWork.KuhnOsthusCycleAbsorberOrderedSweep
public import OverfullWork.KuhnOsthusParityRepair

@[expose] public section


/-! Combine the two sweeps in Kühn–Osthus Lemma 10.2 and the repairs
in Lemma 10.4. The first two factors are the opposite-half splicings
from the start of the proof of Lemma 10.2. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical
variable {V I J : Type*} [Fintype V] {t : ℕ}

/-- The path anchors and switch schedule for one half of the cycle absorber. -/
structure CycleAbsorberSweepData (I : Type*) (F : Fin t → Equiv.Perm V) (i j : Fin t) where
  size : ℕ
  root : ℕ → V
  left : ℕ → V
  right : ℕ → V
  sources : ∀ p < size, left p ≠ right p
  distinct : ∀ p q, p < q → q < size →
    left q ≠ left p ∧ left q ≠ right p ∧ right q ≠ left p ∧ right q ≠ right p
  roots : ∀ p < size,
    (F i).SameCycle (root p) (left p) ∧ (F i).SameCycle (root (p+1)) (right p)
  cover : ∀ z, ∃ p ≤ size, (F i).SameCycle (root p) z
  cross : ∀ p < size, F i (left p) = F j (right p) ∧ F i (right p) = F j (left p)
  mark : Bool × I ↪ V
  step : Equiv.Perm I
  col : ℕ → I
  final : I
  reaches : ∀ c, step.SameCycle c final
  unused : ∀ p < size, col p ≠ final
  marks : ∀ p < size, left p = mark (false,col p) ∧ right p = mark (true,col p)
  order : OrderedReserve (F j) mark step

def CycleAbsorberSweepData.Protected {F : Fin t → Equiv.Perm V} {i j : Fin t}
    (D : CycleAbsorberSweepData I F i j) (a : Fin t) (v : V) : Prop :=
  (a ≠ i ∧ a ≠ j) ∨ ∀ p < D.size, v ≠ D.left p ∧ v ≠ D.right p

/-- Transport the schedule when changes have affected only other factors. -/
def CycleAbsorberSweepData.transport {F G : Fin t → Equiv.Perm V} {i j : Fin t}
    (D : CycleAbsorberSweepData I F i j) (hi : G i = F i) (hj : G j = F j) :
    CycleAbsorberSweepData I G i j :=
  { D with
    roots := by rw [hi]; exact D.roots
    cover := by rw [hi]; exact D.cover
    cross := by rw [hi,hj]; exact D.cross
    order := by rw [hj]; exact D.order }

theorem CycleAbsorberSweepData.sweep [Finite I] {F : Fin t → Equiv.Perm V} {i j : Fin t}
    (D : CycleAbsorberSweepData I F i j) (hij : i ≠ j)
    (hDis : ∀ a b, a ≠ b → ∀ z, F a z ≠ F b z) :
    ∃ G : Fin t → Equiv.Perm V,
      matchingUnion G = matchingUnion F ∧
      (∀ a b, a ≠ b → ∀ z, G a z ≠ G b z) ∧
      HasSpanningCycle (fun x y => G i x = y) ∧
      ((∀ v, (G j).SameCycle (D.mark (false,D.final)) v) ∨
        MarkedBicycle (G j) (D.mark (false,D.final)) (D.mark (true,D.final))) ∧
      (∀ b : Bool, G j (D.mark (b,D.final)) = F j (D.mark (b,D.final))) ∧
      ∀ a z, D.Protected a z → G a z = F a z := by
  obtain ⟨G,hUnion,hDisG,hHam,hAux,_,hL,hR,_,hKeep⟩ :=
    c4_sweep_with_ordered_reserve F hij D.size D.root D.left D.right D.sources
      D.distinct D.roots D.cover D.cross hDis D.mark D.step D.col D.final D.reaches D.unused D.marks D.order
  exact ⟨G,hUnion,hDisG,hHam,hAux,fun b => by cases b; exact hL; exact hR,hKeep⟩

/-- The normalized one-round absorption of Lemma 10.4. The cycle and
parity reserves are supplied on the original vertex set, with the
common repair marks and the two opposite-half primary factors. -/
theorem cycle_and_parity_absorption_round [Finite I] [Finite J]
    (F : Fin 7 → Equiv.Perm V)
    (D : CycleAbsorberSweepData I F 0 2) (E : CycleAbsorberSweepData J F 1 3)
    (C : ParityRepairConfiguration F)
    (hD : ∀ b : Bool, D.mark (b,D.final) = C.mark (b,0))
    (hE : ∀ b : Bool, E.mark (b,E.final) = C.mark (b,1))
    (hDis : ∀ a b, a ≠ b → ∀ z, F a z ≠ F b z) :
    ∃ G : Fin 7 → Equiv.Perm V,
      matchingUnion G = matchingUnion F ∧
      (∀ a b, a ≠ b → ∀ z, G a z ≠ G b z) ∧
      (∀ i, HasSpanningCycle (fun v w => G i v = w)) ∧
      ∀ i v, D.Protected i v → E.Protected i v → C.Protected i v → G i v = F i v := by
  obtain ⟨A,hA,hDisA,hHam0,hAuxA,hFinalA,hKeepA⟩ := D.sweep (by decide) hDis
  have hAoff {i : Fin 7} (hi : i ≠ 0 ∧ i ≠ 2) : A i = F i := by
    ext z
    exact hKeepA i z (.inl hi)
  let E' := E.transport (hAoff (by decide)) (hAoff (by decide))
  obtain ⟨B,hBA,hDisB,hHam1,hAuxB,hFinalB,hKeepB⟩ := E'.sweep (by decide) hDisA
  have hBoff {i : Fin 7} (hi : i ≠ 1 ∧ i ≠ 3) : B i = A i := by
    ext z
    exact hKeepB i z (.inl hi)
  have hB0 : B 0 = A 0 := hBoff (by decide)
  have hB2 : B 2 = A 2 := hBoff (by decide)
  have hB4 : B 4 = F 4 := (hBoff (by decide)).trans (hAoff (by decide))
  have hB5 : B 5 = F 5 := (hBoff (by decide)).trans (hAoff (by decide))
  have hB6 : B 6 = F 6 := (hBoff (by decide)).trans (hAoff (by decide))
  have hArc₂ (b : Bool) : B 2 (C.mark (b,0)) = F 2 (C.mark (b,0)) := by
    rw [← hD b,hB2]
    exact hFinalA b
  have hArc₃ (b : Bool) : B 3 (C.mark (b,1)) = F 3 (C.mark (b,1)) := by
    rw [← hE b]
    exact (hFinalB b).trans (congrArg (fun p : Equiv.Perm V => p (E.mark (b,E.final))) (hAoff (i := 3) (by decide)))
  let C' : ParityRepairConfiguration B := {
    mark := C.mark
    order := by rw [hB4]; exact C.order
    auxLeft := C.auxLeft
    auxRight := C.auxRight
    crossFirst := by rw [hB4,hArc₂ false,hArc₂ true]; exact C.crossFirst
    crossSecond := by rw [hB4,hArc₃ false,hArc₃ true]; exact C.crossSecond
    crossAux := by rw [hB5,hB6]; exact C.crossAux
    crossTriple := by rw [hB4,hB5,hB6]; exact C.crossTriple
    auxBicycles := by rw [hB5,hB6]; exact C.auxBicycles
    tripleBicycles := by rw [hB5,hB6]; exact C.tripleBicycles }
  have h₀ : HasSpanningCycle (fun v w => B 0 v = w) := by rw [hB0]; exact hHam0
  have hModes (σ : Equiv.Perm V) (l r : V)
      (h : (∀ z, σ.SameCycle l z) ∨ MarkedBicycle σ l r) :
      ∃ b : Bool, if b then MarkedBicycle σ l r else ∀ z, σ.SameCycle l z := by
    rcases h with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  have hAux₂ : (∀ v, (B 2).SameCycle (C.mark (false,0)) v) ∨
      MarkedBicycle (B 2) (C.mark (false,0)) (C.mark (true,0)) := by
    rw [← hD false,← hD true,hB2]
    exact hAuxA
  have hAux₃ : (∀ v, (B 3).SameCycle (C.mark (false,1)) v) ∨
      MarkedBicycle (B 3) (C.mark (false,1)) (C.mark (true,1)) := by
    rw [← hE false,← hE true]
    exact hAuxB
  obtain ⟨b₀,hMode₀⟩ := hModes _ _ _ hAux₂
  obtain ⟨b₁,hMode₁⟩ := hModes _ _ _ hAux₃
  obtain ⟨G,hGB,hDisG,hHam,hKeepG⟩ :=
    parity_repair_seven_factors B C' hDisB h₀ hHam1 b₀ b₁ hMode₀ hMode₁
  exact ⟨G,hGB.trans (hBA.trans hA),hDisG,hHam,fun i v hd he hc =>
    (hKeepG i v hc).trans ((hKeepB i v he).trans (hKeepA i v hd))⟩

end OverfullWork.DirectedRobustExpansion
