module

public import OverfullWork.KuhnOsthusChordRoundConstruction
public import OverfullWork.KuhnOsthusPreparedChordSystems

@[expose] public section


/-! Prepare an original chord round directly from one residue factor,
the paired complete exceptional systems, and its walk bank. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedDemandHall
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

/-- A round of Lemma 9.7 gives exact original arc ownership and
the free-pair data used by the chord completion. The original
exceptional paths remain attached to the prescribed cycles. -/
theorem prepare_original_chord_round {n b g count cap scale ell k m : ℕ} [NeZero g]
    (Z : Finset V) (rank : ↥Zᶜ → Fin (n+2)) (quarter : ↥Zᶜ → Fin 4)
    (parent : Fin (n+2) → I) (s : Equiv.Perm I) (root : I)
    (σ : Equiv.Perm ↥Zᶜ) (H : Digraph ↥Zᶜ) (kind : ↥Zᶜ → Fin g)
    (P : OrderedResidueMatchings H kind (b*10) count cap 10)
    (E : Digraph V) (C : Fin (b*10) → Digraph V) (owner : Fin (n+2) → I)
    (Q : Fin (n+2) × Fin 4 → Finset ↥Zᶜ)
    (M : ∀ j : Fin (n+2) × Fin 4, Fin k → Q j ≃ Q (finRotate (n+2) j.1,j.2))
    (hCycle : ∀ i, s.SameCycle root i) (hσ : ∀ x y, H.Adj x y ↔ σ x = y)
    (hPos : 0 < k*m) (hQ : 110 < 10*b) (hScale : 24 ≤ scale)
    (hRoom : 3*(130*scale) ≤ m) (hSize : ∀ j, (Q j).card = m)
    (hCell : ∀ j v, v ∈ Q j → rank v = j.1 ∧ quarter v = j.2)
    (hBank : ∀ j p q, p ≠ q → ∀ x, M j p x ≠ M j q x)
    (hLo : (b*10)*(12*scale) ≤ 4*(k*m)) (hHi : 4*(k*m) ≤ (b*10)*(12*(scale+1)))
    (hFibre : ∀ x, (finiteSatisfying (fun j => parent j = x)).card = ell)
    (hCluster : ∀ x, (finiteSatisfying (fun v => parent (rank v) = x)).card =
      (finiteSatisfying (fun v => parent (rank v) = s x)).card)
    (hBlock : ∀ j x,
      (∑ e, if owner e = j ∧ parent e = x then (1:ℕ) else 0) + (if j = x then 1 else 0) =
      (∑ e, if owner e = j ∧ parent (finRotate (n+2) e) = s x then (1:ℕ) else 0) +
        (if j = s x then 1 else 0))
    (hCap : 3*cap ≤ scale)
    (hCE : ∀ i, C i ≤ E) (hEO : ∀ x y, E.Adj x y → ∃! i, (C i).Adj x y)
    (hC : ∀ i, IsDirectedPathSystem (C i) ∧ CoversExceptional (C i) Z)
    (hNo : ∀ i x y, (C i).Adj x y → x ∈ Z → y ∉ Z) :
    let basic (i : Fin (b*10)) := basicExceptionalPathSystem (C i) Z
    let c := parent ∘ rank
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
    let U := successorCellMatchingUnion Q ((finRotate (n+2)).prodCongr (Equiv.refl (Fin 4))) M
    Disjoint U H → Disjoint (liftDirectedPair e e (U ⊔ H)) E →
    (∀ i, Disjoint (finiteSatisfying (IncidentTo (P.matching i))) (finiteSatisfying (IncidentTo (basic i)))) →
    (∀ i j, residueCyclicClose 10 i j →
      Disjoint (finiteSatisfying (IncidentTo (P.matching i ⊔ basic i)))
        (finiteSatisfying (IncidentTo (P.matching j ⊔ basic j)))) →
    (∀ i x, (finiteSatisfying (fun v => c v = x ∧ IncidentTo (basic i) v)).card ≤ cap) →
    (∀ i x, (∑ a : Arc (basic i), if c a.val.1 = x then (1:ℕ) else 0) =
      ∑ a : Arc (basic i), if c a.val.2 = s x then (1:ℕ) else 0) →
    Nonempty (PreparedChordSystems (liftDirectedPair e e (U ⊔ H) ⊔ E) Z c s
      (scale+2*(ell*(13*scale))) (Fin (b*10))) := by
  intro basic c e U hUH hDis hCApart hSep hTouch hBalance
  let slot : Fin b × Fin 10 ≃ Fin (b*10) := finProdFinEquiv
  obtain ⟨D,hPart,hLe,hAway,hReady⟩ := prepare_basic_chord_round rank quarter parent s root σ H
    kind P basic owner Q M hCycle hσ hPos hQ hScale hRoom hSize hCell hBank hLo hHi hFibre
    hCluster hBlock hCap (fun i => basicExceptionalPathSystem.isDirectedPathSystem (hC i).1)
    hCApart hSep hTouch hBalance
  let walk (i : Fin (b*10)) := D (slot.symm i)
  have hWalkOwn (x y : ↥Zᶜ) (he : U.Adj x y) : ∃! i, (walk i).Adj x y := by
    obtain ⟨j,hj,hUnique⟩ := (hPart x y).mp he
    refine ⟨slot j,by simpa only [walk,slot.symm_apply_apply] using hj,?_⟩
    intro i hi
    have he' := hUnique (slot.symm i) hi
    exact (slot.apply_symm_apply i).symm.trans (congrArg slot he')
  exact exists_prepared_chord_systems Z H U E P.matching walk C c s _ (fun i => hLe (slot.symm i))
    P.matching_le hCE hWalkOwn (fun x y h => (P.partition x y).mp h) hEO hUH P.pathSystem
    hC hNo (fun i x h => by simpa only [slot,Equiv.apply_symm_apply,basic] using hAway (slot.symm i) x h)
    (fun i v hv hc => disjoint_left.mp (hCApart i) (mem_finiteSatisfying.mpr hv) (mem_finiteSatisfying.mpr hc))
    (fun i => by simpa only [slot,Equiv.apply_symm_apply,basic] using hReady (slot.symm i)) hDis

end OverfullWork.DirectedRobustExpansion
