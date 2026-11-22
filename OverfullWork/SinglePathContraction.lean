module

public import OverfullWork.PairedEndpointContraction

@[expose] public section


/-! Contract a nonempty actual vertex set to one directed vertex whose
incoming representative is the path start and outgoing representative
is the path end. This is the contraction in KLO Corollary 6.8. -/
namespace OverfullWork.DirectedEndpointContraction
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 12000000

def pointRepresentative (E : Finset V) (v : V) (hv : v∈E) :
    (Outside E ⊕ Fin 1) ↪ V :=
  replacementEmbedding E ⟨fun _ => v,fun _ _ _ => Subsingleton.elim _ _⟩ (fun _ => hv)

def singleContraction (D : Digraph V) (E : Finset V) (x y : V) (hx : x∈E) (hy : y∈E) :
    Digraph (Outside E ⊕ Fin 1) :=
  looplessContracted D (pointRepresentative E y hy) (pointRepresentative E x hx)

theorem single_carrier_order (E : Finset V) (hE : E.Nonempty) :
    Fintype.card (Outside E ⊕ Fin 1)+(E.card-1)=Fintype.card V := by
  rw [Fintype.card_sum,outside_card,Fintype.card_fin]
  have hCard := card_le_univ E
  have hPos := card_pos.mpr hE
  omega

theorem single_contraction_robust (D : Digraph V) (E : Finset V) (x y : V)
    (hx : x∈E) (hy : y∈E) (ν τ : ℝ) (hν : 0 < ν) (hνOne : ν ≤ 1) (hτ : 0 < τ)
    (hLarge : 16 ≤ ν*(Fintype.card V:ℝ)) (hOrder : 2 ≤ τ*(Fintype.card V:ℝ))
    (hSmall : (E.card:ℝ) ≤ ν*(Fintype.card V:ℝ)/4)
    (hRobust : IsRealRobust D ν τ) :
    IsRealRobust (singleContraction D E x y hx hy) (ν/2) (2*τ) := by
  have hE : E.Nonempty := ⟨x,hx⟩
  have hCard := single_carrier_order E hE
  have hDeficit : Fintype.card V-Fintype.card (Outside E ⊕ Fin 1)=E.card-1 := by omega
  have hPos := card_pos.mpr hE
  have hLoss : (((Fintype.card V-Fintype.card (Outside E ⊕ Fin 1):ℕ):ℝ)+1)=(E.card:ℝ) := by
    have hh : Fintype.card V-Fintype.card (Outside E ⊕ Fin 1)+1=E.card := by omega
    exact_mod_cast hh
  have hN := mul_le_mul_of_nonneg_right hνOne
    (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ Fintype.card V)
  have hQuarter : (E.card:ℝ) ≤ (Fintype.card V:ℝ)/4 := by linarith
  have hCast : (Fintype.card (Outside E ⊕ Fin 1):ℝ)+(E.card:ℝ)-1=(Fintype.card V:ℝ) := by
    have hh : Fintype.card (Outside E ⊕ Fin 1)+E.card=Fintype.card V+1 := by omega
    have hr : (Fintype.card (Outside E ⊕ Fin 1):ℝ)+(E.card:ℝ)=(Fintype.card V:ℝ)+1 := by exact_mod_cast hh
    linarith only [hr]
  have hScale : 4 ≤ ν*(Fintype.card (Outside E ⊕ Fin 1):ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hQuarter hν.le
    have he := congrArg (fun t : ℝ => ν*t) hCast
    nlinarith only [hh,he,hLarge,hν]
  apply robust_loopless_contracted D (pointRepresentative E y hy) (pointRepresentative E x hx)
    ν τ hν hτ hRobust hScale hOrder
  · have hh : ((Fintype.card V-Fintype.card (Outside E ⊕ Fin 1):ℕ):ℝ) ≤ (E.card:ℝ) := by linarith
    exact hh.trans hQuarter
  · rw [hLoss]
    exact hSmall

theorem single_contraction_semidegrees (D : Digraph V) (E : Finset V) (x y : V)
    (hx : x∈E) (hy : y∈E) (α : ℝ) (hα : 0 ≤ α)
    (hSmall : (E.card:ℝ) ≤ α*(Fintype.card V:ℝ)/2)
    (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) :
    (∀ w,(α/2)*(Fintype.card (Outside E ⊕ Fin 1):ℝ) ≤
      (inDegree (singleContraction D E x y hx hy) w:ℝ)) ∧
    (∀ w,(α/2)*(Fintype.card (Outside E ⊕ Fin 1):ℝ) ≤
      (outDegree (singleContraction D E x y hx hy) w:ℝ)) := by
  have hCard := single_carrier_order E ⟨x,hx⟩
  have hPos := card_pos.mpr (show E.Nonempty from ⟨x,hx⟩)
  have hLoss : Fintype.card V-Fintype.card (Outside E ⊕ Fin 1)+1=E.card := by omega
  apply semidegrees_loopless_contracted D (pointRepresentative E y hy)
    (pointRepresentative E x hx) α hα hIn hOut
  have hh : (((Fintype.card V-Fintype.card (Outside E ⊕ Fin 1):ℕ):ℝ)+1)=(E.card:ℝ) := by exact_mod_cast hLoss
  rw [hh]
  exact hSmall

end OverfullWork.DirectedEndpointContraction
