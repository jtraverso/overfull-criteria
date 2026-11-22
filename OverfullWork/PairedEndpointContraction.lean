module

public import OverfullWork.LooplessEndpointContraction

@[expose] public section


/-! The actual simultaneous contraction of prescribed disjoint endpoint
pairs. Outgoing representatives follow a supplied endpoint permutation;
incoming representatives are the prescribed terminal vertices. -/
namespace OverfullWork.DirectedEndpointContraction
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 18000000

noncomputable def pairedSet {p : ℕ} (a b : Fin p → V) : Finset V := univ.image a ∪ univ.image b

abbrev Outside (E : Finset V) := {v : V // v ∉ E}

def replacementEmbedding {p : ℕ} (E : Finset V) (e : Fin p ↪ V)
    (hE : ∀ i,e i ∈ E) : (Outside E ⊕ Fin p) ↪ V where
  toFun x := match x with | .inl v => v.val | .inr i => e i
  inj' := by
    intro x y hh
    cases x with
    | inl v =>
      cases y with
      | inl w => exact congrArg Sum.inl (Subtype.ext hh)
      | inr i =>
        change v.val=e i at hh
        exact False.elim (v.property (by rw [hh];exact hE i))
    | inr i =>
      cases y with
      | inl w =>
        change e i=w.val at hh
        exact False.elim (w.property (by rw [←hh];exact hE i))
      | inr j => exact congrArg Sum.inr (e.injective hh)

theorem pairedSet_card {p : ℕ} (a b : Fin p → V)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j,a i ≠ b j) :
    (pairedSet a b).card=2*p := by
  have hDis : Disjoint (univ.image a) (univ.image b) := by
    apply disjoint_left.mpr
    intro v hv hw
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    obtain ⟨j,_,hh⟩ := mem_image.mp hw
    exact hab i j hh.symm
  unfold pairedSet
  rw [card_union_of_disjoint hDis,card_image_of_injective _ ha,card_image_of_injective _ hb]
  simp only [card_univ,Fintype.card_fin]
  omega

theorem outside_card (E : Finset V) : Fintype.card (Outside E)=Fintype.card V-E.card := by
  simpa only [Fintype.card_coe] using Fintype.card_subtype_compl (fun v : V => v ∈ E)

theorem paired_carrier_card {p : ℕ} (a b : Fin p → V)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j,a i ≠ b j) :
    Fintype.card (Outside (pairedSet a b) ⊕ Fin p)+p=Fintype.card V := by
  rw [Fintype.card_sum,outside_card,pairedSet_card a b ha hb hab,Fintype.card_fin]
  have hBound : 2*p ≤ Fintype.card V := by
    have hh := card_le_univ (pairedSet a b)
    rw [pairedSet_card a b ha hb hab] at hh
    exact hh
  omega

noncomputable def outgoingRepresentative {p : ℕ} (a b : Fin p → V) (ha : Function.Injective a)
    (next : Fin p ≃ Fin p) : (Outside (pairedSet a b) ⊕ Fin p) ↪ V :=
  replacementEmbedding (pairedSet a b) (next.toEmbedding.trans ⟨a,ha⟩)
    (fun i => mem_union_left _ (mem_image.mpr ⟨next i,mem_univ _,rfl⟩))

noncomputable def incomingRepresentative {p : ℕ} (a b : Fin p → V) (hb : Function.Injective b) :
    (Outside (pairedSet a b) ⊕ Fin p) ↪ V :=
  replacementEmbedding (pairedSet a b) ⟨b,hb⟩
    (fun i => mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))

noncomputable def pairedContraction {p : ℕ} (D : Digraph V) (a b : Fin p → V)
    (ha : Function.Injective a) (hb : Function.Injective b) (next : Fin p ≃ Fin p) :
    Digraph (Outside (pairedSet a b) ⊕ Fin p) :=
  looplessContracted D (outgoingRepresentative a b ha next) (incomingRepresentative a b hb)

theorem fourth_power_contraction_budgets (n p : ℕ) (ν : ℝ)
    (hν : 0 < ν) (hνHalf : ν ≤ 1/2) (hLarge : 16 ≤ ν*(n:ℝ))
    (hP : (p:ℝ) ≤ ν^4*(n:ℝ)) :
    (p:ℝ) ≤ (n:ℝ)/4 ∧ (p:ℝ)+1 ≤ ν*(n:ℝ)/4 := by
  have hν2 : ν^2 ≤ 1/4 := by nlinarith only [hν,hνHalf]
  have hν3 : ν^3 ≤ 1/8 := by
    have hh := mul_le_mul_of_nonneg_left hν2 hν.le
    nlinarith only [hh,hνHalf]
  have hν4 : ν^4 ≤ ν/8 := by
    have hh := mul_le_mul_of_nonneg_left hν3 hν.le
    nlinarith only [hh]
  have hN := mul_le_mul_of_nonneg_right hν4 (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hHalfN := mul_le_mul_of_nonneg_right hνHalf (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  constructor <;> nlinarith only [hP,hN,hHalfN,hLarge]

theorem paired_contraction_robust {p : ℕ} (D : Digraph V) (a b : Fin p → V)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j,a i ≠ b j)
    (next : Fin p ≃ Fin p) (ν τ : ℝ) (hν : 0 < ν) (hνHalf : ν ≤ 1/2) (hτ : 0 < τ)
    (hLarge : 16 ≤ ν*(Fintype.card V:ℝ)) (hOrder : 2 ≤ τ*(Fintype.card V:ℝ))
    (hP : (p:ℝ) ≤ ν^4*(Fintype.card V:ℝ)) (hRobust : IsRealRobust D ν τ) :
    IsRealRobust (pairedContraction D a b ha hb next) (ν/2) (2*τ) := by
  have hCard := paired_carrier_card a b ha hb hab
  have hDeficit : Fintype.card V-Fintype.card (Outside (pairedSet a b) ⊕ Fin p)=p := by omega
  obtain ⟨hSmall,hLoss⟩ := fourth_power_contraction_budgets (Fintype.card V) p ν hν hνHalf hLarge hP
  have hScale : 4 ≤ ν*(Fintype.card (Outside (pairedSet a b) ⊕ Fin p):ℝ) := by
    have hCast : (Fintype.card (Outside (pairedSet a b) ⊕ Fin p):ℝ)+(p:ℝ)=(Fintype.card V:ℝ) := by exact_mod_cast hCard
    have hScaled := mul_le_mul_of_nonneg_left hSmall hν.le
    have hEq := congrArg (fun x : ℝ => ν*x) hCast
    nlinarith only [hScaled,hEq,hLarge]
  apply robust_loopless_contracted D (outgoingRepresentative a b ha next) (incomingRepresentative a b hb)
    ν τ hν hτ hRobust hScale hOrder
  · simpa only [hDeficit] using hSmall
  · simpa only [hDeficit] using hLoss


theorem paired_contraction_semidegrees {p : ℕ} (D : Digraph V) (a b : Fin p → V)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j,a i ≠ b j)
    (next : Fin p ≃ Fin p) (ν α : ℝ) (hν : 0 < ν) (hνHalf : ν ≤ 1/2)
    (hνα : ν ≤ α) (hLarge : 16 ≤ ν*(Fintype.card V:ℝ))
    (hP : (p:ℝ) ≤ ν^4*(Fintype.card V:ℝ))
    (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) :
    (∀ w,(α/2)*(Fintype.card (Outside (pairedSet a b) ⊕ Fin p):ℝ) ≤
      (inDegree (pairedContraction D a b ha hb next) w:ℝ)) ∧
    (∀ w,(α/2)*(Fintype.card (Outside (pairedSet a b) ⊕ Fin p):ℝ) ≤
      (outDegree (pairedContraction D a b ha hb next) w:ℝ)) := by
  have hCard := paired_carrier_card a b ha hb hab
  have hDeficit : Fintype.card V-Fintype.card (Outside (pairedSet a b) ⊕ Fin p)=p := by omega
  obtain ⟨_,hLoss⟩ := fourth_power_contraction_budgets (Fintype.card V) p ν hν hνHalf hLarge hP
  apply semidegrees_loopless_contracted D (outgoingRepresentative a b ha next)
    (incomingRepresentative a b hb) α (le_trans hν.le hνα) hIn hOut
  rw [hDeficit]
  have hh := mul_le_mul_of_nonneg_right hνα (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  linarith

end OverfullWork.DirectedEndpointContraction
