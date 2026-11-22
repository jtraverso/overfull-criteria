module

public import OverfullWork.TwoCentreHeavyFactorization

@[expose] public section


/-! Close the actual second-low terminal under explicit arithmetic reserves. -/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset TwoIndependentIdentifications Gate8J2I
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {B K : ℕ} {s : State V B K}
set_option maxHeartbeats 10000000

theorem second_low_excluded_of_reserves (p : SecondLowData s) (hM : Margins s)
    (C : ℕ) (hC : 4000 ≤ C)
    (hSize : 2*linearHalfBound C (6*B+1)+K+1 ≤ Fintype.card V)
    (hSlack : Fintype.card V+30*B+12 ≤ 2*s.graph.maxDegree)
    (hDense : (C+64)*Fintype.card V ≤ 2*C*(s.graph.maxDegree-6*B)) : False := by
  obtain ⟨part⟩ := p.exists_partition
  obtain ⟨J,_,hReg,hJ0,hNo,_,hPair,_⟩ := part.exists_star_completion_no_overfull hM
  let M := part.image.addCopies J
  let q := s.graph.maxDegree-M.mult s(Sum.inl false,Sum.inl true)
  have hq : q ≤ 3*B := by dsimp only [q,M];omega
  have hSimple : ∀ u v : Outside p.exceptional, M.mult s(Sum.inr u,Sum.inr v) ≤ 1 := by
    intro u v
    change part.image.mult s(Sum.inr u,Sum.inr v)+J.mult s(Sum.inr u,Sum.inr v) ≤ 1
    rw [hJ0,Nat.add_zero]
    exact mult_inr_le s.graph p.exceptional part.left part.subset p.independent u v
  have hCardOutside : Fintype.card (Outside p.exceptional)=p.exceptionalᶜ.card := by
    have hh := card_vertices p.exceptional
    rw [Fintype.card_sum,Fintype.card_bool] at hh
    omega
  obtain ⟨m,hm⟩ := p.even_complement
  have hCard : Fintype.card (Outside p.exceptional)=2*m := by omega
  have hParts := card_add_card_compl p.exceptional
  have hK := p.card_bound
  have hCoef : 1 ≤ (10:ℕ)^24*C^6 := by
    have hh : 1 ≤ C^6 := Nat.one_le_pow _ C (by omega)
    nlinarith only [hh]
  have hBase : 4 ≤ linearHalfBound C (6*B+1) := by
    unfold linearHalfBound
    have hPos : 1 ≤ C^6*(6*B+1) := by
      simpa using Nat.mul_le_mul (Nat.one_le_pow 6 C (by omega)) (show 1 ≤ 6*B+1 by omega)
    nlinarith only [hPos]
  have hm4 : 4 ≤ m := by omega
  have hSizeActual : linearHalfBound C (2*q+1) ≤ m := by
    have hMono := Nat.mul_le_mul_left ((10:ℕ)^24*C^6) (show 2*q+1 ≤ 6*B+1 by omega)
    change (10:ℕ)^24*C^6*(2*q+1) ≤ m
    change 2*((10:ℕ)^24*C^6*(6*B+1))+K+1 ≤ Fintype.card V at hSize
    omega
  have hSlackActual : 2*m+10*q+12 ≤ 2*s.graph.maxDegree := by omega
  have hDenseActual : (C+64)*m ≤ C*(s.graph.maxDegree-2*q) := by
    have hCount : 2*m ≤ Fintype.card V := by omega
    have hScaled := Nat.mul_le_mul_left (C+64) hCount
    have hSub := Nat.mul_le_mul_left C
      (show s.graph.maxDegree-6*B ≤ s.graph.maxDegree-2*q by omega)
    nlinarith only [hDense,hScaled,hSub]
  obtain ⟨F⟩ := TwoCentreHeavyFactorization.colourable M s.graph.maxDegree q C m hReg hNo
    hSimple hCard hm4 rfl hC hSizeActual hSlackActual hDenseActual
  exact s.uncolourable (part.source_colourable_of_completed J F)

end OverfullWork.NormalizedClassTwoStep
