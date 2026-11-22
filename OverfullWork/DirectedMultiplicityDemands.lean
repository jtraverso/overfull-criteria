module

public import OverfullWork.DirectedDemandHall
public import OverfullWork.RealDirectedRobustExpansion

@[expose] public section


/-! Prescribed directed degrees with multiplicities, as used in
Osthus–Staden Lemma 4.1. Integer hypotheses make the cut bounds explicit. -/
namespace OverfullWork.DirectedMultigraphFactors
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]

private abbrev Copies (M : V → V → ℕ) := Σ a : V × V, Fin (M a.1 a.2)

omit [Fintype V] in
private theorem copies_over (M : V → V → ℕ) (A : Finset (V × V)) :
    (A.sigma (fun a => (univ : Finset (Fin (M a.1 a.2))))).card =
      ∑ a ∈ A, M a.1 a.2 := by
  rw [card_sigma]
  simp

/-- Integer arc capacities admit a submatrix realizing the degrees
whenever all capacity cuts hold. -/
theorem exists_matrix_of_capacity_cuts (M : V → V → ℕ) (p q : V → ℕ)
    (hBalance : (∑ v,p v) = ∑ v,q v)
    (hCuts : ∀ S T : Finset V, (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v) +
      ∑ v ∈ S,∑ w ∈ Tᶜ,M v w) :
    ∃ H : V → V → ℕ, (∀ v w, H v w ≤ M v w) ∧
      (∀ v, (∑ w,H v w) = p v) ∧ (∀ w, (∑ v,H v w) = q w) := by
  let src := fun a : Copies M => a.1.1
  let dst := fun a : Copies M => a.1.2
  have hCut (S T : Finset V) : ((univ : Finset (Copies M)).filter
      (fun a => src a ∈ S ∧ dst a ∉ T)).card = ∑ v ∈ S,∑ w ∈ Tᶜ,M v w := by
    have he : (univ : Finset (Copies M)).filter (fun a => src a ∈ S ∧ dst a ∉ T) =
        (S ×ˢ Tᶜ).sigma (fun a => (univ : Finset (Fin (M a.1 a.2)))) := by
      ext a
      simp [src,dst]
    rw [he,copies_over,sum_product]
  obtain ⟨C,hSrc,hDst⟩ := DirectedDemandHall.exists_labeled_arcs_of_capacity_cuts src dst p q
    hBalance (fun S T => by rw [hCut]; exact hCuts S T)
  let H := fun v w => (C.filter (fun a => src a = v ∧ dst a = w)).card
  refine ⟨H,?_,?_,?_⟩
  · intro v w
    have h : C.filter (fun a => src a = v ∧ dst a = w) ⊆
        (univ : Finset (Copies M)).filter (fun a => a.1 = (v,w)) := by
      intro a ha
      have hp := (mem_filter.mp ha).2
      exact mem_filter.mpr ⟨mem_univ _,Prod.ext hp.1 hp.2⟩
    refine (card_le_card h).trans_eq ?_
    have he : (univ : Finset (Copies M)).filter (fun a => a.1 = (v,w)) =
        ({(v,w)} : Finset (V × V)).sigma (fun a => (univ : Finset (Fin (M a.1 a.2)))) := by
      ext a
      simp
    rw [he,copies_over,sum_singleton]
  · intro v
    have h := sum_card_fiberwise_eq_card_filter (C.filter (fun a => src a = v)) univ dst
    simpa only [H,filter_filter,mem_univ,filter_true,and_true,hSrc] using h
  · intro w
    have h := sum_card_fiberwise_eq_card_filter (C.filter (fun a => dst a = w)) univ src
    simpa only [H,filter_filter,and_comm,mem_univ,filter_true,true_and,and_true,hDst] using h

/-- The support of a multiplicity matrix can supply all balanced nearly
constant demands under the robust cut bounds. -/
theorem exists_matrix_of_robust_demands (M : V → V → ℕ) (D : Digraph V)
    (r t L U c : ℕ) (p q : V → ℕ) (hCap : ∀ v w, D.Adj v w → c ≤ M v w)
    (hR : IsRobustAt D r t) (hLU : L ≤ U) (hTwo : U ≤ 2*L)
    (hGap : 2*(U-L)*Fintype.card V ≤ L*r)
    (hSquare : 2*U*Fintype.card V ≤ c*r*r)
    (hIn : ∀ v, c*t+U ≤ c*inDegree D v) (hOut : ∀ v, 2*c*t+U ≤ c*outDegree D v)
    (hp : ∀ v, L ≤ p v ∧ p v ≤ U) (hq : ∀ v, L ≤ q v ∧ q v ≤ U)
    (hBalance : (∑ v,p v) = ∑ v,q v) :
    ∃ H : V → V → ℕ, (∀ v w, H v w ≤ M v w) ∧
      (∀ v, (∑ w,H v w) = p v) ∧ (∀ w, (∑ v,H v w) = q w) := by
  apply exists_matrix_of_capacity_cuts M p q hBalance
  intro S T
  apply (scaled_degree_demand_cut_bound D r t L U c p q hR hLU hTwo hGap hSquare
    hIn hOut hp hq hBalance S T).trans
  apply Nat.add_le_add_left
  rw [sum_comm,incidences,mul_sum]
  apply sum_le_sum
  intro w _
  simp only [inNeighbours,card_filter,mul_sum]
  apply sum_le_sum
  intro v _
  by_cases h : D.Adj v w
  · simpa [h] using hCap v w h
  · simp [h]

/-- Normalized multiplicity version of Osthus–Staden Lemma 4.1
with explicit hierarchy and rounding margins. -/
theorem osthus_staden_lemma_4_1 (M : V → V → ℕ) (D : Digraph V) (c : ℕ)
    (ν τ α ε ρ : ℝ) (p q : V → ℕ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hντ : ν ≤ τ) (hτα : 4*τ ≤ α) (hε : 0 ≤ ε) (hεν : 16*ε ≤ ν)
    (hρ : 0 ≤ ρ) (hρν : 3*ρ ≤ (c:ℝ)*ν^2)
    (hOrder : 8 ≤ α*(Fintype.card V:ℝ))
    (hCap : ∀ v w, D.Adj v w → c ≤ M v w)
    (hR : IsRealRobust D ν τ)
    (hIn : ∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (hp : ∀ v, (1-ε)*ρ*(Fintype.card V:ℝ) ≤ (p v:ℝ) ∧
      (p v:ℝ) ≤ (1+ε)*ρ*(Fintype.card V:ℝ))
    (hq : ∀ v, (1-ε)*ρ*(Fintype.card V:ℝ) ≤ (q v:ℝ) ∧
      (q v:ℝ) ≤ (1+ε)*ρ*(Fintype.card V:ℝ))
    (hBalance : (∑ v,p v) = ∑ v,q v) :
    ∃ H : V → V → ℕ, (∀ v w, H v w ≤ M v w) ∧
      (∀ v, (∑ w,H v w) = p v) ∧ (∀ w, (∑ v,H v w) = q w) := by
  let n := Fintype.card V
  let L := ⌈(1-ε)*ρ*(n:ℝ)⌉₊
  let U := ⌊(1+ε)*ρ*(n:ℝ)⌋₊
  let r := ⌈ν*(n:ℝ)⌉₊
  let t := ⌈τ*(n:ℝ)⌉₊
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ (c:ℝ) := Nat.cast_nonneg _
  have he : ε ≤ 1/16 := by linarith only [hεν,hν1]
  have hτ : 0 ≤ τ := hν.le.trans hντ
  have hp' (v : V) : L ≤ p v ∧ p v ≤ U := ⟨Nat.ceil_le.mpr (hp v).1,Nat.le_floor (hp v).2⟩
  have hq' (v : V) : L ≤ q v ∧ q v ≤ U := ⟨Nat.ceil_le.mpr (hq v).1,Nat.le_floor (hq v).2⟩
  have hLU : L ≤ U := by
    have hne : Nonempty V := by
      apply Fintype.card_pos_iff.mp
      by_contra! h
      have hz : (Fintype.card V:ℝ) = 0 := by exact_mod_cast (Nat.eq_zero_of_le_zero h)
      rw [hz,mul_zero] at hOrder
      norm_num at hOrder
    exact (hp' (Classical.choice hne)).1.trans (hp' (Classical.choice hne)).2
  have hL : (1-ε)*ρ*(n:ℝ) ≤ (L:ℝ) := Nat.le_ceil _
  have hU : (U:ℝ) ≤ (1+ε)*ρ*(n:ℝ) := Nat.floor_le (by positivity)
  have hr : ν*(n:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
  have ht : (t:ℝ) ≤ τ*(n:ℝ)+1 := (Nat.ceil_lt_add_one (mul_nonneg hτ hn)).le
  have hBase : 0 ≤ ρ*(n:ℝ) := mul_nonneg hρ hn
  have hHalf : ρ*(n:ℝ)/2 ≤ (L:ℝ) := by
    nlinarith only [hL,mul_le_mul_of_nonneg_right he hBase,hBase]
  have hTwo : U ≤ 2*L := by
    exact_mod_cast (show (U:ℝ) ≤ 2*(L:ℝ) by
      nlinarith only [hU,hL,mul_le_mul_of_nonneg_right he hBase,hBase])
  have hGap : 2*(U-L)*n ≤ L*r := by
    have hDiff : ((U-L:ℕ):ℝ) ≤ 2*ε*ρ*(n:ℝ) := by
      rw [Nat.cast_sub hLU]
      linarith only [hL,hU]
    have h1 := mul_le_mul_of_nonneg_right hDiff hn
    have h2 := mul_le_mul_of_nonneg_right hεν (mul_nonneg hBase hn)
    have h3 := mul_le_mul hHalf hr (mul_nonneg hν.le hn) (Nat.cast_nonneg L)
    exact_mod_cast (show 2*((U-L:ℕ):ℝ)*(n:ℝ) ≤ (L:ℝ)*(r:ℝ) by
      nlinarith only [h1,h2,h3,mul_nonneg (mul_nonneg hν.le hBase) hn])
  have hSquare : 2*U*n ≤ c*r*r := by
    have hUpper := mul_le_mul_of_nonneg_right hU hn
    have hErr := mul_le_mul_of_nonneg_right he (mul_nonneg hBase hn)
    have hCapSq := mul_le_mul_of_nonneg_right hρν (mul_nonneg hn hn)
    have hSq := mul_le_mul_of_nonneg_left
      (mul_le_mul hr hr (mul_nonneg hν.le hn) (Nat.cast_nonneg r)) hc
    exact_mod_cast (show 2*(U:ℝ)*(n:ℝ) ≤ (c:ℝ)*(r:ℝ)*(r:ℝ) by
      nlinarith only [hUpper,hErr,hCapSq,hSq,mul_nonneg hBase hn])
  have hMin {d : ℕ} (hd : α*(n:ℝ) ≤ d) : 2*c*t+U ≤ c*d := by
    have hνsq : ν^2 ≤ ν := by nlinarith only [mul_le_mul_of_nonneg_left hν1 hν.le]
    have h1 := mul_le_mul_of_nonneg_right hρν hn
    have h2 := mul_le_mul_of_nonneg_right (hνsq.trans hντ) (mul_nonneg hc hn)
    have h3 := mul_le_mul_of_nonneg_right hτα (mul_nonneg hc hn)
    have h4 := mul_le_mul_of_nonneg_left ht hc
    have h5 := mul_le_mul_of_nonneg_left hd hc
    have h6 := mul_le_mul_of_nonneg_left hOrder hc
    have h7 := mul_le_mul_of_nonneg_right he hBase
    exact_mod_cast (show 2*(c:ℝ)*(t:ℝ)+(U:ℝ) ≤ (c:ℝ)*(d:ℝ) by
      nlinarith only [h1,h2,h3,h4,h5,h6,h7,hU,hBase,hc])
  apply exists_matrix_of_robust_demands M D r t L U c p q hCap
    (integer_of_real D ν τ hν.le hR) hLU hTwo hGap hSquare
    (fun v => le_trans (show c*t+U ≤ 2*c*t+U by
      rw [Nat.mul_assoc]
      omega) (hMin (hIn v)))
    (fun v => hMin (hOut v)) hp' hq' hBalance

end OverfullWork.DirectedMultigraphFactors
