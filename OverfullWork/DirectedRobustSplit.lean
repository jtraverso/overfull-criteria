module

public import OverfullWork.DirectedBiasedSplit
public import OverfullWork.DirectedFractionalTransport

@[expose] public section


/-! An actual robust directed partition at an arbitrary fraction p.
This is the integer-threshold counterpart of Gao--Shan Lemma 2.9
(arXiv:2405.18494v2, citing Kühn--Osthus Lemma 3.2).
Both parts have controlled semidegrees and positive robust thresholds.
No sampling robustness or spanning-layout realization is assumed. -/
namespace OverfullWork.DirectedRobustSplit
open Finset DirectedRobustExpansion DirectedArcSelection
open scoped Classical
universe u
set_option maxHeartbeats 24000000

theorem exists_uniform_split (p ρ ε : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (D : Digraph V) (r t : ℕ),N ≤ Fintype.card V → IsRobustAt D r t →
      ρ*(Fintype.card V:ℝ) ≤ (r:ℝ) →
      ∃ H : Digraph V,H ≤ D ∧
        (∀ v,|(inDegree H v:ℝ)-p*(inDegree D v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        (∀ v,|(outDegree H v:ℝ)-p*(outDegree D v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        (∀ v,|(inDegree (D\H) v:ℝ)-(1-p)*(inDegree D v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        (∀ v,|(outDegree (D\H) v:ℝ)-(1-p)*(outDegree D v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        0 < ⌈p*(r:ℝ)/2⌉₊ ∧ IsRobustAt H ⌈p*(r:ℝ)/2⌉₊ t ∧
        0 < ⌈(1-p)*(r:ℝ)/2⌉₊ ∧ IsRobustAt (D\H) ⌈(1-p)*(r:ℝ)/2⌉₊ t := by
  let m := min p (1-p)
  have hm : 0 < m := lt_min hp (by linarith only [hp1])
  let δ := min ε (m*ρ^2/16)
  have hδ : 0 < δ := by dsimp only [δ];positivity
  obtain ⟨N₀,hSelect⟩ := DirectedBiasedSplit.exists_selection.{u} p δ hp.le hp1.le hδ
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (8/(m*ρ))
  refine ⟨max N₀ N₁,?_⟩
  intro V _ _ D r t hn hRobust hR
  let n := Fintype.card V
  obtain ⟨H,hLe,hIn,hOut,hCuts⟩ := hSelect D (by omega)
  have hδle : δ ≤ ε := min_le_left _ _
  have hδm : 16*δ ≤ m*ρ^2 := by
    have hh := min_le_right ε (m*ρ^2/16)
    change δ ≤ m*ρ^2/16 at hh
    linarith only [hh]
  have hN₁n : (N₁:ℝ) ≤ n := by exact_mod_cast (show N₁ ≤ n by omega)
  have hEight : (8:ℝ) < (m*ρ)*(n:ℝ) := by
    have hh := (div_lt_iff₀ (mul_pos hm hρ)).mp (hN₁.trans_le hN₁n)
    nlinarith only [hh]
  have hLarge : (8:ℝ) < m*(r:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hR hm.le
    nlinarith only [hh,hEight]
  have hmP : m ≤ p := min_le_left _ _
  have hmQ : m ≤ 1-p := min_le_right _ _
  have hTwoP : (8:ℝ) ≤ p*(r:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hmP (Nat.cast_nonneg r : (0:ℝ) ≤ r)
    linarith only [hh,hLarge]
  have hTwoQ : (8:ℝ) ≤ (1-p)*(r:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hmQ (Nat.cast_nonneg r : (0:ℝ) ≤ r)
    linarith only [hh,hLarge]
  have hErrorBase : 8*(δ*(n:ℝ)^2) ≤ m*(r:ℝ)^2 := by
    have hδn := mul_le_mul_of_nonneg_right hδm (sq_nonneg (n:ℝ))
    have hR2 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ρ*(n:ℝ)) hR 2
    have hScale := mul_le_mul_of_nonneg_left hR2 hm.le
    have hNonneg : (0:ℝ) ≤ δ*(n:ℝ)^2 := by positivity
    nlinarith only [hδn,hScale,hNonneg]
  have hErrorP : 8*(δ*(n:ℝ)^2) ≤ p*(r:ℝ)^2 :=
    hErrorBase.trans (mul_le_mul_of_nonneg_right hmP (sq_nonneg (r:ℝ)))
  have hErrorQ : 8*(δ*(n:ℝ)^2) ≤ (1-p)*(r:ℝ)^2 :=
    hErrorBase.trans (mul_le_mul_of_nonneg_right hmQ (sq_nonneg (r:ℝ)))
  have hLower : ∀ S T : Finset V,p*(incidences D S T:ℝ) ≤
      (incidences H S T:ℝ)+δ*(n:ℝ)^2 := by
    intro S T
    have hh := (abs_lt.mp (hCuts S T)).1
    linarith only [hh]
  have hOtherCuts : ∀ S T : Finset V,
      |(incidences (D\H) S T:ℝ)-(1-p)*(incidences D S T:ℝ)| < δ*(n:ℝ)^2 := by
    intro S T
    rw [complementary_cut_error D H hLe p,abs_neg]
    exact hCuts S T
  have hOtherLower : ∀ S T : Finset V,(1-p)*(incidences D S T:ℝ) ≤
      (incidences (D\H) S T:ℝ)+δ*(n:ℝ)^2 := by
    intro S T
    have hh := (abs_lt.mp (hOtherCuts S T)).1
    linarith only [hh]
  obtain ⟨hPos,hH⟩ := DirectedFractionalTransport.robust_ceil_fraction_of_cut_error D H p r t
    (δ*(n:ℝ)^2) hRobust hp hp1.le hTwoP hErrorP hLower
  obtain ⟨hOtherPos,hOther⟩ := DirectedFractionalTransport.robust_ceil_fraction_of_cut_error D (D\H) (1-p) r t
    (δ*(n:ℝ)^2) hRobust (by linarith only [hp1]) (by linarith only [hp]) hTwoQ hErrorQ hOtherLower
  have hTolerance := mul_le_mul_of_nonneg_right hδle (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  refine ⟨H,hLe,(fun v => (hIn v).trans_le hTolerance),
    (fun v => (hOut v).trans_le hTolerance),?_,?_,hPos,hH,hOtherPos,hOther⟩
  · intro v
    have hh := complementary_cut_error D H hLe p univ {v}
    rw [incidences_degree,incidences_degree,incidences_degree] at hh
    rw [hh,abs_neg]
    exact (hIn v).trans_le hTolerance
  · intro v
    have hh := complementary_cut_error D H hLe p {v} univ
    rw [incidences_outDegree,incidences_outDegree,incidences_outDegree] at hh
    rw [hh,abs_neg]
    exact (hOut v).trans_le hTolerance

theorem exists_relative_split (p ρ α η : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hρ : 0 < ρ) (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (D : Digraph V) (r t : ℕ),N ≤ Fintype.card V → IsRobustAt D r t →
      ρ*(Fintype.card V:ℝ) ≤ (r:ℝ) →
      (∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      ∃ H : Digraph V,H ≤ D ∧
        (∀ v,|(inDegree H v:ℝ)-p*(inDegree D v:ℝ)| < η*p*(inDegree D v:ℝ)) ∧
        (∀ v,|(outDegree H v:ℝ)-p*(outDegree D v:ℝ)| < η*p*(outDegree D v:ℝ)) ∧
        (∀ v,|(inDegree (D\H) v:ℝ)-(1-p)*(inDegree D v:ℝ)| < η*(1-p)*(inDegree D v:ℝ)) ∧
        (∀ v,|(outDegree (D\H) v:ℝ)-(1-p)*(outDegree D v:ℝ)| < η*(1-p)*(outDegree D v:ℝ)) ∧
        0 < ⌈p*(r:ℝ)/2⌉₊ ∧ IsRobustAt H ⌈p*(r:ℝ)/2⌉₊ t ∧
        0 < ⌈(1-p)*(r:ℝ)/2⌉₊ ∧ IsRobustAt (D\H) ⌈(1-p)*(r:ℝ)/2⌉₊ t := by
  let m := min p (1-p)
  have hm : 0 < m := lt_min hp (by linarith only [hp1])
  obtain ⟨N,hN⟩ := exists_uniform_split.{u} p ρ (η*m*α) hp hp1 hρ (by positivity)
  refine ⟨N,?_⟩
  intro V _ _ D r t hn hRobust hr hInD hOutD
  obtain ⟨H,hLe,hIn,hOut,hInOther,hOutOther,hPos,hH,hOtherPos,hOther⟩ := hN D r t hn hRobust hr
  have hTol : ∀ k d : ℝ,m ≤ k → α*(Fintype.card V:ℝ) ≤ d →
      (η*m*α)*(Fintype.card V:ℝ) ≤ η*k*d := by
    intro k d hmk hd
    have hd0 : 0 ≤ d := (mul_nonneg hα.le (Nat.cast_nonneg _)).trans hd
    calc
      _ = (η*m)*(α*(Fintype.card V:ℝ)) := by ring
      _ ≤ (η*m)*d := mul_le_mul_of_nonneg_left hd (mul_pos hη hm).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmk hη.le) hd0
  have hmP : m ≤ p := min_le_left _ _
  have hmQ : m ≤ 1-p := min_le_right _ _
  exact ⟨H,hLe,(fun v => (hIn v).trans_le (hTol p _ hmP (hInD v))),
    (fun v => (hOut v).trans_le (hTol p _ hmP (hOutD v))),
    (fun v => (hInOther v).trans_le (hTol (1-p) _ hmQ (hInD v))),
    (fun v => (hOutOther v).trans_le (hTol (1-p) _ hmQ (hOutD v))),
    hPos,hH,hOtherPos,hOther⟩

end OverfullWork.DirectedRobustSplit
