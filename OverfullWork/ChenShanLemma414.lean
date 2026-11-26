module

public import OverfullWork.ChenShanMatchingPacking
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real Filter
open scoped Classical Topology

private theorem eventually_matching_packing_cost (b a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    ∀ᶠ n : ℝ in atTop, 9*b*n^2*exp (-(a*n)/8) < 1 := by
  have hLim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (a/8) (by positivity)
  have hSmall := hLim.eventually (gt_mem_nhds (show (0:ℝ) < 1/(9*b) by positivity))
  filter_upwards [hSmall] with n hn
  change n ^ (2:ℝ)*exp (-(a/8)*n) < 1/(9*b) at hn
  rw [show n ^ (2:ℝ) = n^2 by norm_cast] at hn
  have h := (lt_div_iff₀ (show 0 < 9*b by positivity)).mp hn
  rw [show -(a*n)/8 = -(a/8)*n by ring]
  linarith only [h,show 9*b*n^2*exp (-(a/8)*n) = n^2*exp (-(a/8)*n)*(9*b) by ring]

/-- Chen–Shan, Lemma 4.14, the bipartite case of Lemma 9.1 of
Barber–Kühn–Lo–Osthus–Taylor. Each matching is represented by the
two ordered representatives of each of its edges. The ambient
tripartition is only needed for its order bound and to specify the shores. -/
theorem exists_bklot_bipartite_matching_packing (b : ℕ) (hb : 0 < b) (density : ℝ)
    (hDensity : 0 < density) (_hDensityAtMostOne : density ≤ 1) :
    ∃ n₀ : ℕ, ∀ (n q : ℕ), n₀ ≤ n → q ≤ 3*b*n →
      ∀ (V : Type*) [Fintype V] (E : V → V → Prop) (X Y : ℕ → Finset V),
      Fintype.card V ≤ 3*n →
      (∀ i < q, (X i).card = (Y i).card) →
      (∀ i < q, Disjoint (X i) (Y i)) →
      (∀ i < q, ∀ a ∈ X i, ((Y i).card : ℝ)/2 + 81*b*density^(3/2:ℝ)*n ≤ ((Y i).filter (E a)).card) →
      (∀ i < q, ∀ a ∈ Y i, ((X i).card : ℝ)/2 + 81*b*density^(3/2:ℝ)*n ≤
        ((X i).filter (fun v => E v a)).card) →
      (∀ i < q, ∀ j < q, i ≠ j →
        (((X i ∪ Y i) ∩ (X j ∪ Y j)).card : ℝ) ≤ 6*density^2*n) →
      (∀ v, (((range q).filter (fun j => v ∈ X j ∪ Y j)).card : ℝ) ≤ 2*b*density*n) →
      ∃ M : ℕ → Finset (V × V),
        (∀ i < q, ∃ f : ↥(X i) ≃ ↥(Y i),
          M i = matchingArcs f ∧ ∀ a : X i, E a (f a)) ∧
        ∀ i < q, ∀ j < q, i ≠ j → Disjoint (M i) (M j) := by
  let a := density*sqrt density
  have ha : 0 < a := mul_pos hDensity (sqrt_pos.2 hDensity)
  have hbR : 0 < (b:ℝ) := by exact_mod_cast hb
  have hb₁ : 1 ≤ (b:ℝ) := by exact_mod_cast hb
  have hPow : density^(3/2:ℝ) = a := by
    rw [show (3/2:ℝ) = 1+1/2 by norm_num,rpow_add hDensity,rpow_one,← sqrt_eq_rpow]
  obtain ⟨z,hz⟩ := eventually_atTop.mp (eventually_matching_packing_cost (b:ℝ) a hbR ha)
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (max z (1/a))
  refine ⟨n₀,?_⟩
  intro n q hn hq V _ E X Y hV hSize hDis hL hR hOverlap hOccur
  let L := a*(n:ℝ)
  have hnR : (n₀:ℝ) ≤ n := by exact_mod_cast hn
  have hz' : z ≤ (n:ℝ) := (le_max_left _ _).trans (hn₀.le.trans hnR)
  have hL₁ : 1 ≤ L := by
    have h := (le_max_right _ _).trans (hn₀.le.trans hnR)
    have hh := (div_le_iff₀ ha).mp h
    simpa only [L,mul_comm] using hh
  have hLn : 0 ≤ L := zero_le_one.trans hL₁
  let k := ⌊24*(b:ℝ)*L⌋₊
  let loss := ⌈L⌉₊
  let d (i : ℕ) := ((Y i).card+1)/2
  let p := sqrt density/(4*(b:ℝ))
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hkHi : (k:ℝ) ≤ 24*(b:ℝ)*L := Nat.floor_le (by positivity)
  have hkLo : 24*(b:ℝ)*L < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hLossLo : L ≤ (loss:ℝ) := Nat.le_ceil _
  have hLossHi : (loss:ℝ) < L+1 := Nat.ceil_lt_add_one hLn
  have hHalf (i : ℕ) : (Y i).card ≤ 2*d i := by dsimp only [d]; omega
  have hD (i : ℕ) : (d i : ℝ) ≤ ((Y i).card+1)/2 := by
    apply (le_div_iff₀ (show (0:ℝ) < 2 by norm_num)).mpr
    exact_mod_cast (show d i * 2 ≤ (Y i).card+1 by dsimp only [d]; omega)
  have hRoom (i : ℕ) : (d i:ℝ)+k+loss ≤ ((Y i).card : ℝ)/2+81*(b:ℝ)*L := by
    have hBL := mul_le_mul_of_nonneg_right hb₁ hLn
    have hd' := hD i
    linarith only [hBL,hL₁,hd',hkHi,hLossHi]
  have hLeft (i : ℕ) (hi : i < q) (v : V) (hv : v ∈ X i) :
      d i+k+loss ≤ ((Y i).filter (E v)).card := by
    have h := hL i hi v hv
    rw [hPow] at h
    have h' := hRoom i
    exact_mod_cast (show (d i:ℝ)+k+loss ≤ ((Y i).filter (E v)).card by
      dsimp only [L] at h'
      linarith only [h,h'])
  have hRight (i : ℕ) (hi : i < q) (v : V) (hv : v ∈ Y i) :
      d i+k+loss ≤ ((X i).filter (fun u => E u v)).card := by
    have h := hR i hi v hv
    rw [hPow,hSize i hi] at h
    have h' := hRoom i
    exact_mod_cast (show (d i:ℝ)+k+loss ≤ ((X i).filter (fun u => E u v)).card by
      dsimp only [L] at h'
      linarith only [h,h'])
  have hpTimes : p*(24*(b:ℝ)*L) = 6*density^2*n := by
    calc
      _ = 6*density*(sqrt density*sqrt density)*n := by
        dsimp only [p,L,a]
        field_simp [hbR.ne']
        ring
      _ = _ := by rw [← pow_two (sqrt density),sq_sqrt hDensity.le]; ring
  have hHit (i : ℕ) (hi : i < q) (j : ℕ) (hj : j < q) (hne : i ≠ j) :
      (((X i ∪ Y i) ∩ (X j ∪ Y j)).card : ℝ) ≤ p*((k:ℝ)+1) := by
    rw [← hpTimes] at hOverlap
    exact (hOverlap i hi j hj hne).trans (mul_le_mul_of_nonneg_left hkLo.le hp)
  have hExp : exp (1/2:ℝ)-1 ≤ 3/4 := by
    have h := abs_exp_sub_one_sub_id_le (show |(1/2:ℝ)| ≤ 1 by norm_num)
    have hh := (le_abs_self (exp (1/2:ℝ)-1-1/2)).trans h
    norm_num at hh
    linarith only [hh]
  have hScale : p*(2*(b:ℝ)*density*n) = L/2 := by
    dsimp only [p,L,a]
    field_simp [hbR.ne']
    ring
  have hBudget : p*(exp (1/2:ℝ)-1)*(2*(b:ℝ)*density*n) - (1/2)*L ≤ -L/8 := by
    have h := mul_le_mul_of_nonneg_right hExp (show 0 ≤ p*(2*(b:ℝ)*density*n) by positivity)
    rw [hScale] at h
    have hEq : p*(exp (1/2:ℝ)-1)*(2*(b:ℝ)*density*n) =
        (exp (1/2:ℝ)-1)*(p*(2*(b:ℝ)*density*n)) := by ring
    rw [hEq,hScale]
    linarith only [h]
  have hQR : (q:ℝ) ≤ 3*(b:ℝ)*n := by exact_mod_cast hq
  have hVR : (Fintype.card V:ℝ) ≤ 3*n := by exact_mod_cast hV
  have hNumber : (q:ℝ)*Fintype.card V ≤ 9*(b:ℝ)*n^2 := by
    calc
      _ ≤ (3*(b:ℝ)*n)*(3*n) := mul_le_mul hQR hVR (by positivity) (by positivity)
      _ = _ := by ring
  have hCost : (q:ℝ)*Fintype.card V * exp (p*(exp (1/2:ℝ)-1)*(2*(b:ℝ)*density*n)-(1/2)*L) < 1 :=
    lt_of_le_of_lt (mul_le_mul hNumber (exp_le_exp.mpr hBudget) (exp_pos _).le (by positivity))
      (hz n hz')
  exact exists_matching_packing_of_exponential_bound E X Y q d k loss
    (1/2) p L (2*(b:ℝ)*density*n) (by norm_num) hp hLossLo
    hSize hDis (fun i _ => hHalf i) hLeft hRight hHit hOccur hCost

end OverfullWork.ChenShan
