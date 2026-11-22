module

public import OverfullWork.RobustRegularFactor
public import OverfullWork.RealDirectedRobustExpansion

@[expose] public section


/-! Kühn–Osthus, Applications Lemma 3.4, with the target degree supplied
as an integer in an explicit interval. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u

theorem exists_real_robust_regular_factor (ν τ α ξ : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hτ : 0 ≤ τ) (hτα : 16*τ ≤ α) (hα : 0 < α)
    (hξ : 0 < ξ) (hξα : 8*ξ ≤ α) (hξν : 32*ξ ≤ ν^2) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (D : Digraph V) (k : ℕ), N ≤ Fintype.card V → IsRealRobust D ν τ →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      ξ*(Fintype.card V:ℝ)/2 ≤ (k:ℝ) → (k:ℝ) ≤ ξ*(Fintype.card V:ℝ) →
      ∃ H : Digraph V, H ≤ D ∧ IsRealRobust H μ τ ∧
        ∀ v, outDegree H v = k ∧ inDegree H v = k := by
  let p := ν*ξ/512
  have hp : 0 < p := by dsimp [p]; positivity
  have hp4 : p ≤ 1/4 := by dsimp [p]; nlinarith only [hξν,hξ,hν,hν1,mul_nonneg hν.le (sub_nonneg.mpr hν1)]
  have hp1 : p < 1 := by linarith only [hp4]
  obtain ⟨N,hN⟩ := DirectedRobustSplit.exists_real_relative_split.{u} p ν τ α (1/2)
    hp hp1 hν hτ hα (by norm_num)
  refine ⟨p*ν/2,by positivity,max N (max ⌈1/p⌉₊ ⌈16/α⌉₊),?_⟩
  intro V _ _ D k hn hD hIn hOut hklo hkhi
  let n := Fintype.card V
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hn' := le_max_left N (max ⌈1/p⌉₊ ⌈16/α⌉₊)
  have hpN : 1 ≤ p*(n:ℝ) := by
    have hb : ⌈1/p⌉₊ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have h := (div_le_iff₀ hp).mp (Nat.ceil_le.mp hb)
    simpa [mul_comm] using h
  have hαN : 16 ≤ α*(n:ℝ) := by
    have hb : ⌈16/α⌉₊ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have h := (div_le_iff₀ hα).mp (Nat.ceil_le.mp hb)
    simpa [mul_comm] using h
  obtain ⟨A,hAD,hAI,hAO,hBI,hBO,hA,hB⟩ := hN D (hn'.trans hn) hD hIn hOut
  let B := D \ A
  let a := ⌈2*p*(n:ℝ)⌉₊
  let L := k-a
  let rA := ⌈(p*ν/2)*(n:ℝ)⌉₊
  let rB := ⌈((1-p)*ν/2)*(n:ℝ)⌉₊
  let t := ⌈τ*(n:ℝ)⌉₊
  have ha : (a:ℝ) ≤ 3*p*(n:ℝ) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2*p*(n:ℝ) by positivity)
    dsimp only [a]
    linarith only [hc,hpN]
  have hak : (a:ℝ) ≤ ν*(k:ℝ)/16 := by
    have hm := mul_le_mul_of_nonneg_left hklo hν.le
    dsimp only [p] at ha
    nlinarith only [ha,hm,mul_nonneg hν.le (Nat.cast_nonneg k : 0 ≤ (k:ℝ))]
  have hak2 : (a:ℝ) ≤ (k:ℝ)/2 := by
    have hm := mul_le_mul_of_nonneg_right hν1 (Nat.cast_nonneg k : 0 ≤ (k:ℝ))
    nlinarith only [hak,hm, (Nat.cast_nonneg k : 0 ≤ (k:ℝ))]
  have hakN : a ≤ k := by exact_mod_cast (show (a:ℝ) ≤ k by linarith)
  have hL : (L:ℝ) = (k:ℝ)-(a:ℝ) := Nat.cast_sub hakN
  have hLhalf : (k:ℝ)/2 ≤ L := by linarith only [hak2,hL]
  have hR : ν*(n:ℝ)/4 ≤ (rB:ℝ) := by
    have hr := Nat.le_ceil (((1-p)*ν/2)*(n:ℝ))
    have hm := mul_le_mul_of_nonneg_right (show 1/2 ≤ 1-p by linarith only [hp4])
      (mul_nonneg hν.le hn0)
    dsimp only [rB]
    nlinarith only [hr,hm]
  have ht : (t:ℝ) ≤ τ*(n:ℝ)+1 := (Nat.ceil_lt_add_one (mul_nonneg hτ hn0)).le
  have hkα : (k:ℝ) ≤ α*(n:ℝ)/8 := by
    nlinarith only [hkhi,mul_le_mul_of_nonneg_right hξα hn0]
  have hTB : 2*(t:ℝ)+k ≤ 3*α*(n:ℝ)/8 := by
    nlinarith only [ht,hkα,hαN,mul_le_mul_of_nonneg_right hτα hn0]
  have hReserve {d dB : ℕ} (hd : α*(n:ℝ) ≤ d)
      (hdB : |(dB:ℝ)-(1-p)*(d:ℝ)| < (1/2:ℝ)*(1-p)*(d:ℝ)) :
      2*t+k ≤ dB := by
    have hh := (abs_lt.mp hdB).1
    have hc := mul_le_mul_of_nonneg_left hd (by linarith only [hp4] : 0 ≤ 1-p)
    have hm := mul_le_mul_of_nonneg_right (show 3/4 ≤ 1-p by linarith only [hp4])
      (mul_nonneg hα.le hn0)
    exact_mod_cast (show 2*(t:ℝ)+k ≤ dB by nlinarith only [hh,hc,hm,hTB])
  have hSeed {d dA : ℕ} (hd : d ≤ n)
      (hdA : |(dA:ℝ)-p*(d:ℝ)| < (1/2:ℝ)*p*(d:ℝ)) : dA ≤ a := by
    have hh := (abs_lt.mp hdA).2
    have hc := mul_le_mul_of_nonneg_left (show (d:ℝ) ≤ n by exact_mod_cast hd) hp.le
    have ha' := Nat.le_ceil (2*p*(n:ℝ))
    exact_mod_cast (show (dA:ℝ) ≤ (a:ℝ) by nlinarith only [hh,hc,ha',mul_nonneg hp.le hn0])
  have hTwo : k ≤ 2*L := by exact_mod_cast (show (k:ℝ) ≤ 2*(L:ℝ) by linarith)
  have hGap : 2*(k-L)*n ≤ L*rB := by
    have hsub : k-L = a := by dsimp [L]; omega
    rw [hsub]
    have hm := mul_le_mul_of_nonneg_right hak hn0
    have hprod := mul_le_mul hLhalf hR (by positivity : 0 ≤ ν*(n:ℝ)/4)
      (Nat.cast_nonneg L)
    exact_mod_cast (show 2*(a:ℝ)*(n:ℝ) ≤ (L:ℝ)*(rB:ℝ) by nlinarith only [hm,hprod])
  have hSquare : 2*k*n ≤ rB*rB := by
    have h1 := mul_le_mul_of_nonneg_right hkhi hn0
    have h2 := mul_le_mul_of_nonneg_right hξν (mul_nonneg hn0 hn0)
    have h3 := mul_le_mul hR hR (by positivity : 0 ≤ ν*(n:ℝ)/4) (Nat.cast_nonneg rB)
    exact_mod_cast (show 2*(k:ℝ)*(n:ℝ) ≤ (rB:ℝ)*(rB:ℝ) by nlinarith only [h1,h2,h3])
  obtain ⟨H,_,hH,hRob,hReg⟩ := exists_robust_regular_completion A B k rA rB t L
    (integer_of_real A _ τ (by positivity) hA)
    (integer_of_real B _ τ (by positivity) hB)
    (by intro v w h; exact h.2.2 h.1)
    (Nat.sub_le _ _) hTwo hGap hSquare
    (fun v => (by omega : t+k ≤ 2*t+k).trans (hReserve (hIn v) (hBI v)))
    (fun v => hReserve (hOut v) (hBO v))
    (by
      intro v
      have hi := hSeed (DirectedArcSelection.inDegree_le D v) (hAI v)
      have ho := hSeed (DirectedArcSelection.outDegree_le D v) (hAO v)
      dsimp only [L]
      omega)
  refine ⟨H,hH.trans (sup_le hAD ?_),?_,hReg⟩
  · exact fun _ _ h => h.1
  · exact real_of_integer_at_ceil_interval H rA _ τ hτ hRob (Nat.le_ceil _)

end OverfullWork.DirectedRobustExpansion
