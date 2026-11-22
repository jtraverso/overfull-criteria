module

public import OverfullWork.DirectedHamiltonFromAbsorber
public import OverfullWork.DirectedRobustAbsorber
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section


/-! The eventual Hamiltonian case of Lo–Patel Theorem 1.3.
All parameters are chosen before the host. -/
namespace OverfullWork.DirectedAbsorbingLadder

open Filter Finset DirectedRobustExpansion
open scoped Classical Topology
universe u
set_option maxHeartbeats 12000000

private theorem eventually_scale (c k : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, k ≤ c*(n:ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (k/c)
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  exact (div_le_iff₀ hc).mp (hN.trans (by exact_mod_cast hn)) |>.trans_eq (mul_comm _ _)

private theorem eventually_cover_weight (A d : ℕ) (hA : 0 < A) (δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, 0 < n/A ∧ (n:ℝ)^2*(1-δ/2)^(n/A) < (1/2:ℝ)^d := by
  let z := 1-δ/2
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hz' : z < 1 := by dsimp [z]; linarith
  have hLim := (tendsto_pow_const_mul_const_pow_of_lt_one 2 hz hz').const_mul (4*(A:ℝ)^2)
  have hEv : ∀ᶠ k : ℕ in atTop, 4*(A:ℝ)^2*((k:ℝ)^2*z^k) < (1/2:ℝ)^d :=
    (show Tendsto (fun k : ℕ => 4*(A:ℝ)^2*((k:ℝ)^2*z^k)) atTop (𝓝 0) by
      simpa only [mul_zero] using hLim).eventually (gt_mem_nhds (by positivity))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hEv
  refine eventually_atTop.mpr ⟨(M+1)*A, fun n hn => ?_⟩
  let k := n/A
  have hk : M+1 ≤ k := (Nat.le_div_iff_mul_le hA).mpr hn
  have hk₁ : 1 ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hBase : (n:ℝ) ≤ (A:ℝ)*((k:ℝ)+1) :=
    (by exact_mod_cast (Nat.lt_mul_div_succ n hA) : (n:ℝ) < (A:ℝ)*((k:ℝ)+1)).le
  have hA0 : (0:ℝ) ≤ A := by positivity
  have hN : (n:ℝ) ≤ 2*(A:ℝ)*(k:ℝ) := by
    nlinarith only [hBase, mul_nonneg hA0 (sub_nonneg.mpr hk₁)]
  have hSq := pow_le_pow_left₀ (Nat.cast_nonneg n : (0:ℝ) ≤ n) hN 2
  have hUpper := mul_le_mul_of_nonneg_right hSq (pow_nonneg hz k)
  refine ⟨by omega, ?_⟩
  calc
    _ ≤ 4*(A:ℝ)^2*((k:ℝ)^2*z^k) := by
      have hEq : (2*(A:ℝ)*(k:ℝ))^2*z^k = 4*(A:ℝ)^2*((k:ℝ)^2*z^k) := by ring
      rw [hEq] at hUpper
      exact hUpper
    _ < _ := hM k (by omega)

/-- A fixed threshold for Hamiltonicity under normalized robust
out-expansion and a linear minimum semidegree. -/
theorem exists_hamilton_threshold (ν τ γ : ℝ) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V),
      N ≤ Fintype.card V → IsRealRobust D ν τ →
      (∀ v, γ*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, γ*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      ∃ T : List V, ∃ x : V, T.Nodup ∧ (∀ v, v ∈ T) ∧ T.head? = some x ∧
        (T ++ [x]).IsChain D.Adj := by
  have hτ : 0 < τ := hν.trans_le hντ
  have hν1 : ν ≤ 1 := by linarith
  have hνγ : ν ≤ γ := by linarith
  have hγ0 : 0 < γ := hν.trans_le hνγ
  let d := ⌈4/(ν^2/32)⌉₊
  let δ := γ^2/32
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hγsq : γ^2 ≤ γ := by nlinarith only [mul_le_mul_of_nonneg_left hγ hγ0.le]
  have hδ' : δ ≤ 1 := by dsimp [δ]; linarith
  let P := ⌈16/ν^2⌉₊+8
  let L := ⌈8/ν⌉₊+4
  let B := P+P/4*L
  let Q := P/4+1
  let K := 2+B+Q*L+P+B+2
  obtain ⟨A, hA⟩ := exists_nat_ge ((K:ℝ)/(ν^2/64)+1)
  have hνs : 0 < ν^2/64 := by positivity
  have hA' : 0 < A := by
    have hh : (0:ℝ) < A := by
      have hNonneg : (0:ℝ) ≤ (K:ℝ)/(ν^2/64) := by positivity
      linarith only [hA,hNonneg]
    exact_mod_cast hh
  have hAK : (K:ℝ) ≤ (ν^2/64)*(A:ℝ) := by
    rw [mul_comm]
    apply (div_le_iff₀ hνs).mp
    linarith
  have hEventually : ∀ᶠ n : ℕ in atTop,
      (K:ℝ) ≤ (ν^2/64)*(n:ℝ) ∧ 32 ≤ ν*(n:ℝ) ∧
      128 ≤ (ν/2)^3*((n:ℝ)/2) ∧ 4 ≤ (ν^2/32)*((n:ℝ)/2) ∧
      0 < n/A ∧ (n:ℝ)^2*(1-δ/2)^(n/A) < (1/2:ℝ)^d := by
    filter_upwards [eventually_scale (ν^2/64) K hνs, eventually_scale ν 32 hν,
      eventually_scale ((ν/2)^3/2) 128 (by positivity),
      eventually_scale ((ν^2/32)/2) 4 (by positivity),
      eventually_cover_weight A d hA' δ hδ hδ'] with n hK hn hn' hnd hCover
    exact ⟨hK, hn, by linarith only [hn'], by linarith only [hnd], hCover⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hEventually
  refine ⟨N, ?_⟩
  intro V _ D hn hRobust hIn hOut
  let n := Fintype.card V
  obtain ⟨hK, hN₁, hN₂, hN₃, hm, hSmall⟩ := hN n hn
  have hn₀ : 0 < n := Nat.pos_of_ne_zero (fun he => by simp [he] at hm)
  let _ : Nonempty V := Fintype.card_pos_iff.mp hn₀
  let m := n/A
  let r := ⌈ν*(n:ℝ)⌉₊
  let t := ⌈τ*(n:ℝ)⌉₊
  let s := ⌊ν^2*(n:ℝ)/8⌋₊
  let r' := ⌊ν*(n:ℝ)/4⌋₊
  let g := ⌊γ*(n:ℝ)/2⌋₊
  have hmA : (m:ℝ)*(A:ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n A
  have hMK : (m:ℝ)*(K:ℝ) ≤ (ν^2/64)*(n:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hAK (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    have h2 := mul_le_mul_of_nonneg_left hmA hνs.le
    nlinarith only [h1,h2]
  let bulk := m*K+K
  have hBulk : (bulk:ℝ) ≤ (ν^2/32)*(n:ℝ) := by
    simp only [bulk, Nat.cast_add, Nat.cast_mul]
    linarith only [hMK,hK]
  have hK1 : 1 ≤ K := by dsimp [K]; omega
  have hOne : 1 ≤ (ν^2/64)*(n:ℝ) := (by exact_mod_cast hK1 : (1:ℝ) ≤ K).trans hK
  have hνsn : ν^2*(n:ℝ) ≤ ν*(n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hν1 hν.le
    nlinarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hνγn := mul_le_mul_of_nonneg_right hνγ (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hτγn := mul_le_mul_of_nonneg_right hτγ (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hr : ν*(n:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
  have ht : (t:ℝ) < τ*(n:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have hsUpper : (s:ℝ) ≤ ν^2*(n:ℝ)/8 := Nat.floor_le (by positivity)
  have hsLower : ν^2*(n:ℝ)/16 ≤ (s:ℝ) := by
    have h := Nat.lt_floor_add_one (ν^2*(n:ℝ)/8)
    change _ < (s:ℝ)+1 at h
    linarith only [h,hOne]
  have hs : 0 < s := by
    exact_mod_cast (show (0:ℝ) < s by linarith only [hsLower,hOne])
  have hsr : s ≤ r := by exact_mod_cast (show (s:ℝ) ≤ r by linarith only [hsUpper,hνsn,hr,hN₁])
  have hrt : r ≤ t := Nat.ceil_mono (mul_le_mul_of_nonneg_right hντ (Nat.cast_nonneg n))
  have hRev : s*n ≤ r*(r-s) := by
    have hDiff : ν*(n:ℝ)/2 ≤ (r:ℝ)-(s:ℝ) := by linarith only [hsUpper,hνsn,hr,hN₁]
    have hLow := mul_le_mul hr hDiff (by linarith only [hN₁]) (Nat.cast_nonneg r : (0:ℝ) ≤ _)
    have hHi := mul_le_mul_of_nonneg_right hsUpper (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have h : (s:ℝ)*(n:ℝ) ≤ (r:ℝ)*((r:ℝ)-(s:ℝ)) := by
      nlinarith only [hLow,hHi,sq_nonneg (ν*(n:ℝ))]
    exact_mod_cast (by simpa only [Nat.cast_mul, Nat.cast_sub hsr] using h : ((s*n:ℕ):ℝ) ≤ ((r*(r-s):ℕ):ℝ))
  have hSemidegree : (2*t+s:ℕ) ≤ γ*(n:ℝ) := by
    push_cast
    linarith only [ht, hsUpper,hνsn,hνγn,hτγn,hN₁]
  have hr'Upper : (r':ℝ) ≤ ν*(n:ℝ)/4 := Nat.floor_le (by positivity)
  have hr'Lower : ν*(n:ℝ)/8 ≤ (r':ℝ) := by
    have h := Nat.lt_floor_add_one (ν*(n:ℝ)/4)
    change _ < (r':ℝ)+1 at h
    linarith only [h,hN₁]
  have hr' : 0 < r' := by exact_mod_cast (show (0:ℝ) < r' by linarith only [hr'Lower,hN₁])
  have hP : n/s+8 ≤ P := by
    apply Nat.add_le_add_right
    apply Nat.div_le_of_le_mul
    have hCeil := Nat.le_ceil (16/ν^2)
    have hLe : (n:ℝ) ≤ (16/ν^2)*(s:ℝ) := by
      have h := mul_le_mul_of_nonneg_left hsLower (show 0 ≤ 16/ν^2 by positivity)
      have hEq : (16/ν^2)*(ν^2*(n:ℝ)/16) = n := by field_simp [hν.ne']
      rwa [hEq] at h
    change n ≤ s*⌈16/ν^2⌉₊
    rw [Nat.mul_comm s]
    exact_mod_cast hLe.trans (mul_le_mul_of_nonneg_right hCeil (Nat.cast_nonneg s))
  have hL : n/r'+4 ≤ L := by
    apply Nat.add_le_add_right
    apply Nat.div_le_of_le_mul
    have hLe : (n:ℝ) ≤ (8/ν)*(r':ℝ) := by
      have h := mul_le_mul_of_nonneg_left hr'Lower (show 0 ≤ 8/ν by positivity)
      have hEq : (8/ν)*(ν*(n:ℝ)/8) = n := by field_simp [hν.ne']
      rwa [hEq] at h
    change n ≤ r'*⌈8/ν⌉₊
    rw [Nat.mul_comm r']
    exact_mod_cast hLe.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil (8/ν)) (Nat.cast_nonneg r'))
  have hgUpper : (g:ℝ) ≤ γ*(n:ℝ)/2 := Nat.floor_le (by positivity)
  have hgLower : γ*(n:ℝ)/4 ≤ (g:ℝ) := by
    have h := Nat.lt_floor_add_one (γ*(n:ℝ)/2)
    change _ < (g:ℝ)+1 at h
    linarith only [h,hN₁,hνγn]
  have hg : 2 ≤ g := by exact_mod_cast (show (2:ℝ) ≤ g by linarith only [hgLower,hN₁,hνγn])
  have hgLower' : γ*(n:ℝ)/8 ≤ (g:ℝ)-1 := by linarith only [hgLower,hN₁,hνγn]
  have hDensity : δ*(n:ℝ)^2 ≤ (g:ℝ)*(g-1) := by
    have h := mul_le_mul hgLower hgLower' (by nlinarith only [hgLower',hνγn,hN₁])
      (Nat.cast_nonneg g : (0:ℝ) ≤ g)
    dsimp [δ]
    nlinarith only [h]
  have hPay : 2*m+g ≤ bulk+g := by
    have hK' : 2 ≤ K := by dsimp [K]; omega
    have hh := Nat.mul_le_mul_left m hK'
    rw [Nat.mul_comm m 2] at hh
    dsimp [bulk]
    omega
  have hCoverDegree : ((2*m+g:ℕ):ℝ) ≤ γ*(n:ℝ) := by
    have hh : ((2*m+g:ℕ):ℝ) ≤ (bulk:ℝ)+(g:ℝ) := by exact_mod_cast hPay
    linarith only [hh,hBulk,hgUpper,hνsn,hνγn,hN₁]
  have hBulk₁ : 2*m+m*B+P ≤ bulk := by
    have hKB : 2+B ≤ K := by dsimp [K]; omega
    have hKP : P ≤ K := by dsimp [K]; omega
    have hh := Nat.mul_le_mul_left m hKB
    rw [Nat.mul_add, Nat.mul_comm m 2] at hh
    change _ ≤ m*K+K
    omega
  have hBulk₂ : 2*m+m*B+B ≤ bulk := by
    have hKB : 2+B ≤ K := by dsimp [K]; omega
    have hKP : B ≤ K := by dsimp [K]; omega
    have hh := Nat.mul_le_mul_left m hKB
    rw [Nat.mul_add, Nat.mul_comm m 2] at hh
    change _ ≤ m*K+K
    omega
  have hBulk₃ : m*B+m*Q*L ≤ bulk := by
    have hKB : B+Q*L ≤ K := by dsimp [K]; omega
    have hh := Nat.mul_le_mul_left m hKB
    rw [Nat.mul_add, ← Nat.mul_assoc] at hh
    change _ ≤ m*K+K
    omega
  have hSpine : bulk ≤ s := by exact_mod_cast
    (show (bulk:ℝ) ≤ s by linarith only [hBulk,hsLower,hOne])
  have hRoute : bulk+r' ≤ r := by exact_mod_cast
    (show (bulk:ℝ)+(r':ℝ) ≤ r by linarith only [hBulk,hr'Upper,hr,hνsn,hN₁])
  have hOutDegree : (t:ℝ)+(bulk:ℝ) ≤ γ*(n:ℝ) := by
    linarith only [ht,hBulk,hτγn,hνsn,hνγn,hN₁]
  have pay_degree {a b : ℕ} (hab : a ≤ b) (h : (b:ℝ) ≤ γ*(n:ℝ)) {z : ℕ}
      (hz : γ*(n:ℝ) ≤ (z:ℝ)) : a ≤ z := by exact_mod_cast
    ((by exact_mod_cast hab : (a:ℝ) ≤ b).trans (h.trans hz))
  obtain ⟨C,hC⟩ := exists_robust_absorbing_cycle D (m := m) (d := d)
    (g := g) (r := r) (s := s) (t := t) (r' := r') (L := L) (P := P) (B := B) δ hm hg hδ.le hδ' hDensity
    (fun v => pay_degree le_rfl hCoverDegree (hIn v))
    (fun v => pay_degree le_rfl hCoverDegree (hOut v)) hSmall hs hsr hrt hRev
    (fun v => pay_degree le_rfl hSemidegree (hIn v))
    (fun v => pay_degree le_rfl hSemidegree (hOut v))
    (integer_of_real D ν τ hν.le hRobust) hr' hL hP (le_refl B)
    (hBulk₁.trans hSpine) ((Nat.add_le_add_right hBulk₂ _).trans hRoute)
    ((Nat.add_le_add_right hBulk₃ _).trans hRoute)
    (fun v => pay_degree (by simpa only [Nat.add_assoc] using Nat.add_le_add_left hBulk₂ t)
      (by push_cast; exact hOutDegree) (hOut v))
    (fun v => pay_degree (by simpa only [Nat.add_assoc] using Nat.add_le_add_left hBulk₃ t)
      (by push_cast; exact hOutDegree) (hOut v))
  have hC' : (C.vertices.length:ℝ) ≤ (bulk:ℝ) := by exact_mod_cast hC.trans hBulk₃
  obtain ⟨T,hT⟩ := C.hamilton_of_robust D ν τ γ hν hντ hτγ hγ hRobust hIn hOut
    (by linarith only [hC',hBulk,hνsn,hN₁]) hN₁ hN₂ hN₃ (Nat.le_ceil _)
  exact ⟨T,C.root,hT⟩

end OverfullWork.DirectedAbsorbingLadder
