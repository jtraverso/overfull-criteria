module

public import OverfullWork.FixedLayerRoundScales

@[expose] public section


/-! # Simultaneous nonvacuous scalar margins for Case 2 seed completion

Fix ell from the partition expansion denominator before selecting the
error rate. Then choose integer residue cap, forbidden bound, gain and
predecessor reserve for every sufficiently large half order.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open scoped Classical
set_option maxHeartbeats 32000000

structure CaseTwoCompletionScalars (P T m : ℕ) (A0 : ℝ) (ell : ℕ) where
  h : ℕ
  g : ℕ
  q : ℕ
  Wbar : ℕ
  cap_pos : 0 < h
  gain_pos : 0 < g
  cap : 5*A0 ≤ (h:ℝ)
  forbidden : ((ell:ℝ)+1)*(6*A0+2)+12*(T:ℝ)+8+
    4*A0*(5+(ell:ℝ)*((m:ℝ)+1))/(h:ℝ) ≤ (Wbar:ℝ)
  forbidden_margin : (Wbar:ℝ) ≤ (m:ℝ)/32
  deletion_margin : 2+(Nat.ceil (6*A0):ℝ)+(h:ℝ) ≤ (m:ℝ)/32
  seed_window : ((m/(1024*P)+2*(3*T+1):ℕ):ℝ) ≤ (m:ℝ)/8
  gain : Wbar+g ≤ m/(2^30*P^3)-4*(3*T+1)
  rounds : m/g+3 ≤ ell
  reserve : 4+2*ell < q
  predecessors : q ≤ m/(2^30*P^3)-4*(3*T+1)-(2+Nat.ceil (6*A0)+h)

theorem exists_case_two_completion_scalars (P : ℕ) (hP : 8 ≤ P) :
    ∃ ell : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∀ A0 : ℝ, 0 ≤ A0 → A0 ≤ δ*(m:ℝ) → Nonempty (CaseTwoCompletionScalars P T m A0 ell) := by
  let d := 2^30*P^3
  have hPpos : 0 < P := by omega
  have hd : 0 < d := by dsimp only [d];positivity
  have hd4 : 4 ≤ d := by
    have hp : 0 < P^3 := by positivity
    dsimp only [d]
    omega
  let γ : ℝ := 1/(2*(d:ℝ))
  have hγ : 0 < γ := by dsimp only [γ];positivity
  have hγsmall : γ ≤ 1/8 := by
    dsimp only [γ]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(d:ℝ))).mpr
    have hdR : (4:ℝ) ≤ d := by exact_mod_cast hd4
    linarith
  let ell := 8*d+3
  obtain ⟨δ,hδ,hMargins⟩ := exists_dynamic_budget_margins γ hγ ell
  refine ⟨ell,δ,hδ,?_⟩
  intro T
  let H := 3*T+1
  obtain ⟨N₀,hN₀⟩ := hMargins (2*T)
  let N := max N₀ (max (8*d*(H+1)) (max (64*d) (32*H)))
  refine ⟨N,?_⟩
  intro m hm A0 hA0 hSmall
  have hm₀ : N₀ ≤ m := (le_max_left _ _).trans hm
  have hmH : 8*d*(H+1) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm64 : 64*d ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hm32 : 32*H ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  obtain ⟨h,hPos,hCap,hForb,hDel,hReserve⟩ := hN₀ m hm₀ A0 hA0 hSmall
  let g := m/(4*d)
  let Wbar := Nat.ceil (γ*(m:ℝ)/8)
  let r := m/d-4*H
  let B := Nat.ceil (6*A0)
  let q := r-(2+B+h)
  have hRounds := fixed_layer_round_bound d m hd (by omega)
  have hRate : γ*(m:ℝ) ≤ (r:ℝ) := by
    have hh := actual_robust_rate_lower d m H hd hmH
    simpa only [γ,r,one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  have hWlo : γ*(m:ℝ)/8 ≤ (Wbar:ℝ) := Nat.le_ceil _
  have hWhi : (Wbar:ℝ) < γ*(m:ℝ)/8+1 := Nat.ceil_lt_add_one (by positivity)
  have hmR : (64:ℝ)*(d:ℝ) ≤ m := by exact_mod_cast hm64
  have hdR : (4:ℝ) ≤ d := by exact_mod_cast hd4
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hWsmall : (Wbar:ℝ) ≤ (m:ℝ)/32 := by
    have hh := mul_le_mul_of_nonneg_right hγsmall hm0
    linarith
  have hDsmall : 2+(B:ℝ)+(h:ℝ) ≤ (m:ℝ)/32 := by
    have hh := mul_le_mul_of_nonneg_right hγsmall hm0
    change 2+(B:ℝ)+(h:ℝ) ≤ γ*(m:ℝ)/8 at hDel
    linarith
  have hgDiv : (g:ℝ) ≤ (m:ℝ)/(4*(d:ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 4*(d:ℝ))).mpr
    have hh : ((4*d:ℕ):ℝ)*(g:ℝ) ≤ m := by exact_mod_cast Nat.mul_div_le m (4*d)
    push_cast at hh
    nlinarith only [hh]
  have hgRate : (g:ℝ) ≤ γ*(m:ℝ)/2 := by
    convert hgDiv using 1 <;> dsimp only [γ] <;> field_simp <;> ring
  have hγlarge : (16:ℝ) ≤ γ*(m:ℝ) := by
    dsimp only [γ]
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*(d:ℝ))).mpr
    linarith
  have hGain : Wbar+g ≤ r := by
    have hh : (Wbar:ℝ)+(g:ℝ) ≤ r := by linarith
    exact_mod_cast hh
  have hDle : 2+B+h ≤ r := by
    have hh : (2:ℝ)+(B:ℝ)+(h:ℝ) ≤ r := by
      change 4+2*(ell:ℝ) < γ*(m:ℝ)-(2+(B:ℝ)+(h:ℝ)) at hReserve
      have hel : (0:ℝ) ≤ ell := Nat.cast_nonneg _
      linarith
    exact_mod_cast hh
  have hQ : (q:ℝ)=(r:ℝ)-(2+(B:ℝ)+(h:ℝ)) := by
    dsimp only [q]
    rw [Nat.cast_sub hDle]
    push_cast
    rfl
  have hReserveNat : 4+2*ell < q := by
    have hh : (4:ℝ)+2*(ell:ℝ) < q := by
      change 4+2*(ell:ℝ) < γ*(m:ℝ)-(2+(B:ℝ)+(h:ℝ)) at hReserve
      linarith
    exact_mod_cast hh
  have hCutWindow : ((m/(1024*P)+2*H:ℕ):ℝ) ≤ (m:ℝ)/8 := by
    have hCut : 16*(m/(1024*P)) ≤ m :=
      (Nat.mul_le_mul_right _ (show 16 ≤ 1024*P by omega)).trans (Nat.mul_div_le m _)
    have hh : 8*(m/(1024*P)+2*H) ≤ m := by omega
    have hhR : (8:ℝ)*((m/(1024*P)+2*H:ℕ):ℝ) ≤ m := by exact_mod_cast hh
    linarith
  exact ⟨{
    h := h, g := g, q := q, Wbar := Wbar, cap_pos := hPos, gain_pos := hRounds.1,
    cap := hCap, forbidden := by
      push_cast at hForb
      linarith only [hForb,hWlo],
    forbidden_margin := hWsmall,
    deletion_margin := hDsmall, seed_window := hCutWindow, gain := hGain,
    rounds := hRounds.2, reserve := hReserveNat, predecessors := le_refl _
  }⟩

end OverfullWork.NormalizedCanonicalCandidate
