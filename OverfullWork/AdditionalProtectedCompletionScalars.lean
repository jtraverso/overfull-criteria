module

public import OverfullWork.FixedLayerRoundScales

@[expose] public section


/-! # Simultaneous nonvacuous scalar margins for Case 2 seed completion

Fix ell from the partition expansion denominator before selecting the
error rate. Pay the full added protected-set cost 2z, and choose integer cap, bound, gain and
predecessor reserve for every sufficiently large half order.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open scoped Classical
set_option maxHeartbeats 32000000

structure AdditionalProtectedCompletionScalars (P T m : ℕ) (A0 ζ : ℝ) (ell z : ℕ) where
  h : ℕ
  g : ℕ
  q : ℕ
  Wbar : ℕ
  order_expansion : 64*(2^30*P^3) ≤ m
  robust_rate : (m:ℝ)/(2*((2^30*P^3:ℕ):ℝ)) ≤ (m/(2^30*P^3)-4*(3*T+1):ℕ)
  cap_pos : 0 < h
  gain_pos : 0 < g
  cap : 5*A0 ≤ (h:ℝ)
  cap_rate : (h:ℝ) ≤ ζ*(m:ℝ)/8
  cap_expansion : (h:ℝ) ≤ (1/(2*((2^30*P^3:ℕ):ℝ)))*(m:ℝ)/8
  residue_ratio_target : 4*A0*(5+(ell:ℝ)*((m:ℝ)+1))/(h:ℝ) ≤ ζ*(m:ℝ)/8
  residue_ratio_expansion : 4*A0*(5+(ell:ℝ)*((m:ℝ)+1))/(h:ℝ) ≤ (1/(2*((2^30*P^3:ℕ):ℝ)))*(m:ℝ)/8
  forbidden : ((ell:ℝ)+1)*(6*A0+2)+12*(T:ℝ)+8+2*(z:ℝ)+
    4*A0*(5+(ell:ℝ)*((m:ℝ)+1))/(h:ℝ) ≤ (Wbar:ℝ)
  forbidden_margin : (Wbar:ℝ) ≤ (m:ℝ)/32
  deletion_margin : 2+(Nat.ceil (6*A0):ℝ)+(h:ℝ) ≤ (m:ℝ)/32
  seed_window : ((m/(1024*P)+2*(3*T+1):ℕ):ℝ) ≤ (m:ℝ)/8
  gain : Wbar+g ≤ m/(2^30*P^3)-4*(3*T+1)
  rounds : m/g+3 ≤ ell
  reserve : 4+2*ell < q
  predecessors : q ≤ m/(2^30*P^3)-4*(3*T+1)-(2+Nat.ceil (6*A0)+h)

theorem exists_additional_protected_completion_scalars (P : ℕ) (hP : 8 ≤ P) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ ell : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∀ z : ℕ, z ≤ m/(32*(2^30*P^3)) → ∀ A0 : ℝ, 0 ≤ A0 → A0 ≤ δ*(m:ℝ) →
        Nonempty (AdditionalProtectedCompletionScalars P T m A0 ζ ell z) := by
  let d := 2^30*P^3
  have hPpos : 0 < P := by omega
  have hd : 0 < d := by dsimp only [d];positivity
  have hd4 : 8 ≤ d := by
    have hp : 0 < P^3 := by positivity
    dsimp only [d]
    omega
  let γ₀ : ℝ := 1/(2*(d:ℝ))
  have hγ₀ : 0 < γ₀ := by dsimp only [γ₀];positivity
  have hγ₀small : γ₀ ≤ 1/16 := by
    dsimp only [γ₀]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(d:ℝ))).mpr
    have hdR : (8:ℝ) ≤ d := by exact_mod_cast hd4
    linarith
  let γ := min γ₀ ζ
  have hγ : 0 < γ := lt_min hγ₀ hζ
  have hγBase : γ ≤ γ₀ := min_le_left _ _
  have hγLambda : γ ≤ ζ := min_le_right _ _
  let ell := 8*d+3
  obtain ⟨δ,hδ,hMargins⟩ := exists_dynamic_budget_margins γ hγ ell
  refine ⟨ell,δ,hδ,?_⟩
  intro T
  let H := 3*T+1
  obtain ⟨N₀,hN₀⟩ := hMargins (2*T)
  let N := max N₀ (max (8*d*(H+1)) (max (64*d) (32*H)))
  refine ⟨N,?_⟩
  intro m hm z hz A0 hA0 hSmall
  have hm₀ : N₀ ≤ m := (le_max_left _ _).trans hm
  have hmH : 8*d*(H+1) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm64 : 64*d ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hm32 : 32*H ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  obtain ⟨h,hPos,hCap,hForb,hDel,hReserve⟩ := hN₀ m hm₀ A0 hA0 hSmall
  let g := m/(4*d)
  let Wbar := Nat.ceil (γ₀*(m:ℝ)/4)
  let r := m/d-4*H
  let B := Nat.ceil (6*A0)
  let q := r-(2+B+h)
  have hRounds := fixed_layer_round_bound d m hd (by omega)
  have hRateBase : γ₀*(m:ℝ) ≤ (r:ℝ) := by
    have hh := actual_robust_rate_lower d m H hd hmH
    simpa only [γ₀,r,one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  have hActive := mul_le_mul_of_nonneg_right hγBase (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hRate : γ*(m:ℝ) ≤ (r:ℝ) := hActive.trans hRateBase
  have hLambda := mul_le_mul_of_nonneg_right hγLambda (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hWlo : γ₀*(m:ℝ)/4 ≤ (Wbar:ℝ) := Nat.le_ceil _
  have hWhi : (Wbar:ℝ) < γ₀*(m:ℝ)/4+1 := Nat.ceil_lt_add_one (by positivity)
  have hZmul : z*(32*d) ≤ m := (Nat.le_div_iff_mul_le (by positivity : 0 < 32*d)).mp hz
  have hZdiv : (z:ℝ) ≤ (m:ℝ)/(32*(d:ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 32*(d:ℝ))).mpr
    exact_mod_cast hZmul
  have hZrate : 2*(z:ℝ) ≤ γ₀*(m:ℝ)/8 := by
    have hIdentity : (m:ℝ)/(32*(d:ℝ))=γ₀*(m:ℝ)/16 := by
      dsimp only [γ₀]
      field_simp
      ring
    rw [hIdentity] at hZdiv
    linarith
  have hmR : (64:ℝ)*(d:ℝ) ≤ m := by exact_mod_cast hm64
  have hdR : (8:ℝ) ≤ d := by exact_mod_cast hd4
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hWsmall : (Wbar:ℝ) ≤ (m:ℝ)/32 := by
    have hh := mul_le_mul_of_nonneg_right hγ₀small hm0
    linarith
  have hDsmall : 2+(B:ℝ)+(h:ℝ) ≤ (m:ℝ)/32 := by
    have hh := mul_le_mul_of_nonneg_right hγ₀small hm0
    change 2+(B:ℝ)+(h:ℝ) ≤ γ*(m:ℝ)/8 at hDel
    linarith
  have hgDiv : (g:ℝ) ≤ (m:ℝ)/(4*(d:ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 4*(d:ℝ))).mpr
    have hh : ((4*d:ℕ):ℝ)*(g:ℝ) ≤ m := by exact_mod_cast Nat.mul_div_le m (4*d)
    push_cast at hh
    nlinarith only [hh]
  have hgRate : (g:ℝ) ≤ γ₀*(m:ℝ)/2 := by
    convert hgDiv using 1 <;> dsimp only [γ₀] <;> field_simp <;> ring
  have hγ₀large : (16:ℝ) ≤ γ₀*(m:ℝ) := by
    dsimp only [γ₀]
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
  have hRatio : 4*A0*(5+(ell:ℝ)*((m:ℝ)+1))/(h:ℝ) ≤ γ*(m:ℝ)/8 := by
    have hEll : (0:ℝ) ≤ ell := Nat.cast_nonneg _
    have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
    push_cast at hForb
    nlinarith only [hForb,hEll,hT,hA0]
  exact ⟨{
    h := h, g := g, q := q, Wbar := Wbar,
    order_expansion := hm64,
    robust_rate := actual_robust_rate_lower d m H hd hmH,
    cap_pos := hPos, gain_pos := hRounds.1,
    cap := hCap, cap_rate := by
      have hNonneg : (0:ℝ) ≤ B := Nat.cast_nonneg _
      change 2+(B:ℝ)+(h:ℝ) ≤ γ*(m:ℝ)/8 at hDel
      linarith,
    cap_expansion := by
      have hNonneg : (0:ℝ) ≤ B := Nat.cast_nonneg _
      change 2+(B:ℝ)+(h:ℝ) ≤ γ*(m:ℝ)/8 at hDel
      change (h:ℝ) ≤ γ₀*(m:ℝ)/8
      linarith,
    residue_ratio_target := by linarith only [hRatio,hLambda],
    residue_ratio_expansion := by change _ ≤ γ₀*(m:ℝ)/8;linarith only [hRatio,hActive],
    forbidden := by
      push_cast at hForb
      linarith only [hForb,hWlo,hZrate,hActive],
    forbidden_margin := hWsmall,
    deletion_margin := hDsmall, seed_window := hCutWindow, gain := hGain,
    rounds := hRounds.2, reserve := hReserveNat, predecessors := le_refl _
  }⟩

end OverfullWork.NormalizedCanonicalCandidate
