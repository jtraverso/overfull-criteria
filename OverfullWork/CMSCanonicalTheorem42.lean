module

public import OverfullWork.CMSCanonicalBundleComparison
public import OverfullWork.CMSTheorem42

@[expose] public section


/-! The canonical-completion statement of CMS Theorem 4.2, retaining
the ranked support bound and the paper's local error coefficients. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion
open scoped Classical

set_option maxHeartbeats 1800000 in
theorem cms_theorem_4_2_for_canonical_completion (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ α/64 ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {m : ℕ} {D : MultiGraph (Fin (m+1) × Bool)} {d : ℕ}
          (C : Completion D d) (rank : Fin (m+1) × Bool → ℕ),
          let W := Fin (m+1) × Bool
          let a : W := (0,false)
          let b : W := (0,true)
          let n := Fintype.card W
          let G := (D.addCopies C.L).addCopies C.N
          N ≤ n → d < n → α*(n:ℝ) ≤ (d:ℝ) →
          IsRealRobust G.supportGraph ν τ →
          (∀ v, v ≠ a → D.degree b ≤ D.degree v) →
          (∀ v, v ≠ a → v ≠ b → (D.mult s(a,v):ℝ) ≤ 2*η^2*(n:ℝ)) →
          (∀ v, v ≠ a → v ≠ b → 2 ≤ rank v) →
          (∀ v, v ≠ a → v ≠ b →
            ((rank v-1:ℕ):ℝ)/(rank v:ℝ)*(d:ℝ)-6*η*(n:ℝ) ≤ G.supportGraph.degree v) →
          ((d:ℝ)-(G.mult s(a,b):ℝ)-13*η*(n:ℝ) ≤ G.supportGraph.degree b) →
          (∀ v, v ≠ a → v ≠ b →
            (d:ℝ)-(G.mult s(a,v):ℝ)-6*η*(n:ℝ) ≤ G.supportGraph.degree v) →
          (Nonempty (G.EdgeColoring d) ↔ ¬ G.HasOverfullSubset d) := by
  obtain ⟨τ,hτ,hτcap,hProfile⟩ := CMSBalancedCut.cms_theorem_4_2 α hα hα₁
  refine ⟨τ,hτ,hτcap,?_⟩
  intro ν hν hντ
  obtain ⟨ζ,hζ,hComplete⟩ := hProfile ν hν hντ
  obtain ⟨N₀,hN₀⟩ := hComplete ζ hζ le_rfl
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (16/ζ)
  let ηMax := min (1/2) (ζ/56)
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  refine ⟨max N₀ N₁,?_⟩
  intro m D d C rank W a b n G hN hD hDens hRob hOrder hBase hRank hHigh hB hOrd
  let E := ⌈13*η*(n:ℝ)⌉₊
  let Y := ⌈2*η^2*(n:ℝ)⌉₊
  have hTwo : n = 2*(m+1) := by simp [n,W,Nat.mul_comm]
  have hTwoR : (n:ℝ) = 2*((m+1:ℕ):ℝ) := by exact_mod_cast hTwo
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hηcap : η ≤ 1/2 := hηMax.trans (min_le_left _ _)
  have hηζ : η ≤ ζ/56 := hηMax.trans (min_le_right _ _)
  have hFour : 16 ≤ ζ*(n:ℝ) := by
    have hR : (N₁:ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hN
    have hh := (div_le_iff₀ hζ).mp (hN₁.trans hR)
    nlinarith only [hh]
  have hScale : ((E+Y+2:ℕ):ℝ) ≤ ζ*((m+1:ℕ):ℝ) := by
    have hEUp := Nat.ceil_lt_add_one (show 0 ≤ 13*η*(n:ℝ) by positivity)
    have hYUp := Nat.ceil_lt_add_one (show 0 ≤ 2*η^2*(n:ℝ) by positivity)
    change (E:ℝ) < 13*η*(n:ℝ)+1 at hEUp
    change (Y:ℝ) < 2*η^2*(n:ℝ)+1 at hYUp
    have hQuad : 2*η^2*(n:ℝ) ≤ η*(n:ℝ) := by
      have hh := mul_nonneg hη (sub_nonneg.mpr hηcap)
      have hh' := mul_le_mul_of_nonneg_right (show 2*η^2 ≤ η by nlinarith only [hh]) hn
      exact hh'
    have hLin := mul_le_mul_of_nonneg_right hηζ hn
    have hh : ζ*(n:ℝ) = 2*(ζ*((m+1:ℕ):ℝ)) := by rw [hTwoR]; ring
    push_cast at hh ⊢
    nlinarith only [hEUp,hYUp,hQuad,hLin,hFour,hh]
  have hBaseN v (hva : v ≠ a) (hvb : v ≠ b) : D.mult s(a,v) ≤ Y := by
    exact_mod_cast (hBase v hva hvb).trans (Nat.le_ceil _)
  have hER : 13*η*(n:ℝ) ≤ (E:ℝ) := Nat.le_ceil _
  have hLocal v (hv : v ≠ a) : d ≤ G.supportGraph.degree v+G.mult s(a,v)+E := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    by_cases hve : v = b
    · rw [hve]
      linarith only [hB,hER]
    · linarith only [hOrd v hv hve,hER,mul_nonneg hη hn]
  have hOrdinary v (hva : v ≠ a) (hvb : v ≠ b) :
      (d:ℝ)/2-((E+Y+2:ℕ):ℝ) ≤ G.supportGraph.degree v := by
    have hRankV := hRank v hva hvb
    have hr : (0:ℝ) < rank v := by exact_mod_cast (show 0 < rank v by omega)
    have hHalf : (1:ℝ)/2 ≤ ((rank v-1:ℕ):ℝ)/(rank v:ℝ) := by
      apply (le_div_iff₀ hr).mpr
      rw [Nat.cast_sub (by omega : 1 ≤ rank v),Nat.cast_one]
      have hh : (2:ℝ) ≤ rank v := by exact_mod_cast hRankV
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hHalf (Nat.cast_nonneg (α := ℝ) d)
    push_cast
    linarith only [hh,hHigh v hva hvb,hER,mul_nonneg hη hn,Nat.cast_nonneg (α := ℝ) Y]
  exact hN₀ G a b d (m+1) (E+Y+2) ((le_max_left _ _).trans hN) hTwo
    (by simp [a,b]) C.regular hDens (by omega) hRob hScale
    (C.bundle_comparison_of_support E Y hOrder hBaseN hLocal)
    (fun v hv => (hLocal v hv).trans (by omega)) hOrdinary

end OverfullWork.CanonicalRegularization
