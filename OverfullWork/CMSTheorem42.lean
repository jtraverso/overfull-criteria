module

public import OverfullWork.CMSHeavyPairCaseOne
public import OverfullWork.CMSTheorem42CaseTwo

@[expose] public section


/-! The regular multigraph theorem of Chen–McDonald–Shan, using
the degree and bundle outputs of their canonical completion. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph RobustExpansion HeavyPairBoundary
open scoped Classical
universe u

/-- The multigraph overfull obstruction follows by counting the
copies of each colour inside a vertex set. -/
theorem no_overfull_of_edgeColoring {V : Type*} [Fintype V] [DecidableEq V]
    (M : MultiGraph V) (d : ℕ) (C : M.EdgeColoring d) : ¬ M.HasOverfullSubset d := by
  rintro ⟨S,hS⟩
  have hBound (i : Fin d) : (C.colourGraph i).edgesWithin S ≤ S.card/2 :=
    (Nat.le_div_iff_mul_le (by decide)).mpr (by
      have hh := C.twice_colour_edgesWithin_le i S
      omega)
  have hSum := sum_le_sum (s := (univ : Finset (Fin d))) (fun i _ => hBound i)
  rw [C.sum_edgesWithin] at hSum
  have hh : M.edgesWithin S ≤ d*(S.card/2) := by simpa using hSum
  exact (not_lt_of_ge hh) hS

set_option maxHeartbeats 2000000 in
/-- CMS Theorem 4.2 in terms of the three local degree and bundle
profiles. A fixed slack separates the heavy and non-heavy regimes. -/
theorem cms_theorem_4_2 (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ α/64 ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ζ : ℝ, 0 < ζ ∧ ∀ η : ℝ, 0 < η → η ≤ ζ → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (M : MultiGraph V) (a b : V) (d m E₀ : ℕ),
          N ≤ Fintype.card V → Fintype.card V = 2*m → a ≠ b →
          M.IsRegularOfDegree d → α*(Fintype.card V:ℝ) ≤ (d:ℝ) → d ≤ 3*m →
          IsRealRobust M.supportGraph ν τ → (E₀:ℝ) ≤ η*(m:ℝ) →
          (∀ v, v ≠ a → M.mult s(a,v) ≤ M.mult s(a,b)+E₀) →
          (∀ v, v ≠ a → d ≤ M.supportGraph.degree v+M.mult s(a,v)+E₀) →
          (∀ v, v ≠ a → v ≠ b → (d:ℝ)/2-(E₀:ℝ) ≤ M.supportGraph.degree v) →
          (Nonempty (M.EdgeColoring d) ↔ ¬ M.HasOverfullSubset d) := by
  obtain ⟨τ₀,hτ₀,hHeavy⟩ := HeavyPairPeeling.cms_heavy_pair_colourable.{u} α hα hα₁
  let τ := min τ₀ (min (1/16) (α/64))
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτ₀' : τ ≤ τ₀ := min_le_left _ _
  have hτ₁ : τ ≤ 1/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₂ : τ ≤ α/64 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨τ,hτ,hτ₂,?_⟩
  intro ν hν hντ
  obtain ⟨ζ₁,hζ₁,hCaseOne⟩ := hHeavy ν hν (hντ.trans hτ₀')
  let κ := min ν α/32
  have hκ : 0 < κ := div_pos (lt_min hν hα) (by norm_num)
  obtain ⟨ζ₂,hζ₂,hCaseTwo⟩ := cms_theorem_4_2_case_two.{u}
    ν τ α κ hν hντ hτ₁ hτ₂ hα hκ
  let ζ := min (12*ζ₁) ζ₂
  refine ⟨ζ,by dsimp only [ζ]; positivity,?_⟩
  intro η hη hηζ
  have hη₁ : η/12 ≤ ζ₁ := by
    have hh := hηζ.trans (show ζ ≤ 12*ζ₁ from min_le_left _ _)
    linarith only [hh]
  obtain ⟨N₁,hN₁⟩ := hCaseOne (η/12) hη₁
  obtain ⟨N₂,hN₂⟩ := hCaseTwo η hη (hηζ.trans (min_le_right _ _))
  refine ⟨max N₁ N₂,?_⟩
  intro V _ _ M a b d m E₀ hN hOrder hab hReg hDensity hD hRob hError hBundle hProfile hSupport
  refine ⟨fun ⟨C⟩ => no_overfull_of_edgeColoring M d C,?_⟩
  intro hNo
  have hOrderR : (Fintype.card V:ℝ) = 2*(m:ℝ) := by exact_mod_cast hOrder
  have hDens : 2*α*(m:ℝ) ≤ (d:ℝ) := by
    rw [hOrderR] at hDensity
    nlinarith only [hDensity]
  by_cases hGap : (M.mult s(a,b):ℝ)+κ*(m:ℝ) ≤ (d:ℝ)
  · obtain ⟨C,_⟩ := hN₂ M a b d m E₀ ((le_max_right _ _).trans hN) hOrder hab
      hReg hDens hD hRob hNo hError hGap hBundle hProfile hSupport
    exact ⟨C⟩
  · have hEven : Even (Fintype.card V) := ⟨m,by omega⟩
    have hRob' : IsRealRobust M.supportGraph ν τ₀ := by
      intro S hlo hhi
      have hc := mul_le_mul_of_nonneg_right hτ₀' (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
      exact hRob S (hc.trans hlo) (by nlinarith only [hc,hhi])
    have hMult := M.mult_pair_le_degree a b
    rw [hReg a] at hMult
    have hDeficit : ((d-M.mult s(a,b):ℕ):ℝ) ≤ κ*(Fintype.card V:ℝ) := by
      rw [Nat.cast_sub hMult,hOrderR]
      have hm := mul_nonneg hκ.le (Nat.cast_nonneg (α := ℝ) m)
      nlinarith only [hGap,hm]
    apply hN₁ M d a b hab ((le_max_left _ _).trans hN) hEven hReg hNo hDensity hRob' hDeficit
    · intro x
      have hx := (mem_outside a b x.val).mp x.property
      have hh := hSupport x.val hx.1 hx.2
      rw [hOrderR]
      nlinarith only [hh,hError]
    · intro x
      have hx := (mem_outside a b x.val).mp x.property
      have hh : (d:ℝ) ≤ M.supportGraph.degree x.val+(M.mult s(a,x.val):ℝ)+(E₀:ℝ) := by
        exact_mod_cast hProfile x.val hx.1
      rw [hOrderR]
      nlinarith only [hh,hError]

end OverfullWork.CMSBalancedCut
