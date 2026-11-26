module

public import OverfullWork.ChenShanNestedAbsorber
public import OverfullWork.ChenShanNestedImbalance
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

/-- Step 1 of Theorem 4.15. The final prefix admits a common absorber,
while the degree estimates at all retained levels refer to the original graph. -/
theorem exists_nested_prefixes_and_absorber (η ρ μ ξ : ℝ)
    (hη : 0 < η) (hηhalf : η < 1/2)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ min η (1/2)/128)
    (hμ : 0 < μ) (hξ : 0 < ξ) (hξ₁ : ξ ≤ 1) (hmin : ℕ) :
    ∃ (h : ℕ) (ε₀ : ℝ) (m₀ : ℕ), hmin ≤ h ∧ 4 ≤ h ∧ 0 < ε₀ ∧ h ≤ m₀ ∧
    ∀ (m : ℕ), m₀ ≤ m → ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
    ∀ (A : Type*) (B : Type*) (W : Type*) [Fintype A] [Fintype B] [Fintype W]
      (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop),
    DenseTripartite E L R m η ε →
    ∃ l : ℕ, (∀ i ≤ l, h ≤ nestedCoreSize ρ m i) ∧
      nestedCoreSize ρ m (l+1) < h ∧ (nestedCoreSize ρ m l : ℝ) < h/ρ ∧
    ∃ S : NestedTripartitePrefixes A B W ρ m (Fintype.card W) l,
      TripartitePrefixDegreeControl E L R S ξ ∧
      (∀ i ≤ l, ∀ v : ↥(S.left i) ⊕ ↥(S.right i) ⊕ ↥(S.colors i),
        |(arcDivergence
          (tripartiteArcs (fun a b => E a.1 b.1) (fun a w => L a.1 w.1)
            (fun b w => R b.1 w.1)) v : ℝ)| ≤ 2*ξ*nestedCoreSize ρ m i+1/2) ∧
    ∃ (P : A → B → Prop) (Q : A → W → Prop) (T : B → W → Prop),
      tripartiteArcs P Q T ⊆ tripartiteArcs E L R ∧
      Disjoint (tripartiteArcs P Q T) (S.vertices 1 ×ˢ S.vertices 1) ∧
      (∀ v, (incidentDegree (tripartiteArcs P Q T) v : ℝ) ≤ μ*m) ∧
      Nonempty (TripartiteTriangleDecomposition P Q T) ∧
      ∀ (EL : A → B → Prop) (LL : A → W → Prop) (RL : B → W → Prop),
        tripartiteArcs EL LL RL ⊆ tripartiteArcs E L R →
        tripartiteArcs EL LL RL ⊆ S.vertices l ×ˢ S.vertices l →
        TripartiteLocallyBalanced EL LL RL →
        Nonempty (TripartiteTriangleDecomposition
          (fun a b => P a b ∨ EL a b) (fun a w => Q a w ∨ LL a w)
          (fun b w => T b w ∨ RL b w)) := by
  let gap := min η (1/2)
  have hGap : 0 < gap := lt_min hη (by norm_num)
  have hρhalf : ρ ≤ 1/2 := by
    have hGapHalf : gap ≤ 1/2 := min_le_right _ _
    linarith only [hGapHalf,hρsmall]
  obtain ⟨h,hMin,hFour,hSampling⟩ :=
    exists_tripartite_prefix_degree_control ρ ξ hρ hρhalf hξ hξ₁ hmin
  let H := ⌈4*(h : ℝ)/ρ⌉₊
  have hH : 4*(h : ℝ)/ρ ≤ H := Nat.le_ceil _
  have hh : (0:ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hHr : (0:ℝ) < H := (show 0 < 4*(h:ℝ)/ρ by positivity).trans_le hH
  let bound : ℕ := 4*(H*H)*2^(H*H)
  let ε₀ := min (η/32) (1/(32*(H:ℝ)))
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by positivity)
  let scale := max (max ((h:ℝ)/ρ) (128/gap)) (max (16*(bound:ℝ)/gap) ((bound:ℝ)/μ))
  let m₀ := max h ⌈scale⌉₊
  refine ⟨h,ε₀,m₀,hMin,hFour,hε₀,le_max_left _ _,?_⟩
  intro m hm₀ ε hε hε₁ A B W _ _ _ E L R G
  have hm : h ≤ m := (le_max_left h _).trans hm₀
  have hmPos : 0 < m := by omega
  have hεsmall : ε ≤ η/32 := hε₁.trans (min_le_left _ _)
  have hεη : ε ≤ η := by linarith only [hεsmall,hη]
  have hCycles : (H:ℝ)*ε ≤ 1/32 := by
    have hSmall := (le_div_iff₀ (show 0 < 32*(H:ℝ) by positivity)).mp
      (hε₁.trans (min_le_right (η/32) _))
    linarith only [hSmall]
  have hScale : scale ≤ m := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right h ⌈scale⌉₊).trans hm₀)
  have hCore : (h:ℝ)/ρ ≤ m := ((le_max_left _ _).trans (le_max_left _ _)).trans hScale
  have hLarge : 128/gap ≤ m := ((le_max_right _ _).trans (le_max_left _ _)).trans hScale
  have hRoom' : 16*(bound:ℝ)/gap ≤ m :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hScale
  have hRoom : (bound:ℝ) ≤ gap*m/16 := by
    have hx := (div_le_iff₀ hGap).mp hRoom'
    linarith only [hx]
  have hBudget' : (bound:ℝ)/μ ≤ m :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hScale
  have hBudget : (bound:ℝ) ≤ μ*m := by
    simpa only [mul_comm] using (div_le_iff₀ hμ).mp hBudget'
  obtain ⟨hk₀,hk₁⟩ := G.color_count_bounds hmPos hη hηhalf hεη
  have hk : 0 < Fintype.card W := by
    have hmR : (0:ℝ) < m := by exact_mod_cast hmPos
    have hkR : (0:ℝ) < Fintype.card W := by linarith only [hk₀,hmR]
    exact_mod_cast hkR
  obtain ⟨l,hKeep,hExit,hTop,S,hSample⟩ :=
    hSampling m (Fintype.card W) hm hk₀ hk₁ A B W G.sizeA G.sizeB rfl E L R
  refine ⟨l,hKeep,hExit,hTop,S,hSample,?_,?_⟩
  · exact nested_prefix_imbalance E L R S ξ hmPos hk G.sizeA G.sizeB rfl G.balanced hSample
  · exact exists_absorber_for_nested_prefixes G S hρ hρsmall hη hηhalf hε hεsmall
      hCycles hmPos hCore hLarge hH rfl hKeep (by omega) hExit hTop hRoom hBudget

end OverfullWork.ChenShan
