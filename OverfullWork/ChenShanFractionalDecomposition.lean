module

public import OverfullWork.ChenShanFractionalInitial
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Filter
open scoped Classical BigOperators Topology

private theorem tsum_corrects_margin {I : Type*} [Fintype I] (g : ℕ → ℝ) (p : I → ℕ → ℝ)
    {D : ℝ} (hSumm : ∀ i, Summable (p i)) (hBound : ∀ n, |g n| ≤ D*(1/2 : ℝ)^n)
    (hStep : ∀ n, g (n+1) = g n - ∑ i, p i n) :
    (∑ i, ∑' n, p i n) = g 0 := by
  have hHalf : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hDHalf : Tendsto (fun n : ℕ => D*(1/2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hHalf
  have hg : Tendsto g atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hBound n) hDHalf
  have hTel (n : ℕ) : (∑ j ∈ range n, ∑ i, p i j) = g 0 - g n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ,ih,hStep n]
      ring
  have hSeries : HasSum (fun n => ∑ i, p i n) (∑ i, ∑' n, p i n) :=
    hasSum_sum (fun i _ => (hSumm i).hasSum)
  have hLim : Tendsto (fun n => ∑ j ∈ range n, ∑ i, p i j) atTop (𝓝 (g 0)) := by
    have hConst : Tendsto (fun _ : ℕ => g 0) atTop (𝓝 (g 0)) := tendsto_const_nhds
    simpa only [sub_zero] using (hConst.sub hg).congr (fun n => (hTel n).symm)
  exact tendsto_nhds_unique hSeries.tendsto_sum_nat hLim

universe uA uB uW

variable {A : Type uA} {B : Type uB} {W : Type uW} [Fintype A] [Fintype B] [Fintype W]
variable {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}

/-- A fractional triangle decomposition with the two pointwise bounds
of (4.10). Functions are extended by zero on triples outside the graph. -/
def BoundedFractionalTriangleDecomposition (E : A → B → Prop)
    (L : A → W → Prop) (R : B → W → Prop) : Prop :=
  ∃ ω : A → B → W → ℝ, TriangleSupported E L R ω ∧
    triangleBoundary ω = edgeOnes E L R ∧
    ∀ a b w, E a b → L a w → R b w →
      1/(2*(Fintype.card W : ℝ)) ≤ ω a b w ∧ ω a b w ≤ 3/(2*(Fintype.card W : ℝ))

omit [Fintype A] [Fintype B] [Fintype W] in
private theorem edgeWeights_ext {r s : TripartiteEdgeWeights A B W}
    (hab : r.ab = s.ab) (haw : r.aw = s.aw) (hbw : r.bw = s.bw) : r = s := by
  cases r
  cases s
  cases hab
  cases haw
  cases hbw
  rfl

theorem bounded_fractional_triangle_decomposition_of_dense {m : ℕ} {η ε : ℝ}
    (h : DenseTripartite E L R m η ε) (hη : 0 < η) (hηhalf : η < 1/2)
    (hε₀ : 0 ≤ ε) (hε : ε ≤ min η (1/(32*(2+10/η)))) :
    BoundedFractionalTriangleDecomposition E L R := by
  by_cases hm : 0 < m
  swap
  · have hz : m = 0 := by omega
    let _ : IsEmpty A := Fintype.card_eq_zero_iff.mp (h.sizeA.trans hz)
    let _ : IsEmpty B := Fintype.card_eq_zero_iff.mp (h.sizeB.trans hz)
    refine ⟨fun _ _ _ => 0,fun _ _ _ _ => rfl,?_,fun a _ _ => isEmptyElim a⟩
    exact edgeWeights_ext (funext fun a => isEmptyElim a) (funext fun a => isEmptyElim a)
      (funext fun b => isEmptyElim b)
  let k := (Fintype.card W : ℝ)
  let κ : ℝ := 2+10/η
  let d (n : ℕ) := 4*ε*(1/2 : ℝ)^n
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hεη := hε.trans (min_le_left _ _)
  have hεsmall : ε ≤ 1/(32*κ) := hε.trans (min_le_right _ _)
  have hK := h.color_count_bounds hm hη hηhalf hεη
  have hk : 0 < k := by dsimp [k]; linarith [hK.1]
  have hBudget : ε*(32*κ) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 32*κ)).mp hεsmall
  have hFactor : 4*ε*(1+4/η) ≤ 1/2 := by
    have hc : 8*(1+4/η) ≤ 32*κ := by
      calc
        _ = 8+32*(1/η) := by ring
        _ ≤ 64+320*(1/η) := by linarith [show 0 ≤ 1/η by positivity]
        _ = _ := by dsimp only [κ]; ring
    have hMul := mul_le_mul_of_nonneg_left hc hε₀
    linarith
  have hd (n : ℕ) : 0 ≤ d n := by dsimp [d]; positivity
  have hShrink (n : ℕ) : 4*ε*(1+4/η)*d n ≤ d (n+1) := by
    have hp := mul_le_mul_of_nonneg_right hFactor (hd n)
    convert hp using 1
    dsimp only [d]
    rw [pow_succ]
    ring
  let Good (n : ℕ) := {r : TripartiteEdgeWeights A B W //
    r.Supported E L R ∧ r.Balanced ∧ r.Bounded (d n)}
  have hStep (n : ℕ) (r : Good n) :
      ∃ p : A → B → W → ℝ, TriangleSupported E L R p ∧
        (∀ a b w, |p a b w| ≤ κ*d n/m) ∧
        (r.val.sub (triangleBoundary p)).Bounded (d (n+1)) := by
    obtain ⟨p,hP,hBP,hR⟩ := exists_signed_triangle_correction h hm hη hηhalf hε₀ hεη
      r.val (d n) (hd n) r.property.1 r.property.2.1 r.property.2.2
    exact ⟨p,hP,hBP,fun a b => (hR.1 a b).trans (hShrink n),
      fun a w => (hR.2.1 a w).trans (hShrink n),fun b w => (hR.2.2 b w).trans (hShrink n)⟩
  choose p hp hpb hrb using hStep
  let one := edgeOnes E L R
  let w₀ := initialTriangleWeights E L R
  let seed : Good 0 := ⟨one.sub (triangleBoundary w₀),
    edgeOnes_supported.sub (triangleBoundary_supported initialTriangleWeights_supported),
    (edgeOnes_balanced h.balanced).sub (triangleBoundary_balanced w₀),
    by simpa only [d,pow_zero,mul_one] using initial_triangle_residual_bounded h hm hη hηhalf hε₀ hεη⟩
  let r (n : ℕ) : Good n :=
    Nat.rec seed (fun n x => ⟨x.val.sub (triangleBoundary (p n x)),
      x.property.1.sub (triangleBoundary_supported (hp n x)),
      x.property.2.1.sub (triangleBoundary_balanced (p n x)),hrb n x⟩) n
  let c (n : ℕ) := p n (r n)
  let u (a : A) (b : B) (w : W) := ∑' n, c n a b w
  let ω (a : A) (b : B) (w : W) := w₀ a b w + u a b w
  let C : ℝ := κ*(4*ε)/m
  have hBound (n : ℕ) (a : A) (b : B) (w : W) :
      |c n a b w| ≤ C*(1/2 : ℝ)^n := by
    have h' := hpb n (r n) a b w
    convert h' using 1
    dsimp only [C,d]
    ring
  have hGeo : Summable (fun n : ℕ => C*(1/2 : ℝ)^n) :=
    (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num)).mul_left C
  have hSumm (a : A) (b : B) (w : W) : Summable (fun n => c n a b w) :=
    hGeo.of_norm_bounded (fun n => by simpa only [Real.norm_eq_abs] using hBound n a b w)
  have hSupport : TriangleSupported E L R ω := by
    intro a b w he
    have hc (n : ℕ) : c n a b w = 0 := hp n (r n) a b w he
    have hW₀ := initialTriangleWeights_supported a b w he
    change w₀ a b w = 0 at hW₀
    simp [ω,u,hW₀,hc]
  have hAB (a : A) (b : B) : (∑ w, u a b w) = (seed.val).ab a b :=
    tsum_corrects_margin (fun n => (r n).val.ab a b) (fun w n => c n a b w)
      (fun w => hSumm a b w) (fun n => (r n).property.2.2.1 a b) (fun _ => rfl)
  have hAW (a : A) (w : W) : (∑ b, u a b w) = (seed.val).aw a w :=
    tsum_corrects_margin (fun n => (r n).val.aw a w) (fun b n => c n a b w)
      (fun b => hSumm a b w) (fun n => (r n).property.2.2.2.1 a w) (fun _ => rfl)
  have hBW (b : B) (w : W) : (∑ a, u a b w) = (seed.val).bw b w :=
    tsum_corrects_margin (fun n => (r n).val.bw b w) (fun a n => c n a b w)
      (fun a => hSumm a b w) (fun n => (r n).property.2.2.2.2 b w) (fun _ => rfl)
  refine ⟨ω,hSupport,?_,?_⟩
  · apply edgeWeights_ext <;> funext a b
    · simp only [triangleBoundary,ω,sum_add_distrib,hAB,seed,TripartiteEdgeWeights.sub]
      ring
    · simp only [triangleBoundary,ω,sum_add_distrib,hAW,seed,TripartiteEdgeWeights.sub]
      ring
    · simp only [triangleBoundary,ω,sum_add_distrib,hBW,seed,TripartiteEdgeWeights.sub]
      ring
  · intro a b w he hl hr
    have hT : |u a b w| ≤ 2*C := by
      calc
        _ ≤ ∑' n, |c n a b w| := by
          simpa only [u,Real.norm_eq_abs] using
            (norm_tsum_le_tsum_norm (f := fun n : ℕ => c n a b w)
              (by simpa only [Real.norm_eq_abs] using (hSumm a b w).abs))
        _ ≤ ∑' n : ℕ, C*(1/2 : ℝ)^n := Summable.tsum_le_tsum (fun n => hBound n a b w)
          (hSumm a b w).abs hGeo
        _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
    have hScale : 2*C ≤ 1/(2*k) := by
      calc
        _ ≤ (1 : ℝ)/(4*m) := by
          dsimp only [C]
          have ht : κ*(4*ε) ≤ (1/8 : ℝ) := by linarith
          have hf := div_le_div_of_nonneg_right ht hm'.le
          calc
            _ ≤ 2*((1/8 : ℝ)/m) := mul_le_mul_of_nonneg_left hf (by norm_num)
            _ = _ := by ring
        _ ≤ _ := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          have hK₂ : k ≤ 2*m := hK.2
          linarith
    have hU := abs_le.mp (hT.trans hScale)
    have hω : ω a b w = 1/k + u a b w := by simp [ω,w₀,initialTriangleWeights,he,hl,hr,k]
    have hTwo : 1/k = 2*(1/(2*k)) := by ring
    rw [hω,hTwo]
    have hThree : 3/(2*k) = 3*(1/(2*k)) := by ring
    change 1/(2*k) ≤ _ ∧ _ ≤ 3/(2*k)
    rw [hThree]
    constructor <;> linarith

/-- Chen–Shan, Lemma 4.8. One may take
ε₀ = min {η, 1/(32(2+10/η))}. -/
theorem exists_bounded_fractional_triangle_decomposition (η : ℝ)
    (hη : 0 < η) (hηhalf : η < 1/2) :
    ∃ ε₀ > 0, ∀ (m : ℕ) (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      DenseTripartite E L R m η ε → BoundedFractionalTriangleDecomposition E L R := by
  refine ⟨min η (1/(32*(2+10/η))),lt_min hη (by positivity),?_⟩
  intro m ε hε₀ hε h
  exact bounded_fractional_triangle_decomposition_of_dense h hη hηhalf hε₀ hε

end OverfullWork.ChenShan
