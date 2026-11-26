module

public import OverfullWork.ChenShanFractionalIncidence

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical BigOperators

universe uA uB uW

variable {A : Type uA} {B : Type uB} {W : Type uW} [Fintype A] [Fintype B] [Fintype W]
variable {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}

omit [Fintype A] [Fintype B] [Fintype W] in
theorem TripartiteEdgeWeights.Supported.sub {r s : TripartiteEdgeWeights A B W}
    (hr : r.Supported E L R) (hs : s.Supported E L R) : (r.sub s).Supported E L R := by
  exact ⟨fun a b h => by simp [TripartiteEdgeWeights.sub,hr.1 a b h,hs.1 a b h],
    fun a w h => by simp [TripartiteEdgeWeights.sub,hr.2.1 a w h,hs.2.1 a w h],
    fun b w h => by simp [TripartiteEdgeWeights.sub,hr.2.2 b w h,hs.2.2 b w h]⟩

theorem TripartiteEdgeWeights.Balanced.sub {r s : TripartiteEdgeWeights A B W}
    (hr : r.Balanced) (hs : s.Balanced) : (r.sub s).Balanced := by
  refine ⟨?_,?_,?_⟩
  · intro a
    simp only [TripartiteEdgeWeights.sub,sum_sub_distrib,hr.1 a,hs.1 a]
  · intro b
    simp only [TripartiteEdgeWeights.sub,sum_sub_distrib,hr.2.1 b,hs.2.1 b]
  · intro w
    simp only [TripartiteEdgeWeights.sub,sum_sub_distrib,hr.2.2 w,hs.2.2 w]

theorem triangleBoundary_supported {p : A → B → W → ℝ} (hp : TriangleSupported E L R p) :
    (triangleBoundary p).Supported E L R := by
  refine ⟨?_,?_,?_⟩
  · intro a b h
    simp [triangleBoundary,hp a b _ (fun he => h he.1)]
  · intro a w h
    change (∑ b, p a b w) = 0
    exact sum_eq_zero (fun b _ => hp a b w (fun he => h he.2.1))
  · intro b w h
    change (∑ a, p a b w) = 0
    exact sum_eq_zero (fun a _ => hp a b w (fun he => h he.2.2))

theorem triangleBoundary_balanced (p : A → B → W → ℝ) : (triangleBoundary p).Balanced := by
  exact ⟨fun _ => sum_comm,fun _ => sum_comm,fun _ => sum_comm⟩

theorem card_missing_conjunction_le {V : Type*} [Fintype V] (P Q : V → Prop) :
    #(univ.filter (fun v => ¬ (P v ∧ Q v))) ≤
      #(univ.filter (fun v => ¬ P v)) + #(univ.filter (fun v => ¬ Q v)) := by
  have h : univ.filter (fun v => ¬ (P v ∧ Q v)) =
      (univ.filter (fun v => ¬ P v)) ∪ (univ.filter (fun v => ¬ Q v)) := by
    ext v
    simp only [mem_filter,mem_univ,true_and,mem_union]
    tauto
  rw [h]
  exact card_union_le _ _

theorem abs_sum_le_card_mul {V : Type*} (S : Finset V) (f : V → ℝ) (d : ℝ)
    (h : ∀ v ∈ S, |f v| ≤ d) : |∑ v ∈ S, f v| ≤ (S.card : ℝ)*d := by
  exact (abs_sum_le_sum_abs _ _).trans (by simpa [nsmul_eq_mul] using sum_le_sum h)

theorem masked_sum_add_missing {V : Type*} [Fintype V] (Q : V → Prop)
    [DecidablePred Q] [(v : V) → Decidable (¬ Q v)] (f : V → ℝ) :
    (∑ v, if Q v then f v else 0) + (∑ v ∈ univ.filter (fun v => ¬ Q v), f v) = ∑ v, f v := by
  have h := sum_filter_add_sum_filter_not (univ : Finset V) Q f
  rwa [sum_filter Q f] at h

theorem DenseTripartite.color_count_bounds {m : ℕ} {η ε : ℝ}
    (h : DenseTripartite E L R m η ε) (hm : 0 < m) (hη : 0 < η)
    (hηhalf : η < 1/2) (hε : ε ≤ η) :
    (m : ℝ)/2 ≤ (Fintype.card W : ℝ) ∧ (Fintype.card W : ℝ) ≤ 2*m := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hA : 0 < Fintype.card A := by rw [h.sizeA]; exact hm
  let a : A := Classical.choice (Fintype.card_pos_iff.mp hA)
  have hCount : #(univ.filter (E a)) = #(univ.filter (L a)) := by
    simpa only [Fintype.card_subtype] using h.balanced.1 a
  have hDeg := h.degreeA a
  have hTot := card_filter_add_card_filter_not (s := (univ : Finset W)) (L a)
  rw [card_univ] at hTot
  have hTot' : (#(univ.filter (L a)) : ℝ) + (#(univ.filter (fun w => ¬ L a w)) : ℝ) =
      (Fintype.card W : ℝ) := by exact_mod_cast hTot
  have hUpper : (#(univ.filter (L a)) : ℝ) ≤ m := by
    rw [← hCount,← h.sizeB]
    exact_mod_cast (card_filter_le (univ : Finset B) (E a)).trans_eq card_univ
  have hColor : (#(univ.filter (L a)) : ℝ) ≤ (Fintype.card W : ℝ) := by
    exact_mod_cast (card_filter_le (univ : Finset W) (L a)).trans_eq card_univ
  have hMiss := h.missingAW a
  have hεm := mul_le_mul_of_nonneg_right (show ε ≤ 1 by linarith) hm'.le
  have hηm := mul_nonneg hη.le hm'.le
  rw [hCount] at hDeg
  constructor <;> linarith

omit [Fintype A] [Fintype B] [Fintype W] in
private theorem abs_missing_div_sum_le {V : Type*} (S : Finset V) (f : V → ℝ)
    {D m k ε : ℝ} (hD : 0 ≤ D) (hε : 0 ≤ ε) (hk : 0 < k)
    (hkm : m/2 ≤ k) (hS : (S.card : ℝ) ≤ 2*ε*m) (hf : ∀ v, |f v| ≤ D) :
    |∑ v ∈ S, f v/k| ≤ 4*ε*D := by
  rw [← sum_div,abs_div,abs_of_pos hk]
  apply (div_le_div_of_nonneg_right (abs_sum_le_card_mul S f D (fun v _ => hf v)) hk.le).trans
  apply (div_le_iff₀ hk).mpr
  have hCount := mul_le_mul_of_nonneg_right hS hD
  have hK := mul_le_mul_of_nonneg_left hkm (show 0 ≤ 4*ε*D by positivity)
  linarith

/-- One round of (4.12)–(4.14). The cost of the triangle correction and
the contraction of the edge residual use the paper's constants. -/
theorem exists_signed_triangle_correction {m : ℕ} {η ε : ℝ}
    (h : DenseTripartite E L R m η ε) (hm : 0 < m)
    (hη : 0 < η) (hηhalf : η < 1/2) (hε0 : 0 ≤ ε) (hε : ε ≤ η)
    (r : TripartiteEdgeWeights A B W) (d : ℝ) (hd : 0 ≤ d)
    (hr : r.Supported E L R) (hbal : r.Balanced) (hbd : r.Bounded d) :
    ∃ t : A → B → W → ℝ, TriangleSupported E L R t ∧
      (∀ a b w, |t a b w| ≤ (2+10/η)*d/m) ∧
      (r.sub (triangleBoundary t)).Bounded (4*ε*(1+4/η)*d) := by
  let k := (Fintype.card W : ℝ)
  let D := (1+4/η)*d
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hK := h.color_count_bounds hm hη hηhalf hε
  have hKm : (m : ℝ)/2 ≤ k := hK.1
  have hk : 0 < k := by linarith
  obtain ⟨p,hP,hPR,hPC,hPB⟩ := exists_signed_incidence_correction h hm hη hε r d hd hr hbal hbd
  let u (a : A) (b : B) := r.ab a b - ∑ w, p a b w
  have hUzero (a : A) (b : B) (he : ¬ E a b) : u a b = 0 := by
    have hz (w : W) : p a b w = 0 := hP a b w (fun h => he h.1)
    simp [u,hr.1 a b he,hz]
  have hUR (a : A) : (∑ b, u a b) = 0 := by
    dsimp only [u]
    rw [sum_sub_distrib,hbal.1 a,sum_comm (s := (univ : Finset B))]
    simp only [hPR,sub_self]
  have hUC (b : B) : (∑ a, u a b) = 0 := by
    dsimp only [u]
    rw [sum_sub_distrib,hbal.2.1 b,sum_comm (s := (univ : Finset A))]
    simp only [hPC,sub_self]
  have hUbound (a : A) (b : B) : |u a b| ≤ D := by
    have hSum := abs_sum_le_card_mul (univ : Finset W) (p a b) (2*d/(η*m)) (fun w _ => hPB a b w)
    rw [card_univ] at hSum
    have hScale : k*(2*d/(η*m)) ≤ 4*d/η := by
      calc
        _ ≤ (2*(m : ℝ))*(2*d/(η*m)) := mul_le_mul_of_nonneg_right hK.2 (by positivity)
        _ = _ := by field_simp; ring
    dsimp only [u,D]
    calc
      _ ≤ |r.ab a b| + |∑ w, p a b w| := abs_sub _ _
      _ ≤ d+4*d/η := add_le_add (hbd.1 a b) (hSum.trans hScale)
      _ = _ := by ring
  let q (a : A) (b : B) (w : W) := if L a w ∧ R b w then u a b/k else 0
  let t (a : A) (b : B) (w : W) := p a b w + q a b w
  have hT : TriangleSupported E L R t := by
    intro a b w hmiss
    rw [show t a b w = p a b w + q a b w from rfl,hP a b w hmiss,zero_add]
    by_cases hLR : L a w ∧ R b w
    · have hE : ¬ E a b := fun he => hmiss ⟨he,hLR.1,hLR.2⟩
      simp [q,hLR,hUzero a b hE]
    · simp [q,hLR]
  refine ⟨t,hT,?_,?_,?_,?_⟩
  · intro a b w
    have hq : |q a b w| ≤ D/k := by
      by_cases hLR : L a w ∧ R b w
      · simp only [q,ite_eq_left hLR,abs_div,abs_of_pos hk]
        exact div_le_div_of_nonneg_right (hUbound a b) hk.le
      · simpa [q,hLR] using (show 0 ≤ D/k by positivity)
    have hQscale : D/k ≤ 2*D/m := by
      rw [div_le_div_iff₀ hk hm']
      have hMul := mul_le_mul_of_nonneg_left hKm hD
      linarith
    calc
      _ ≤ |p a b w| + |q a b w| := abs_add_le _ _
      _ ≤ 2*d/(η*m) + 2*D/m := add_le_add (hPB a b w) (hq.trans hQscale)
      _ = _ := by dsimp [D]; field_simp; ring
  · intro a b
    let Q (w : W) := L a w ∧ R b w
    have hMiss : (#(univ.filter (fun w => ¬ Q w)) : ℝ) ≤ 2*ε*m := by
      have hc : (#(univ.filter (fun w => ¬ Q w)) : ℝ) ≤
          (#(univ.filter (fun w => ¬ L a w)) : ℝ) + (#(univ.filter (fun w => ¬ R b w)) : ℝ) := by
        exact_mod_cast card_missing_conjunction_le (L a) (R b)
      linarith [h.missingAW a,h.missingBW b]
    have hAll : (∑ w : W, u a b/k) = u a b := by simp [k,nsmul_eq_mul,mul_div_cancel₀,ne_of_gt hk]
    have hs := masked_sum_add_missing Q (fun _ => u a b/k)
    rw [hAll] at hs
    have hMask : (∑ w, q a b w) = ∑ w, if Q w then u a b/k else 0 := by
      apply sum_congr rfl
      intro w _
      by_cases hw : Q w
      · have hw' : L a w ∧ R b w := hw
        simp only [q,ite_eq_left hw,ite_eq_left hw']
      · have hw' : ¬ (L a w ∧ R b w) := hw
        simp only [q,ite_eq_right hw,ite_eq_right hw']
    have hEq : u a b - (∑ w, q a b w) =
        ∑ w ∈ univ.filter (fun w => ¬ Q w), u a b/k := by
      rw [hMask]
      exact sub_eq_iff_eq_add.mpr (hs.symm.trans (add_comm _ _))
    change |r.ab a b - (∑ w, t a b w)| ≤ _
    simp only [t,sum_add_distrib,← sub_sub]
    change |u a b - ∑ w, q a b w| ≤ _
    rw [hEq]
    simpa only [D,mul_assoc] using abs_missing_div_sum_le _ _ hD hε0 hk hKm hMiss (fun _ => hUbound a b)
  · intro a w
    by_cases ha : L a w
    · have hs := masked_sum_add_missing (fun b => R b w) (fun b => u a b/k)
      have hZero : (∑ b, u a b/k) = 0 := by rw [← sum_div,hUR,zero_div]
      rw [hZero] at hs
      change |r.aw a w - (∑ b, t a b w)| ≤ _
      simp only [t,sum_add_distrib,hPR,q,ha,true_and]
      have heq : r.aw a w - (r.aw a w + ∑ b, if R b w then u a b/k else 0) =
          ∑ b ∈ univ.filter (fun b => ¬ R b w), u a b/k := by linarith
      rw [heq]
      have hMiss : (#(univ.filter (fun b => ¬ R b w)) : ℝ) ≤ 2*ε*m :=
        (h.missingWB w).trans (by nlinarith)
      simpa only [D,mul_assoc] using abs_missing_div_sum_le _ _ hD hε0 hk hKm hMiss (hUbound a)
    · simp only [TripartiteEdgeWeights.sub,hr.2.1 a w ha,(triangleBoundary_supported hT).2.1 a w ha,
        sub_self,abs_zero]
      positivity
  · intro b w
    by_cases hb : R b w
    · have hs := masked_sum_add_missing (fun a => L a w) (fun a => u a b/k)
      have hZero : (∑ a, u a b/k) = 0 := by rw [← sum_div,hUC,zero_div]
      rw [hZero] at hs
      change |r.bw b w - (∑ a, t a b w)| ≤ _
      simp only [t,sum_add_distrib,hPC,q,hb,and_true]
      have heq : r.bw b w - (r.bw b w + ∑ a, if L a w then u a b/k else 0) =
          ∑ a ∈ univ.filter (fun a => ¬ L a w), u a b/k := by linarith
      rw [heq]
      have hMiss : (#(univ.filter (fun a => ¬ L a w)) : ℝ) ≤ 2*ε*m :=
        (h.missingWA w).trans (by nlinarith)
      simpa only [D,mul_assoc] using abs_missing_div_sum_le _ _ hD hε0 hk hKm hMiss (fun a => hUbound a b)
    · simp only [TripartiteEdgeWeights.sub,hr.2.2 b w hb,(triangleBoundary_supported hT).2.2 b w hb,
        sub_self,abs_zero]
      positivity

end OverfullWork.ChenShan
