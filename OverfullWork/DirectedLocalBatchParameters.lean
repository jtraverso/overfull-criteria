module

public import OverfullWork.DirectedSampledBatchConstruction

@[expose] public section


/-! Uniform choices for a small batch. This is the parameter substitution
into GGKLO 7.3(i); the outer stages use fresh choices of the block order. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion
open scoped Classical
universe u v w

private theorem rounded_load_le (l : ℝ) (n : ℕ) (_hl : 0 < l)
    (hN : 2 ≤ l*(n:ℝ)) :
    0 < ⌈(l/2)*(n:ℝ)⌉₊ ∧ (⌈(l/2)*(n:ℝ)⌉₊:ℝ) ≤ l*(n:ℝ) := by
  have hn : 0 < (l/2)*(n:ℝ) := by linarith only [hN]
  exact ⟨Nat.ceil_pos.mpr hn,(Nat.ceil_lt_add_one hn.le).le.trans (by linarith only [hN])⟩

private theorem cyclic_charge (m k : ℕ) (hk : 0 < k) :
    (((m+k-1)/k:ℕ):ℝ) ≤ (m:ℝ)/(k:ℝ)+1 := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have h : (((m+k-1)/k:ℕ):ℝ)*(k:ℝ) ≤ (m:ℝ)+(k:ℝ) := by
    exact_mod_cast (Nat.div_mul_le_self (m+k-1) k).trans (Nat.sub_le _ _)
  have hc := (le_div_iff₀ hk').mpr h
  rwa [add_div,div_self hk'.ne'] at hc

/-- For any fixed number of reserve blocks, sufficiently small layouts
and a sufficiently small batch admit a packing. The order threshold and
the width of the semidegree interval are uniform in the dense center.
The exact cyclic charge is retained for the next stage. -/
theorem exists_small_batch_parameters (ν τ α d₀ σ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/8)
    (hα : α ≤ 1) (hτα : 256*(8*τ) ≤ α)
    (hd₀ : 0 < d₀) (hσ : 0 < σ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, ∃ h N : ℕ, 5 ≤ h ∧
      let l := κ/((k+2:ℕ):ℝ)
      ∀ (δ γ e : ℝ), d₀ ≤ δ → δ ≤ 1 → α+σ ≤ γ → γ ≤ 1 → 0 < e → e ≤ l →
      ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I] {J : Type w} [Fintype J]
        (D Γ : Digraph V) (L : J → Layout V I) (long : J → I),
        let n := Fintype.card V
        let m := Fintype.card J
        let b := ⌈(e/2)*(n:ℝ)⌉₊
        N ≤ n → 2 ≤ e*(n:ℝ) → Disjoint D Γ → IsRealRobust Γ ν τ →
        SemidegreesAround D (δ*(n:ℝ)) (l*(n:ℝ)) →
        SemidegreesAround Γ (γ*(n:ℝ)) (l*(n:ℝ)) →
        (m:ℝ) ≤ l*(n:ℝ) →
        (∀ i, (L i).boundary.card ≤ b ∧ long i ∉ (L i).fixed ∧
          (univ \ insert (long i) (L i).fixed).card*h ≤ b) →
        (∀ v, (∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v)) ≤ b) →
        ∃ P : PackingPrefix (D ⊔ Γ) L (univ : Finset J),
          ∀ v, inDegree (P.used ⊓ Γ) v+outDegree (P.used ⊓ Γ) v ≤
            3*b+2*((m+(k+2)-1)/(k+2)) := by
  let μ : ℝ := ν^6/(2:ℝ)^60/4
  let R : ℝ := (μ/4)^3
  let p : ℝ := min (R/8) (d₀/32)
  let t : ℝ := min 1 (min (d₀/8) (p*d₀/52))
  let w : ℝ := min t (min μ (min σ (min 1 (min τ d₀))))
  let κ : ℝ := w/200
  have hτp := hν.trans_le hντ
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hp : 0 < p := lt_min (by positivity) (by positivity)
  have ht : 0 < t := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hw : 0 < w := lt_min ht (lt_min hμ (lt_min hσ (lt_min (by norm_num) (lt_min hτp hd₀))))
  have hκ : 0 < κ := div_pos hw (by norm_num)
  refine ⟨κ,hκ,?_⟩
  intro k
  let K := k+2
  let c : ℝ := 1/(2*(K:ℝ))
  let ρ := c*p
  let η := c*t
  let l := κ/(K:ℝ)
  have hK : 0 < K := by dsimp [K]; omega
  have hKR : (2:ℝ) ≤ K := by exact_mod_cast (show 2 ≤ K by dsimp [K]; omega)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcB : c ≤ 1/4 := by
    apply (div_le_iff₀ (show 0 < 2*(K:ℝ) by positivity)).mpr
    linarith only [hKR]
  have hc₁ : c ≤ 1 := by linarith only [hcB]
  have hρ : 0 < ρ := mul_pos hc hp
  have hρR : ρ ≤ R*c/8 := by
    have h := mul_le_mul_of_nonneg_left (min_le_left (R/8) (d₀/32)) hc.le
    dsimp only [ρ,p]
    linarith only [h]
  have hρd : ρ ≤ d₀*c/32 := by
    have h := mul_le_mul_of_nonneg_left (min_le_right (R/8) (d₀/32)) hc.le
    dsimp only [ρ,p]
    linarith only [h]
  have hη : 0 < η := mul_pos hc ht
  have ht₁ : t ≤ 1 := min_le_left _ _
  have hη₁ : η ≤ 1 := (mul_le_mul_of_nonneg_left ht₁ hc.le).trans (by simpa using hc₁)
  have hGap : 8*η ≤ d₀ := by
    have h : t ≤ d₀/8 := (min_le_right _ _).trans (min_le_left _ _)
    have h' := mul_le_mul_of_nonneg_left h hc.le
    have h'' := mul_le_mul_of_nonneg_right hc₁ hd₀.le
    dsimp only [η]
    linarith only [h',h'']
  have hScale : 52*η ≤ ρ*d₀ := by
    have h : t ≤ p*d₀/52 := (min_le_right _ _).trans (min_le_right _ _)
    have h' := mul_le_mul_of_nonneg_left h hc.le
    dsimp only [ρ,η]
    linarith only [h']
  have hl : 0 < l := div_pos hκ (by positivity)
  have hCommon : 100*l = c*w := by dsimp [l,κ,c]; ring
  have pay (x : ℝ) (h : w ≤ x) : 100*l ≤ c*x :=
    hCommon.le.trans (mul_le_mul_of_nonneg_left h hc.le)
  have hlη : 100*l ≤ η := pay t (min_le_left _ _)
  have hlμ : 100*l ≤ μ*c := by
    rw [mul_comm μ c]
    exact pay μ ((min_le_right _ _).trans (min_le_left _ _))
  have hlσ : 100*l ≤ σ*c := by
    rw [mul_comm σ c]
    exact pay σ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hlc : 100*l ≤ c := by
    rw [← mul_one c]
    exact pay 1 ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hlτ : 100*l ≤ τ*c := by
    rw [mul_comm τ c]
    exact pay τ ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hld : 100*l ≤ d₀*c := by
    rw [mul_comm d₀ c]
    exact pay d₀ (min_le_right _ _ |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans (min_le_right _ _))
  obtain ⟨H,hH⟩ := exists_nat_ge (2/μ)
  let h := H+5
  have hh : 5 ≤ h := by omega
  have hRatio : 1 ≤ (μ/2)*((h-5:ℕ):ℝ) := by
    have he : h-5 = H := by omega
    rw [he]
    have hb := (div_le_iff₀ hμ).mp hH
    linarith only [hb]
  obtain ⟨N,N₀,N₁,hBatch⟩ := exists_batch_of_global_profiles.{u,v,w} ν τ α d₀ ρ η c (1/4) l
    hν hντ hτ hα hτα hd₀ hρ hη hGap hScale hc (by linarith only [hcB]) hcB hl
  obtain ⟨T,hT⟩ := exists_nat_ge (2/l)
  obtain ⟨T₀,hT₀⟩ := exists_nat_ge ((2*(N₀:ℝ))/c)
  obtain ⟨T₁,hT₁⟩ := exists_nat_ge (8*(N₁:ℝ))
  refine ⟨h,max (max N (4*K)) (max T (max T₀ T₁)),hh,?_⟩
  dsimp only
  intro δ γ e hδ hδ₁ hγ hγ₁ he hel V _ I _ J _ D Γ L long
  intro hn heN hDis hRob hD hΓ hm hLayout hEnd
  let n := Fintype.card V
  let m := Fintype.card J
  let b := ⌈(e/2)*(n:ℝ)⌉₊
  let a := (m+K-1)/K
  let g := b+2*b+2*a
  let d := m+b
  let M := c*(n:ℝ)-(b:ℝ)
  let B := (1/4:ℝ)*(n:ℝ)
  let E := l*(n:ℝ)+l*(n:ℝ)+3*(b:ℝ)
  have hLarge : N ≤ n ∧ 4*K ≤ n ∧ T ≤ n ∧ T₀ ≤ n ∧ T₁ ≤ n := by
    change max (max N (4*K)) (max T (max T₀ T₁)) ≤ n at hn
    simpa only [max_le_iff, and_assoc] using hn
  have hnpos : 0 < n := by have := hLarge.2.1; omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hnpos
  have hn₁ : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hL : 2 ≤ l*(n:ℝ) := by
    have hreal : (T:ℝ) ≤ n := by exact_mod_cast hLarge.2.2.1
    have hb := (div_le_iff₀ hl).mp (hT.trans hreal)
    linarith only [hb]
  have h0 : (N₀:ℝ) ≤ c*(n:ℝ)/2 := by
    have hreal : (T₀:ℝ) ≤ n := by exact_mod_cast hLarge.2.2.2.1
    have hb := (div_le_iff₀ hc).mp (hT₀.trans hreal)
    linarith only [hb]
  have h1 : (N₁:ℝ) ≤ (n:ℝ)/8 := by
    have hreal : (T₁:ℝ) ≤ n := by exact_mod_cast hLarge.2.2.2.2
    linarith only [hT₁,hreal]
  have hb₀ := rounded_load_le e n he heN
  have hb : 0 < b ∧ (b:ℝ) ≤ l*(n:ℝ) :=
    ⟨hb₀.1,hb₀.2.trans (mul_le_mul_of_nonneg_right hel hnR.le)⟩
  have hMB : c*(n:ℝ)/2 ≤ M := by
    have h := mul_le_mul_of_nonneg_right hlc hnR.le
    dsimp only [M]
    linarith only [h,hb.2]
  have hB : c*(n:ℝ) ≤ B := by dsimp [B]; nlinarith only [hcB,hnR]
  have hg : (g:ℝ) ≤ 6*l*(n:ℝ) := by
    have ha := cyclic_charge m K hK
    have hd : (m:ℝ)/(K:ℝ) ≤ (m:ℝ) := by
      apply (div_le_iff₀ (show 0 < (K:ℝ) by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left hKR (Nat.cast_nonneg (α := ℝ) m)
      nlinarith only [hh,Nat.cast_nonneg (α := ℝ) m]
    change (a:ℝ) ≤ (m:ℝ)/(K:ℝ)+1 at ha
    dsimp only [g]
    push_cast
    change (m:ℝ) ≤ l*(n:ℝ) at hm
    linarith only [ha,hd,hL,hm,hb.2]
  have hE : E ≤ 5*l*(n:ℝ) := by dsimp only [E]; linarith only [hb.2]
  have hd : (d:ℝ) ≤ 2*l*(n:ℝ) := by dsimp only [d]; push_cast; linarith only [hm,hb.2]
  have hμB := mul_le_mul_of_nonneg_left hB hμ.le
  have hμM := mul_le_mul_of_nonneg_left hMB hμ.le
  have hσM := mul_le_mul_of_nonneg_left hMB hσ.le
  have hσB := mul_le_mul_of_nonneg_left hB hσ.le
  have hδM := mul_le_mul_of_nonneg_left hMB (hd₀.trans_le hδ).le
  have hδc := mul_le_mul_of_nonneg_right hδ (mul_nonneg hc.le hnR.le)
  have hγM := mul_le_mul_of_nonneg_right (show σ ≤ γ-α by linarith only [hγ])
    (show 0 ≤ M from (by positivity : 0 ≤ c*(n:ℝ)/2).trans hMB)
  have hγB := mul_le_mul_of_nonneg_right (show σ ≤ γ-8*τ by linarith only [hγ,hτα,hτp])
    (show 0 ≤ B by positivity)
  have hScaleμ := mul_le_mul_of_nonneg_right hlμ hnR.le
  have hScaleσ := mul_le_mul_of_nonneg_right hlσ hnR.le
  have hScaleη := mul_le_mul_of_nonneg_right hlη hnR.le
  have hScalec := mul_le_mul_of_nonneg_right hlc hnR.le
  have hScaleτ := mul_le_mul_of_nonneg_right hlτ hnR.le
  have hScaled := mul_le_mul_of_nonneg_right hld hnR.le
  have hl₁ : l ≤ 1 := by linarith only [hlη,hη₁]
  obtain ⟨size,hSum,hSizes⟩ := AdjacentLayerPathCover.exists_balanced_reserve_sizes k n
    (by exact hLarge.2.1)
  have hParts (i : Fin (k+2)) :
      c*(n:ℝ) ≤ (size i:ℝ) ∧ (1/4:ℝ)*(n:ℝ) ≤ ((n-size i:ℕ):ℝ) := by
    simpa [c,K,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hSizes i
  have hSlots : 3*(k+2) < n^2 := by
    have h := hLarge.2.1
    change 4*(k+2) ≤ n at h
    nlinarith only [h,Nat.le_mul_self n]
  have hN₁ : ((N₁+b+b:ℕ):ℝ) ≤ (1/4:ℝ)*(n:ℝ) := by
    push_cast
    have h := mul_le_mul_of_nonneg_right hcB hnR.le
    linarith only [h1,h,hScalec,hb.2]
  have hρN : ρ*((n:ℝ)+1) ≤ 2*ρ*(n:ℝ) :=
    by nlinarith only [mul_le_mul_of_nonneg_left hn₁ hρ.le]
  have hCount : ρ*((n:ℝ)+1) ≤ R*M := by
    have ht := mul_le_mul_of_nonneg_left hMB hR.le
    have hrr := mul_le_mul_of_nonneg_right hρR hnR.le
    linarith only [hρN,ht,hrr,hR,hc,hnR,
      mul_nonneg hR.le (mul_nonneg hc.le hnR.le)]
  have hAttach : 2*ρ*((n:ℝ)+1)+(d:ℝ)+E ≤ δ*M := by
    have ht := mul_le_mul_of_nonneg_right hρd hnR.le
    have hNon := mul_nonneg hd₀.le (mul_nonneg hc.le hnR.le)
    linarith only [hρN,ht,hScaled,hδM,hδc,hd,hE,hNon]
  have hEta : η*(n:ℝ)/16 ≥ 5*l*(n:ℝ) := by
    linarith only [hScaleη,mul_nonneg hl.le hnR.le]
  have hSlack : (η+1)*((b+b:ℕ):ℝ)+1 ≤ (η/2)*B := by
    have hh := mul_le_mul_of_nonneg_right hη₁ (Nat.cast_nonneg (α := ℝ) (b+b))
    push_cast at hh ⊢
    dsimp only [B]
    linarith only [hh,hb.2,hL,hScaleη]
  have hShort : (((m+b+b+1:ℕ)):ℝ) ≤ (μ/2)*B := by
    push_cast
    have he : (μ/2)*B = μ*B/2 := by ring
    rw [he]
    linarith only [hScaleμ,hμB,hL,hm,hb.2]
  have hComp : E+((m+b+b+g+2:ℕ):ℝ) ≤ (γ-8*τ)*B := by
    push_cast
    linarith only [hScaleσ,hσB,hγB,hE,hg,hL,hm,hb.2]
  have hBase : E+(g:ℝ) ≤ (γ-α)*M := by
    linarith only [hScaleσ,hσM,hγM,hE,hg]
  have hTrimν : 8*(b:ℝ) ≤ (ν^6/(2:ℝ)^60)*(c*(n:ℝ)) := by
    rw [show ν^6/(2:ℝ)^60 = 4*μ by dsimp [μ]; ring]
    linarith only [hScaleμ,hb.2]
  have hTrimτ : 4*(b:ℝ) ≤ (4*τ)*(c*(n:ℝ)) := by
    linarith only [hScaleτ,hb.2]
  obtain ⟨P,hP⟩ := hBatch δ γ l hδ hδ₁ (by linarith only [hγ,hσ]) hγ₁ hl.le hl₁
    hK D Γ L long size b b b b m h hLarge.1 hnpos hDis hRob hD hΓ hSum hSlots hParts
    hLayout hEnd hb.1 (by rw [Nat.mul_comm]) hTrimν hTrimτ
    ((by positivity : 0 < c*(n:ℝ)/2).trans_le hMB) (h0.trans hMB) hN₁
    (by change (g:ℝ) ≤ μ*M; linarith only [hg,hScaleμ,hμM])
    (by change (g:ℝ) ≤ μ*B; linarith only [hg,hScaleμ,hμB])
    hBase hComp hh hRatio hShort
    (by change E ≤ (η/4)*B; dsimp only [B]; linarith only [hE,hEta])
    (by change (d:ℝ) ≤ (η/4)*B; dsimp only [B]; linarith only [hd,hEta,mul_nonneg hl.le hnR.le])
    hSlack hCount hAttach
  refine ⟨P,fun v => ?_⟩
  have hv := hP v
  change _ ≤ b+2*b+2*a at hv
  change _ ≤ 3*b+2*a
  omega

end OverfullWork.DirectedSpanningConfiguration
