module

public import OverfullWork.DirectedCenteredBatchBlocks
public import OverfullWork.DirectedPreparedBatch

@[expose] public section


/-! Construct a small batch from global semidegrees and scalar budgets.
All block-specific profile hypotheses come from the sampled partition. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveUsage InducedDigraphSampling
open scoped Classical
universe u v w

private theorem block_filter_eq {V : Type*} [Fintype V] (D : Digraph V) (X : Finset V) (v : V) :
    X ∩ inProfile D v = X.filter (fun w => D.Adj w v) ∧
    X ∩ outProfile D v = X.filter (D.Adj v) := by
  constructor <;> ext w <;> simp [inProfile,outProfile]

private theorem block_profile_absolute {V : Type*} [Fintype V] {D : Digraph V}
    {X : Finset V} {c e ε θ : ℝ} {z : ℕ} (he : 0 ≤ ε)
    (h : BlockProfiles D X c (ε*(X.card:ℝ)+θ*(Fintype.card V:ℝ)+3*(z:ℝ)))
    (hE : ε*(Fintype.card V:ℝ)+θ*(Fintype.card V:ℝ)+3*(z:ℝ) ≤ e) :
    ∀ v, |((X.filter (fun w => D.Adj w v)).card:ℝ)-c*(X.card:ℝ)| ≤ e ∧
      |((X.filter (D.Adj v)).card:ℝ)-c*(X.card:ℝ)| ≤ e := by
  intro v
  have hSize : (X.card:ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast card_le_univ X
  have hErr : ε*(X.card:ℝ)+θ*(Fintype.card V:ℝ)+3*(z:ℝ) ≤ e := by
    have hp := mul_le_mul_of_nonneg_left hSize he
    linarith only [hp,hE]
  simpa only [(block_filter_eq D X v).1,(block_filter_eq D X v).2] using
    And.intro ((h v).1.trans hErr) ((h v).2.trans hErr)

/-- A uniform small-batch theorem with scalar hypotheses. Vertex order
and the current dense center may vary after the constants and thresholds
have been chosen. The output includes its actual reserve loss. -/
theorem exists_batch_of_global_profiles (ν τ α d₀ ρ η c cB θ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/8)
    (hα : α ≤ 1) (hτα : 256*(8*τ) ≤ α)
    (hd₀ : 0 < d₀) (hρ : 0 < ρ) (hη : 0 < η) (hGap : 8*η ≤ d₀)
    (hScale : 52*η ≤ ρ*d₀) (hc : 0 < c) (hc₁ : c ≤ 1) (hcB : c ≤ cB) (hθ : 0 < θ) :
    ∃ N N₀ N₁ : ℕ, ∀ (δ γ ε : ℝ), d₀ ≤ δ → δ ≤ 1 → α ≤ γ → γ ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I] {J : Type w} [Fintype J]
      {k : ℕ}, 0 < k → ∀ (D Γ : Digraph V) (L : J → Layout V I) (long : J → I)
      (size : Fin k → ℕ) (z₀ b cap q z h : ℕ),
      let n := Fintype.card V
      let m := Fintype.card J
      let a := (m+k-1)/k
      let g := b+2*cap+2*a
      let d := m+b
      let νs := ν^6/(2:ℝ)^60
      let μ := νs/4
      let M := c*(n:ℝ)-(z₀:ℝ)
      let B := cB*(n:ℝ)
      let E := ε*(n:ℝ)+θ*(n:ℝ)+3*(z₀:ℝ)
      N ≤ n → 0 < n → Disjoint D Γ → IsRealRobust Γ ν τ →
      SemidegreesAround D (δ*(n:ℝ)) (ε*(n:ℝ)) →
      SemidegreesAround Γ (γ*(n:ℝ)) (ε*(n:ℝ)) →
      (∑ i,size i) = n → 3*k < n^2 →
      (∀ i, c*(n:ℝ) ≤ (size i:ℝ) ∧ cB*(n:ℝ) ≤ ((n-size i:ℕ):ℝ)) →
      (∀ i, (L i).boundary.card ≤ z₀ ∧ long i ∉ (L i).fixed ∧
        (univ \ insert (long i) (L i).fixed).card*h ≤ q) →
      (∀ v, (∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v)) ≤ b) →
      0 < cap → m*q ≤ cap*z →
      8*(z₀:ℝ) ≤ νs*(c*(n:ℝ)) → 4*(z₀:ℝ) ≤ (4*τ)*(c*(n:ℝ)) →
      0 < M → (N₀:ℝ) ≤ M → ((N₁+z₀+q:ℕ):ℝ) ≤ B →
      (g:ℝ) ≤ μ*M → (g:ℝ) ≤ μ*B →
      E+(g:ℝ) ≤ (γ-α)*M →
      E+((z+z₀+q+g+2:ℕ):ℝ) ≤ (γ-8*τ)*B →
      5 ≤ h → 1 ≤ (μ/2)*((h-5:ℕ):ℝ) →
      ((z+z₀+q+1:ℕ):ℝ) ≤ (μ/2)*B →
      E ≤ (η/4)*B → (d:ℝ) ≤ (η/4)*B →
      (η+1)*((z₀+q:ℕ):ℝ)+1 ≤ (η/2)*B →
      ρ*((n:ℝ)+1) ≤ (μ/4)^3*M →
      2*ρ*((n:ℝ)+1)+(d:ℝ)+E ≤ δ*M →
      ∃ P : PackingPrefix (D ⊔ Γ) L (univ : Finset J),
        ∀ v, inDegree (P.used ⊓ Γ) v+outDegree (P.used ⊓ Γ) v ≤ g := by
  let νs := ν^6/(2:ℝ)^60
  let μ := νs/4
  have hμ : 0 < μ := by dsimp [μ,νs]; positivity
  have hτp := hν.trans_le hντ
  have hμτ : μ ≤ 8*τ := by
    have hp : ν^6 ≤ ν := by
      have hh := pow_le_one₀ hν.le (show ν ≤ 1 by linarith only [hντ,hτ]) (n := 5)
      have h := mul_le_mul_of_nonneg_left hh hν.le
      nlinarith only [h]
    dsimp [μ,νs]
    norm_num
    linarith only [hp,hντ,hτp]
  obtain ⟨N,hSample⟩ := exists_centered_batch_blocks.{u,w} ν τ c cB θ
    hν hντ hτ hc hc₁ hcB hθ
  obtain ⟨N₀,N₁,hPack⟩ := exists_prepared_batch_uniform_in_density.{u,v,w} μ (8*τ) α d₀ ρ η
    hμ hμτ hτα hα hd₀ hρ hη hGap hScale
  refine ⟨N,N₀,N₁,?_⟩
  intro δ γ ε hδ₀ hδ₁ hγα hγ₁ he he₁ V _ I _ J _ k hk D Γ L long size z₀ b cap q z h
  dsimp only
  intro hN hn hDΓ hR hD hG hSum hSlots hSize hLayout hEnd hCap hz hTrimν hTrimτ hM hN₀
    hN₁ hG₁ hG₂ hGA hGB hh hRatio hShort hApprox hDense hSlack hCount hAttach
  let n := Fintype.card V
  let m := Fintype.card J
  let a := (m+k-1)/k
  let g := b+2*cap+2*a
  let d := m+b
  let M := c*(n:ℝ)-(z₀:ℝ)
  let B := cB*(n:ℝ)
  let E := ε*(n:ℝ)+θ*(n:ℝ)+3*(z₀:ℝ)
  have hB : 0 < B := mul_pos (hc.trans_le hcB) (by exact_mod_cast hn)
  have hd : 0 < δ := hd₀.trans_le hδ₀
  have hγ : 0 ≤ γ := by linarith only [hγα,hτα,hτp]
  obtain ⟨A,hVisits,hA⟩ := hSample hk D Γ (fun i => (L i).boundary) size z₀ δ γ ε
    hN hn hR hSum hSlots hSize (fun i => (hLayout i).1) hTrimν hTrimτ hd.le hδ₁ hγ hγ₁
    he he₁ hD hG
  obtain ⟨P⟩ := hPack δ hδ₀ hδ₁ D Γ L long A b a cap q z h (νs/2) (νs/2) μ
    (η/4) (η/2) hDΓ hμ.le hCap hz hEnd hVisits (by
      intro i
      dsimp only
      let X := A i
      let Y := Xᶜ
      let p := (univ \ insert (long i) (L i).fixed).card*h
      let s := ⌈(μ/2)*(Y.card:ℝ)⌉₊
      let t := ⌈(8*τ)*(Y.card:ℝ)⌉₊
      obtain ⟨hApart,hX,hY,hRX,hRY,hDX,hDY,hΓX,hΓY⟩ := hA i
      obtain ⟨hbd,hLong,hp⟩ := hLayout i
      change M ≤ (X.card:ℝ) at hX
      change B ≤ (Y.card:ℝ) at hY
      have hYPos := hB.trans_le hY
      have hYn : (Y.card:ℝ) ≤ (n:ℝ) := by exact_mod_cast card_le_univ Y
      have hPBound : ((L i).boundary.card+p:ℕ) ≤ z₀+q := Nat.add_le_add hbd hp
      have hPR : ((L i).boundary.card:ℝ)+(p:ℝ) ≤ ((z₀+q:ℕ):ℝ) := by exact_mod_cast hPBound
      have hGX := block_profile_absolute he hΓX (le_refl E)
      have hGY := block_profile_absolute he hΓY (le_refl E)
      have hDX' := block_profile_absolute he hDX (le_refl E)
      have hDY' := block_profile_absolute he hDY (le_refl E)
      have hXg : (g:ℝ) ≤ μ*(X.card:ℝ) :=
        hG₁.trans (mul_le_mul_of_nonneg_left hX hμ.le)
      have hYg : (g:ℝ) ≤ μ*(Y.card:ℝ) :=
        hG₂.trans (mul_le_mul_of_nonneg_left hY hμ.le)
      have hSize₁ : ((N₁+(L i).boundary.card+p:ℕ):ℝ) ≤ ((N₁+z₀+q:ℕ):ℝ) := by
        exact_mod_cast (show N₁+(L i).boundary.card+p ≤ N₁+z₀+q by omega)
      have hDsize := hSize₁.trans (hN₁.trans hY)
      have hMinX : E+(g:ℝ) ≤ (γ-α)*(X.card:ℝ) :=
        hGA.trans (mul_le_mul_of_nonneg_left hX (sub_nonneg.mpr hγα))
      have hMinY : E+((z+z₀+q+g+2:ℕ):ℝ) ≤ (γ-8*τ)*(Y.card:ℝ) :=
        hGB.trans (mul_le_mul_of_nonneg_left hY (by linarith only [hγα,hτα,hτp]))
      have hCeilT : (t:ℝ) < (8*τ)*(Y.card:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
      have hCpos : 0 < (μ/2)*(Y.card:ℝ) := mul_pos (by positivity) hYPos
      have hs : 0 < s := Nat.ceil_pos.mpr hCpos
      refine ⟨hLong,hApart,by exact_mod_cast hM.trans_le hX,
        by exact_mod_cast hN₀.trans hX,by exact_mod_cast hDsize,hp,hRX,?_,?_,hRY,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · change μ*(X.card:ℝ)+(g:ℝ) ≤ (νs/2)*(X.card:ℝ)
        dsimp [μ] at hXg ⊢
        linarith only [hXg]
      · intro x
        rw [induced_inDegree,induced_outDegree,(block_filter_eq Γ X x.val).1,
          (block_filter_eq Γ X x.val).2]
        have hi := (abs_le.mp (hGX x.val).1).1
        have ho := (abs_le.mp (hGX x.val).2).1
        constructor <;> linarith only [hMinX,hi,ho]
      · change μ*(Y.card:ℝ)+(g:ℝ) ≤ (νs/2)*(Y.card:ℝ)
        dsimp [μ] at hYg ⊢
        linarith only [hYg]
      · refine ⟨s,hs,?_,?_⟩
        · have hUse := mul_le_mul_of_nonneg_left (Nat.le_ceil ((μ/2)*(Y.card:ℝ)))
            (Nat.cast_nonneg (α := ℝ) (h-5))
          change 1 ≤ (μ/2)*((h-5:ℕ):ℝ) at hRatio
          have hUse' := mul_le_mul_of_nonneg_right hRatio (Nat.cast_nonneg (α := ℝ) Y.card)
          have hProd : Y.card ≤ s*(h-5) := by
            exact_mod_cast (show (Y.card:ℝ) ≤ (s:ℝ)*((h-5:ℕ):ℝ) by
              change _ ≤ ((h-5:ℕ):ℝ)*(s:ℝ) at hUse
              nlinarith only [hUse,hUse'])
          change Y.card/s+5 ≤ h
          have := Nat.div_le_of_le_mul hProd
          omega
        · have hS : (s:ℝ) < (μ/2)*(Y.card:ℝ)+1 := Nat.ceil_lt_add_one hCpos.le
          change ((z+z₀+q+1:ℕ):ℝ) ≤ (μ/2)*B at hShort
          have hAvail := hShort.trans (mul_le_mul_of_nonneg_left hY
            (show 0 ≤ μ/2 by positivity))
          have hToR : ((z+(L i).boundary.card+p+s:ℕ):ℝ) ≤ μ*(Y.card:ℝ) := by
            push_cast at hAvail hPR ⊢
            linarith only [hS,hAvail,hPR]
          exact_mod_cast hToR.trans (Nat.le_ceil (μ*(Y.card:ℝ)))
      · intro x
        rw [induced_inDegree,induced_outDegree,(block_filter_eq Γ Y x.val).1,
          (block_filter_eq Γ Y x.val).2]
        have hi := (abs_le.mp (hGY x.val).1).1
        have ho := (abs_le.mp (hGY x.val).2).1
        have hMin := hMinY
        push_cast at hMin
        have h₁ : (t:ℝ)+(g:ℝ) ≤ ((Y.filter (fun w => Γ.Adj w x.val)).card:ℝ) := by
          have hNon : 0 ≤ (z:ℝ)+(z₀:ℝ)+(q:ℝ) := by positivity
          linarith only [hMin,hi,hCeilT,hNon]
        have h₂ : (t:ℝ)+(z:ℝ)+((L i).boundary.card:ℝ)+(p:ℝ)+1+(g:ℝ) ≤
            ((Y.filter (Γ.Adj x.val)).card:ℝ) := by
          push_cast at hPR
          linarith only [hMin,ho,hCeilT,hPR]
        exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩
      · intro x _
        have hh := hApprox.trans (mul_le_mul_of_nonneg_left hY
          (show 0 ≤ η/4 by positivity))
        exact ⟨(hDY' x).1.trans hh,(hDY' x).2.trans hh⟩
      · have hh := hDense.trans (mul_le_mul_of_nonneg_left hY (show 0 ≤ η/4 by positivity))
        linarith only [hh]
      · have hh := hSlack.trans (mul_le_mul_of_nonneg_left hY (show 0 ≤ η/2 by positivity))
        have hPP : (((L i).boundary.card+p:ℕ):ℝ) ≤ ((z₀+q:ℕ):ℝ) := by exact_mod_cast hPBound
        have hPP' := mul_le_mul_of_nonneg_left hPP (show 0 ≤ η+1 by positivity)
        linarith only [hh,hPP']
      · exact (mul_le_mul_of_nonneg_left (by linarith only [hYn] : (Y.card:ℝ)+1 ≤ (n:ℝ)+1)
          hρ.le).trans (hCount.trans (mul_le_mul_of_nonneg_left hX (by positivity)))
      · intro x _
        have hAttach' := hAttach.trans (mul_le_mul_of_nonneg_left hX hd.le)
        have hB' := mul_le_mul_of_nonneg_left (show (Y.card:ℝ)+1 ≤ (n:ℝ)+1 by linarith only [hYn])
          (show 0 ≤ 2*ρ by positivity)
        have hi := (abs_le.mp (hDX' x).1).1
        have ho := (abs_le.mp (hDX' x).2).1
        exact ⟨by linarith only [hAttach',hB',ho],by linarith only [hAttach',hB',hi]⟩)
  exact ⟨P.toPackingPrefix,fun x => P.reserve_use hDΓ b a
    (fun v => by simpa using hEnd v) (fun v => (visits_prefix_le univ A v).trans (hVisits v)) x⟩

end OverfullWork.DirectedSpanningConfiguration
