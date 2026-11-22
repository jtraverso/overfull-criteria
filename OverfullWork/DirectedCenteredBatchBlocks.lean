module

public import OverfullWork.DirectedSampledBatchBlocks

@[expose] public section


/-! Turn the relative sampling errors into actual semidegree profiles
around the dense and reserve centers, including after a layout trim. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveUsage InducedDigraphSampling UniformSubsetSampling
open scoped Classical
universe u v

/-- Incoming and outgoing degrees into a specified block, including for
vertices outside the block that need to attach to it. -/
def BlockProfiles {V : Type*} [Fintype V] (D : Digraph V) (X : Finset V) (c e : ℝ) : Prop :=
  ∀ v, |((X ∩ inProfile D v).card:ℝ)-c*(X.card:ℝ)| ≤ e ∧
       |((X ∩ outProfile D v).card:ℝ)-c*(X.card:ℝ)| ≤ e

/-- A prescribed degree center and absolute error on the whole host. -/
def SemidegreesAround {V : Type*} [Fintype V] (D : Digraph V) (c e : ℝ) : Prop :=
  ∀ v, |(inDegree D v:ℝ)-c| ≤ e ∧ |(outDegree D v:ℝ)-c| ≤ e

private theorem rescale_profile (n k s p q z : ℕ) (c ε θ : ℝ)
    (hn : 0 < n) (hc : 0 ≤ c) (hc₁ : c ≤ 1) (he : 0 ≤ ε) (he₁ : ε ≤ 1)
    (hSize : k ≤ s+z ∧ s ≤ k+z)
    (hOriginal : |(p:ℝ)-c*(n:ℝ)| ≤ ε*(n:ℝ))
    (hSample : |(q:ℝ)-(k:ℝ)/(n:ℝ)*(p:ℝ)| ≤ θ+(z:ℝ)) :
    |(q:ℝ)-c*(s:ℝ)| ≤ ε*(s:ℝ)+θ+3*(z:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let r : ℝ := (k:ℝ)/(n:ℝ)
  have hr : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) hnR.le
  have hrn : r*(n:ℝ) = (k:ℝ) := div_mul_cancel₀ _ hnR.ne'
  have hMid : |r*(p:ℝ)-c*(k:ℝ)| ≤ ε*(k:ℝ) := by
    calc
      _ = r*|(p:ℝ)-c*(n:ℝ)| := by
        have hEq : r*(p:ℝ)-c*(k:ℝ) = r*((p:ℝ)-c*(n:ℝ)) := by
          calc
            _ = r*(p:ℝ)-c*(r*(n:ℝ)) := by rw [hrn]
            _ = _ := by ring
        rw [hEq,abs_mul,abs_of_nonneg hr]
      _ ≤ r*(ε*(n:ℝ)) := mul_le_mul_of_nonneg_left hOriginal hr
      _ = _ := by rw [show r*(ε*(n:ℝ)) = ε*(r*(n:ℝ)) by ring,hrn]
  have h₁ : (k:ℝ) ≤ (s:ℝ)+(z:ℝ) := by exact_mod_cast hSize.1
  have h₂ : (s:ℝ) ≤ (k:ℝ)+(z:ℝ) := by exact_mod_cast hSize.2
  have hShift : |c*(k:ℝ)-c*(s:ℝ)| ≤ (z:ℝ) := by
    have hAbs : |(k:ℝ)-(s:ℝ)| ≤ (z:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
    rw [← mul_sub,abs_mul,abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left hAbs hc).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc₁ (Nat.cast_nonneg (α := ℝ) z))
  have hScale : ε*(k:ℝ) ≤ ε*(s:ℝ)+(z:ℝ) := by
    have h := mul_le_mul_of_nonneg_left h₁ he
    have hz := mul_le_mul_of_nonneg_right he₁ (Nat.cast_nonneg (α := ℝ) z)
    nlinarith only [h,hz]
  have hTriangle := abs_sub_le (q:ℝ) (r*(p:ℝ)) (c*(s:ℝ))
  have hTriangle' := abs_sub_le (r*(p:ℝ)) (c*(k:ℝ)) (c*(s:ℝ))
  change |(q:ℝ)-r*(p:ℝ)| ≤ θ+(z:ℝ) at hSample
  linarith only [hTriangle,hTriangle',hSample,hMid,hShift,hScale]

/-- Sample and trim all blocks for a batch using the normalized
semidegrees of both actual host graphs. The recovered profiles are
centered at the size of the trimmed block and its complement. -/
theorem exists_centered_batch_blocks (ν τ c cB θ : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ 1/8) (hc : 0 < c) (hc₁ : c ≤ 1) (hcB : c ≤ cB) (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {J : Type v} [Fintype J]
      {k : ℕ} (_hk : 0 < k) (D Γ : Digraph V) (boundary : J → Finset V)
      (size : Fin k → ℕ) (z : ℕ) (δ γ ε : ℝ),
      let n := Fintype.card V
      let νs := ν^6/(2:ℝ)^60
      N ≤ n → 0 < n → IsRealRobust Γ ν τ → (∑ i,size i) = n → 3*k < n^2 →
      (∀ i, c*(n:ℝ) ≤ (size i:ℝ) ∧ cB*(n:ℝ) ≤ ((n-size i:ℕ):ℝ)) →
      (∀ j, (boundary j).card ≤ z) → 8*(z:ℝ) ≤ νs*(c*(n:ℝ)) →
      4*(z:ℝ) ≤ (4*τ)*(c*(n:ℝ)) →
      0 ≤ δ → δ ≤ 1 → 0 ≤ γ → γ ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      SemidegreesAround D (δ*(n:ℝ)) (ε*(n:ℝ)) →
      SemidegreesAround Γ (γ*(n:ℝ)) (ε*(n:ℝ)) →
      ∃ A : J → Finset V,
        (∀ v, visits A v ≤ (Fintype.card J+k-1)/k) ∧
        ∀ i, let B := (A i)ᶜ
          let e := fun X : Finset V => ε*(X.card:ℝ)+θ*(n:ℝ)+3*(z:ℝ)
          Disjoint (boundary i) (A i) ∧ c*(n:ℝ)-(z:ℝ) ≤ ((A i).card:ℝ) ∧ cB*(n:ℝ) ≤ (B.card:ℝ) ∧
          IsRealRobust (induced Γ (A i)) (νs/2) (8*τ) ∧ IsRealRobust (induced Γ B) (νs/2) (8*τ) ∧
          BlockProfiles D (A i) δ (e (A i)) ∧ BlockProfiles D B δ (e B) ∧
          BlockProfiles Γ (A i) γ (e (A i)) ∧ BlockProfiles Γ B γ (e B) := by
  obtain ⟨N,hN⟩ := exists_sampled_batch_blocks.{u,v,u} ν τ c 4 θ hν hντ hτ hc hc₁
    (by norm_num) hθ
  refine ⟨N,?_⟩
  intro V _ J _ k hk D Γ boundary size z δ γ ε
  dsimp only
  intro hOrder hn hR hSum hSlots hSmall hBdry hνTrim hτTrim hδ hδ₁ hγ hγ₁ he he₁ hDeg hRes
  let profiles (i : Bool × Bool × V) : Finset V :=
    let G := if i.1 then Γ else D
    if i.2.1 then outProfile G i.2.2 else inProfile G i.2.2
  have hP : (Fintype.card (Bool × Bool × V):ℝ) ≤ 4*(Fintype.card V:ℝ) := by
    simp [Fintype.card_prod]
    linarith
  obtain ⟨rank,slot,hVisit,hBlock⟩ := hN hk Γ profiles boundary size z hOrder hn hR hSum
    hP hSlots (fun i => ⟨(hSmall i).1,(mul_le_mul_of_nonneg_right hcB
      (Nat.cast_nonneg _)).trans (hSmall i).2⟩) hBdry hνTrim hτTrim
  let A := fun i => slice rank (slot i) \ boundary i
  refine ⟨A,hVisit,?_⟩
  intro i
  let X := A i
  let Y := (A i)ᶜ
  let n := Fintype.card V
  let m := size (slot i)
  obtain ⟨hApart,ha,ha',hrA,hrB,hs⟩ := hBlock i
  change X.card ≤ m at ha
  change m ≤ X.card+z at ha'
  have hSize : m ≤ n := by
    change size (slot i) ≤ Fintype.card V
    rw [← hSum]
    exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ (slot i))
  have hC : Y.card = n-X.card := card_compl _
  have hCY : n-m ≤ Y.card ∧ Y.card ≤ (n-m)+z := by omega
  have hX : c*(n:ℝ)-(z:ℝ) ≤ (X.card:ℝ) := by
    have ht : (m:ℝ) ≤ (X.card:ℝ)+(z:ℝ) := by exact_mod_cast ha'
    linarith only [ht,(hSmall (slot i)).1]
  have hY : cB*(n:ℝ) ≤ (Y.card:ℝ) := (hSmall (slot i)).2.trans (by exact_mod_cast hCY.1)
  have hAll (j : Bool × Bool × V) (center : ℝ) (hh : 0 ≤ center) (hh₁ : center ≤ 1)
      (hOriginal : |((profiles j).card:ℝ)-center*(n:ℝ)| ≤ ε*(n:ℝ)) :
      |((X ∩ profiles j).card:ℝ)-center*(X.card:ℝ)| ≤ ε*(X.card:ℝ)+θ*(n:ℝ)+3*(z:ℝ) ∧
      |((Y ∩ profiles j).card:ℝ)-center*(Y.card:ℝ)| ≤ ε*(Y.card:ℝ)+θ*(n:ℝ)+3*(z:ℝ) := by
    refine ⟨rescale_profile n m X.card _ _ z center ε (θ*(n:ℝ)) hn hh hh₁ he he₁
      ⟨ha',ha.trans (Nat.le_add_right _ _)⟩ hOriginal (hs j).1.le,
      rescale_profile n (n-m) Y.card _ _ z center ε (θ*(n:ℝ)) hn hh hh₁ he he₁
        ⟨hCY.1.trans (Nat.le_add_right _ _),hCY.2⟩ hOriginal (hs j).2.le⟩
  have hDi (v : V) := hAll (false,false,v) δ hδ hδ₁ (by simpa [profiles,inProfile_card] using (hDeg v).1)
  have hDo (v : V) := hAll (false,true,v) δ hδ hδ₁ (by simpa [profiles,outProfile_card] using (hDeg v).2)
  have hΓi (v : V) := hAll (true,false,v) γ hγ hγ₁ (by simpa [profiles,inProfile_card] using (hRes v).1)
  have hΓo (v : V) := hAll (true,true,v) γ hγ hγ₁ (by simpa [profiles,outProfile_card] using (hRes v).2)
  exact ⟨hApart,hX,hY,hrA,hrB,fun v => ⟨(hDi v).1,(hDo v).1⟩,fun v => ⟨(hDi v).2,(hDo v).2⟩,
    fun v => ⟨(hΓi v).1,(hΓo v).1⟩,fun v => ⟨(hΓi v).2,(hΓo v).2⟩⟩

end OverfullWork.DirectedSpanningConfiguration
