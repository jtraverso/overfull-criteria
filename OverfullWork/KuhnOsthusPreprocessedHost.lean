module

public import OverfullWork.KuhnOsthusExceptionalStagesFromHost
public import OverfullWork.KuhnOsthusPreprocessedCorollary85
public import OverfullWork.KuhnOsthusPreprocessingSamplingScales

@[expose] public section


/-! Construct the physical preprocessing graph in the proof of
Kühn–Osthus Theorem 1.2 (Lemma 8.6 and (11.7)–(11.12)). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 4800000 in
/-- Instantiate the bounds of Lemma 8.6 before choosing the actual
cluster sizes. The graph and extender come from the 50-style packing,
and the chord factors are then chosen in their physical complement.
The same extender processes every admissible leftover by Corollary 8.5. -/
theorem exists_kuhn_osthus_preprocessed_robust_host
    (ν τ α d θ d₁Max ζMax : ℝ) (l g L : ℕ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hντ : ν ≤ τ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hTau : 64*τ ≤ α)
    (hd : 0 < d) (hdν : 8*d ≤ ν) (hdα : d ≤ α)
    (hθ : 0 < θ) (hθ₁ : θ < 1) (hd₁Max : 0 < d₁Max) (hζMax : 0 < ζMax)
    (hl : 2 ≤ l) (hg : 2 ≤ g) (hWalk : ⌈25/((ν/8)^2/2)^2⌉₊+4 ≤ L)
    (hRouteMass : (10^7:ℝ) ≤ ((50*l+1:ℕ):ℝ)*((ν/8)^2/2)^2) :
    ∃ d₁ : ℝ, 0 < d₁ ∧ d₁ < d ∧ d₁ ≤ d₁Max ∧
    ∀ (fMin qMin : ℕ) (target εP : ℝ), 0 < target → 0 < εP → εP ≤ 1/100 →
      800*εP ≤ ((1/1000:ℝ)*((d/2)/4))^2 →
    ∃ (f q b₈ b₁₀ : ℕ) (w₈ : f^2 = l*b₈) (w₉ : f^2 = f*f) (w₁₀ : f^2 = 7*b₁₀),
      fMin ≤ f ∧ qMin ≤ q ∧ g ∣ f ∧ f ∣ q ∧ 0 < q/f ∧ (q/f)*f = q ∧ f ≤ q/f ∧
    ∃ ζ ε ξ σ₈ σ₉ σ₁₀ : ℝ, 0 < ζ ∧ ζ ≤ ζMax ∧ ζ ≤ 1/2 ∧ 0 < ε ∧ 0 < ξ ∧ ξ ≤ target ∧
      0 < σ₈ ∧ 2*σ₈ ≤ d/2 ∧ 0 < σ₉ ∧ 0 < σ₁₀ ∧
      2*ζ ≤ 1/((50*l+1:ℕ):ℝ) ∧ 32*ζ ≤ ν ∧ ζ ≤ (ν/4)^4 ∧
      22*d₁+4*ζ ≤ ν/2 ∧ 22*d₁+4*ζ ≤ α ∧
    ∃ nMax : ℕ, 0 < nMax ∧
    ∀ (d₃Max : ℝ) (ηMax : ℝ → ℝ → ℝ), 0 < d₃Max →
      (∀ x y, 0 < x → 0 < y → 0 < ηMax x y) →
    ∃ d₃ c η d₀ ηS : ℝ, 0 < d₃ ∧ 0 < c ∧ 0 < η ∧ c ≤ d₃ ∧ d₃ ≤ d₃Max ∧ η ≤ ηMax d₃ c ∧
      0 < d₀ ∧ 0 < ηS ∧ ηS ≤ d₀/400 ∧
    ∀ T : ℕ, ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (r : ℕ),
      N ≤ Fintype.card V → IsRealRobust G ν τ → (8*α)*(Fintype.card V:ℝ) ≤ (r:ℝ) →
      (∀ v, inDegree G v = r ∧ outDegree G v = r) → (∀ v, ¬ G.Adj v v) →
      ∃ (k m base m₈ m₉ mWalk : ℕ) (hk : 0 < k) (Z₀ Z : Finset V) (P : Fin k → Finset V)
        (R₀ : Digraph (Fin k)) (A X : Fin (f^2*k) → Finset V)
        (routes : Fin (f^2*k) → List (Fin (f^2*k))) (F : Fin (L+1) → Equiv.Perm (Fin (f^2*k))),
        let n := f^2*k
        let parent := windingParent (n := n) k hk
        let R := fibrePullback R₀ parent parent
        let i₈ : n = l*(b₈*k) := by dsimp only [n]; rw [w₈,Nat.mul_assoc]
        let i₉ : n = f*(f*k) := by dsimp only [n]; rw [w₉,Nat.mul_assoc]
        let i₁₀ : n = 7*(b₁₀*k) := by dsimp only [n]; rw [w₁₀,Nat.mul_assoc]
        let R₈ := fibrePullback R (finCongr i₈.symm) (finCongr i₈.symm)
        let X₈ (i : Fin (l*(b₈*k))) := X (finCongr i₈.symm i)
        let X₉ (i : Fin (f*(f*k))) := X (finCongr i₉.symm i)
        let X₁₀ (i : Fin (7*(b₁₀*k))) := X (finCongr i₁₀.symm i)
        let r₀ := ⌊η*(r:ℝ)⌋₊
        let p := ⌊d₃*(base:ℝ)⌋₊
        let a := 50*l*r₀
        let t := p-a
        let r₁ := ⌊d₁*(base:ℝ)⌋₊
        let r₂ := 96*(L+1)*g^2*n*t
        ∃ (r₃ : ℕ) (j₈ : 0 < b₈*k) (j₉ : 0 < f*k) (j₁₀ : 0 < b₁₀*k),
          let s := r₁+r₂+t-(q-1)*r₃
          base = 50*m₈ ∧ base = (q/f)*m₉ ∧ f*base = q*m₉ ∧ base = (4*(L+1))*mWalk ∧
          T ≤ m₈ ∧ T ≤ m₉ ∧ T ≤ mWalk ∧ T ≤ base ∧ n ≤ nMax ∧
          14 ∣ n ∧ q ∣ f*n ∧ (∃ p d : ℕ, f*n = p*10 ∧ f*n = d*3*g.choose 2) ∧
          WoundExceptionalPartition G Z₀ Z P A X R₀ hk (f^2) (f^2*m) base α θ ε (ν/8) (4*τ) ∧
          (Z.card:ℝ) ≤ ζ*(Fintype.card V:ℝ) ∧
          (∀ i j, R.Adj i j → IsUniform G ξ (X i) (X j) ∧ d ≤ density G (X i) (X j)) ∧
          (∀ s i, IsLowerSuperregularPair G ξ d (X i) (X (F s i))) ∧
          F 0 = finRotate n ∧ (∀ s i, R.Adj i (F s i)) ∧
          (∀ j, DirectedListRoutes.Route (reindexSources R (finRotate n).symm) j (finRotate n j) (routes j) ∧
            ((routes j).length:ℝ) ≤ 3/((ν/8)^2/2)) ∧
          (∀ x y, ((univ : Finset (Fin (L+1))).filter (fun j => F j x = y)).card =
            elementaryChordMultiplicity (finRotate n) routes x y +
              if finRotate n x = y then L+1 - (∑ z, elementaryChordMultiplicity (finRotate n) routes x z) else 0) ∧
          HasSpanningCycle (fun e f : (Σ _ : Fin (L+1), Fin n) => F e.1 e.2 = f.2) ∧
          0 < r₀ ∧ (r₀:ℝ) ≤ c*(base:ℝ) ∧ a+t = p ∧ p*n^2 ≤ r₁ ∧ r₁ ≤ base ∧ t*n*f^2 ≤ base ∧
          t*(f*n) = q*r₃ ∧ q*r₃ ≤ r₁ ∧ r₂ ≤ r₁ ∧ r₃ ≤ r₁ ∧ (q-1)*r₃+s = r₁+r₂+t ∧ r₂+t+r₃ ≤ s ∧
          p+r₁+r₂+r₃+6*s ≤ 22*r₁ ∧ Zᶜ.card = n*base ∧
          ((r₀*(50*l+1):ℕ):ℝ) ≤ εP*(d₀/(n:ℝ))*((2*εP)*(50*m₈)) ∧
          (1/1000:ℝ)*d₀*(50*m₈)+((r₀*(50*l+1):ℕ):ℝ) ≤ 21*((d₀/200-ηS)*(50*m₈)) ∧
          ∃ prep : KuhnOsthusPreprocessingReserve G Z R₈ X₈ j₈ m₈ r₀ t σ₈ (d/2) d₀ εP ηS,
            Nonempty (WoundFactorPacking (G \ prep.graph) Z X₉ j₉ (q/f) m₉ r₃ σ₉) ∧
            WoundFactorStage G Z X₁₀ j₁₀ 1 base s (a+t+r₁+r₂+r₃) (a+q*r₃) σ₁₀ ∧
            ∀ B H : Digraph V, H ≤ G \ (prep.graph ⊔ B) →
              (∀ v, inDegree H v = r₀ ∧ outDegree H v = r₀) →
              (∀ x y, x ∈ Z → y ∈ Z → ¬ H.Adj x y) →
              ∃ (a : ℕ) (C : Fin a → Equiv.Perm V), matchingUnion C ≤ prep.graph ⊔ H ∧
                (∀ i, HasSpanningCycle (fun x y => C i x = y)) ∧
                (∀ i j, i ≠ j → ∀ v, C i v ≠ C j v) ∧
                let Remainder := (prep.graph ⊔ H) \ matchingUnion C
                (∀ x y, Remainder.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
                ∀ v : ↥Zᶜ, inDegree (induced Remainder Zᶜ) v = t ∧ outDegree (induced Remainder Zᶜ) v = t := by
  let dP := d/2
  have hdP : 0 < dP := by dsimp only [dP]; positivity
  have hdP₁ : dP ≤ 1 := by dsimp only [dP]; linarith only [hdν,hν₁]
  obtain ⟨d₁,hd₁,hd₁d,hd₁Max',hStage⟩ :=
    exists_kuhn_osthus_exceptional_stages_from_robust_host.{u} ν τ α d θ d₁Max ζMax l g L
      hν hν₁ hντ hα hα₁ hTau hd hdν hdα hθ hθ₁ hd₁Max hζMax hl hg hWalk
  refine ⟨d₁,hd₁,hd₁d,hd₁Max',?_⟩
  intro fMin qMin target εP hTarget hεP hεP₁ hεPScale
  obtain ⟨ξCap,ξP,δ,cMax,hCap,hξP,hδ,hcMax,hξε,hξ₁,hRel,hξd,hLocal⟩ :=
    exists_kuhn_osthus_preprocessing_pair_scales dP εP hdP hdP₁ hεP
  obtain ⟨f,q,b₈,b₁₀,w₈,w₉,w₁₀,hfMin,hqMin,hgf,hfq,hqf,hqEq,hRatio,ζ,ε,ξ,σ₈,σ₉,σ₁₀,
    hζ,hζMax',hζHalf,hε,hξ,hξCap,hσ₈,hσ₈d,hσ₉,hσ₁₀,hZSlots,hZν,hZPow,hZν',hZα,J,hJ,hSchedule⟩ :=
    hStage fMin qMin (min target ξCap) (lt_min hTarget hCap)
  change 2*σ₈ ≤ dP at hσ₈d
  have hσ₈Half : σ₈ ≤ 1/2 := by linarith only [hσ₈d,hdP₁]
  have hStyle : (1/200:ℝ) ≤ (1-σ₈)/50 := by linarith only [hσ₈Half]
  refine ⟨f,q,b₈,b₁₀,w₈,w₉,w₁₀,hfMin,hqMin,hgf,hfq,hqf,hqEq,hRatio,ζ,ε,ξ,σ₈,σ₉,σ₁₀,
    hζ,hζMax',hζHalf,hε,hξ,hξCap.trans (min_le_left _ _),hσ₈,hσ₈d,hσ₉,hσ₁₀,
    hZSlots,hZν,hZPow,hZν',hZα,J,hJ,?_⟩
  intro d₃Max ηMax hd₃Max hηMax
  let dExt (c : ℝ) := c*dP/16
  let residualCap (c : ℝ) := εP^2*(dExt c/(J:ℝ))/(((50*l+1:ℕ):ℝ)*(J:ℝ))
  have hJR : (0:ℝ) < J := by exact_mod_cast hJ
  have heCap (c : ℝ) (hc : 0 < c) : 0 < residualCap c := by
    dsimp only [residualCap,dExt]
    positivity
  obtain ⟨d₃,c,η,hd₃,hc,hη,hc₃,hd₃Cap,hηCap,hHost⟩ :=
    hSchedule (min d₃Max (min cMax 1)) (fun a b => min (ηMax a b) (residualCap b))
      (lt_min hd₃Max (lt_min hcMax (by norm_num))) (fun a b ha hb => lt_min (hηMax a b ha hb) (heCap b hb))
  have hcMax' : c ≤ cMax := hc₃.trans (hd₃Cap.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc₁ : c ≤ 1 := hc₃.trans (hd₃Cap.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let d₀ := dExt c
  have hd₀ : 0 < d₀ := by dsimp only [d₀,dExt]; positivity
  have hd₀Small : d₀ ≤ dP/4 := by
    dsimp only [d₀,dExt]
    linarith only [mul_le_mul_of_nonneg_right hc₁ hdP.le,hdP]
  obtain ⟨ηS,hηS,hηS',hSample⟩ := exists_kuhn_osthus_preprocessing_sampling_error εP d₀ J hεP hd₀ hJ
  refine ⟨d₃,c,η,d₀,ηS,hd₃,hc,hη,hc₃,hd₃Cap.trans (min_le_left _ _),
    hηCap.trans (min_le_left _ _),hd₀,hηS,hηS',?_⟩
  let ready (j : ℕ) (hj : 0 < j) (hJ' : l*j ≤ J) :=
    let margin := hSample (l*j) (Nat.mul_pos (by omega) hj) hJ'
    kuhn_osthus_preprocessing_reserve_from_wound_pack.{u} dP d₀ εP ξP δ ζ ηS σ₈ (1/200) l j hl hj
      hdP hdP₁ hd₀ hd₀Small hεP hξP hξε hξ₁ hRel hξd hζHalf hηS
      margin.1 margin.2.1 margin.2.2.1 margin.2.2.2 hδ (by linarith only [hσ₈Half]) hStyle
  let process (j : ℕ) (hj : 0 < j) :=
    exists_kuhn_osthus_process_leftover_on_preprocessing_reserve.{u} l j hl hj dP d₀ εP
      hdP hd₀ hεP hεP₁ hεPScale
  let cutoff (j : ℕ) : ℕ :=
    if h : 0 < j ∧ l*j ≤ J then max (ready j h.1 h.2).choose (process j h.1).choose else 0
  let C := (range (J+1)).sup cutoff
  intro T
  let T' := max 1 (max T C)
  obtain ⟨N,hN⟩ := hHost T'
  refine ⟨N,?_⟩
  intro V _ G r hNlarge hRob hMin hRegular hLoop
  obtain ⟨k,m,base,m₈,m₉,mWalk,hk,Z₀,Z,P,R₀,A,X,routes,F,r₃,u,j₈,j₉,j₁₀,
    hB₈,hB₉,hBQ,hBW,hT₈,hT₉,hTW,hTB,hnJ,hOrder,hSlotOrder,h14,hStyleDiv,hDiv,hPart,hSizeZ,hReg,hSup,hFirst,hF,hRoutes,hMult,hWalk',
    hR₀,hR₀c,hSum,hpK,hr₁,hSparse,hChord,hQr,hR₂,hR₃,hBal,hSpend,hTot,hDemand,hLo,hHi,hSmall,hSquare,
    hOrd,hrVol,hWidthLow,hWidthHigh,hFlowRobust,hFlowDegree,hStage₈,hStage₉,hStage₁₀⟩ :=
    hN G r hNlarge hRob hMin hRegular
  let n := f^2*k
  have hi₈ : n = l*(b₈*k) := by dsimp only [n]; rw [w₈,Nat.mul_assoc]
  have hi₉ : n = f*(f*k) := by dsimp only [n]; rw [w₉,Nat.mul_assoc]
  let toOriginal := finCongr hi₈.symm
  let parent := windingParent (n := n) k hk
  let R := fibrePullback R₀ parent parent
  let R₈ := fibrePullback R toOriginal toOriginal
  let X₈ i := X (toOriginal i)
  let X₉ i := X (finCongr hi₉.symm i)
  let r₀ := ⌊η*(r:ℝ)⌋₊
  let p := ⌊d₃*(base:ℝ)⌋₊
  let a := 50*l*r₀
  let t := p-a
  let D := ⌈c*(base:ℝ)⌉₊
  have hjBound : l*(b₈*k) ≤ J := hi₈ ▸ hnJ
  have hjSmall : b₈*k ≤ J := (Nat.le_mul_of_pos_left _ (by omega : 0 < l)).trans hjBound
  have hNb : max (ready (b₈*k) j₈ hjBound).choose (process (b₈*k) j₈).choose ≤ C := by
    have hSup' : cutoff (b₈*k) ≤ C :=
      Finset.le_sup (f := cutoff) (mem_range.mpr (by omega : b₈*k < J+1))
    have hj : 0 < b₈*k ∧ l*(b₈*k) ≤ J := ⟨j₈,hjBound⟩
    simpa only [cutoff,dif_pos hj] using hSup'
  have hm₈ : 0 < m₈ := (le_max_left _ _).trans hT₈
  have hC₈ : C ≤ m₈ := (le_max_right _ _).trans ((le_max_right _ _).trans hT₈)
  have hN₈ : (ready (b₈*k) j₈ hjBound).choose ≤ 50*m₈ :=
    (le_max_left _ _).trans (hNb.trans (hC₈.trans (Nat.le_mul_of_pos_left _ (by decide))))
  have hN₈₅ : (process (b₈*k) j₈).choose ≤ m₈ := (le_max_right _ _).trans (hNb.trans hC₈)
  have hRLocal : (r₀:ℝ) ≤ cMax*((50*m₈:ℕ):ℝ) := by
    rw [←hB₈]
    exact hR₀c.trans (mul_le_mul_of_nonneg_right hcMax' (Nat.cast_nonneg base))
  obtain ⟨hTol,hTol',hTheta,hLocalCut,hLocalPay,_,hLocalStyles⟩ :=
    hLocal ξ σ₈ hξ.le (hξCap.trans (min_le_right _ _)) (by linarith only [hσ₈d,hσ₈]) hσ₈Half
      r₀ (50*m₈) hRLocal
  have hRot (i : Fin (l*(b₈*k))) :
      toOriginal (finRotate (l*(b₈*k)) i) = finRotate n (toOriginal i) := by
    apply Fin.ext
    change (finRotate (l*(b₈*k)) i).val = (finRotate n (toOriginal i)).val
    rw [finRotate_val_modulo,finRotate_val_modulo]
    change (i.val+1) % (l*(b₈*k)) = (i.val+1) % n
    exact congrArg ((i.val+1) % ·) hi₈.symm
  have hRegular₈ (i j : Fin (l*(b₈*k))) (h : R₈.Adj i j) :
      IsUniform G ξ (X₈ i) (X₈ j) ∧ dP ≤ density G (X₈ i) (X₈ j) := by
    obtain ⟨hU,hD⟩ := hReg (toOriginal i) (toOriginal j) h
    exact ⟨hU,(by dsimp only [dP]; linarith only [hd] : dP ≤ d).trans hD⟩
  have hSuper₈ (i : Fin (l*(b₈*k))) :
      IsLowerSuperregularPair G ξ dP (X₈ i) (X₈ (finRotate (l*(b₈*k)) i)) := by
    obtain ⟨d',hLo',hHi',hSuper⟩ := hSup 0 (toOriginal i)
    rw [hFirst] at hSuper
    refine ⟨d',by dsimp only [dP]; linarith only [hd,hLo'],hHi',?_⟩
    simpa only [X₈,hRot] using hSuper
  have hZero (x : V) : inDegree (⊥ : Digraph V) x ≤ 0 ∧ outDegree (⊥ : Digraph V) x ≤ 0 := by
    simp [inDegree,inNeighbours,outDegree]
  have hPacking₈ : Nonempty (WoundFactorPacking G Z X₈ j₈ 50 m₈ r₀ σ₈) := by
    simpa only [sdiff_bot] using hStage₈ ⊥ bot_le hZero (fun x _ => hZero x)
  obtain ⟨E₈⟩ := hPacking₈
  have hExtenderDegree : (8*d₀/dP)*(50*m₈) ≤ (D:ℝ) := by
    have hEq : 8*d₀/dP = c/2 := by
      dsimp only [d₀,dExt]
      field_simp; ring
    rw [hEq]
    have hDB : c*(base:ℝ) ≤ (D:ℝ) := Nat.le_ceil _
    have hLE := mul_le_mul_of_nonneg_right (show c/2 ≤ c by linarith only [hc]) (Nat.cast_nonneg base)
    simpa only [hB₈,Nat.cast_mul,Nat.cast_ofNat] using hLE.trans hDB
  have hDegreeP : r₀*(50*l)+t = p := by rw [mul_comm r₀]; exact hSum
  have hDegreeA : r₀*(50*l) = a := mul_comm _ _
  have hIn (v : V) : 2*⌈(2*τ)*(Zᶜ.card:ℝ)⌉₊+p+(D+a)+Z.card ≤ inDegree G v :=
    (hRegular v).1.symm ▸ hFlowDegree
  have hOut (v : V) : 2*⌈(2*τ)*(Zᶜ.card:ℝ)⌉₊+p+(D+a)+Z.card ≤ outDegree G v :=
    (hRegular v).2.symm ▸ hFlowDegree
  obtain ⟨label,cluster,H,S,PG,B,hLabel,hCoord,hHS,hSub,hPairs,hDegreeHS,hPG,hB,hInd,hKeep,hApart,hDegree⟩ :=
    (ready (b₈*k) j₈ hjBound).choose_spec G Z R₈ X₈ t D u ξ ν τ (ν/16) (2*τ) hN₈ hm₈
      (fun i => (hPart.fine_size (toOriginal i)).1.trans hB₈)
      (fun i j hij => hPart.fine_disjoint _ _ (fun h => hij (toOriginal.injective h)))
      (fun i => hPart.fine_ordinary (toOriginal i))
      (fun v hv => by
        obtain ⟨i,hi⟩ := hPart.fine_cover v hv
        exact ⟨toOriginal.symm i,by simpa only [X₈,Equiv.apply_symm_apply] using hi⟩)
      hRegular₈ hSuper₈ hξ.le hTol hTol' hTheta (by exact_mod_cast hLocalCut)
      (by exact_mod_cast hLocalPay) (by exact_mod_cast hLocalStyles) hExtenderDegree
      hRob (by positivity) hWidthLow hWidthHigh (by rwa [hDegreeA])
      (by rwa [hDegreeP]) (by rwa [hDegreeP]) (by rwa [hDegreeP])
      (by rwa [hDegreeP,hOrd]) (by rwa [hDegreeP,hOrd])
      (fun v => by rw [hDegreeP,hDegreeA]; exact hIn v)
      (fun v => by rw [hDegreeP,hDegreeA]; exact hOut v) E₈
  have hStyleEq : (1/200:ℝ)*d₀-ηS = d₀/200-ηS := by ring
  rw [hStyleEq] at hPairs
  let prep : KuhnOsthusPreprocessingReserve G Z R₈ X₈ j₈ m₈ r₀ t σ₈ dP d₀ εP ηS :=
    ⟨E₈,label,cluster,H,S,PG,B,hLabel,hCoord,hHS,hPairs,hDegreeHS,hPG,hB,hInd,hKeep,hApart,hDegree⟩
  have hAll (v : V) : inDegree PG v ≤ a+t ∧ outDegree PG v ≤ a+t := by
    obtain ⟨hi,ho⟩ := hDegree v
    by_cases hv : v ∈ Z
    · rw [if_pos hv] at hi ho
      exact ⟨hi.le.trans (Nat.le_add_right _ _),ho.le.trans (Nat.le_add_right _ _)⟩
    · rw [if_neg hv] at hi ho
      exact ⟨hi.le,ho.le⟩
  have hExc (v : V) (hv : v ∈ Z) : inDegree PG v ≤ a ∧ outDegree PG v ≤ a := by
    obtain ⟨hi,ho⟩ := hDegree v
    rw [if_pos hv] at hi ho
    exact ⟨hi.le,ho.le⟩
  have hPacking₉ : Nonempty (WoundFactorPacking (G \ prep.graph) Z X₉ j₉ (q/f) m₉ r₃ σ₉) :=
    hStage₉ PG hPG hAll hExc
  have hn : 0 < n := hi₈.symm ▸ Nat.mul_pos (by omega) j₈
  obtain ⟨hEnds,hStyles⟩ := kuhn_osthus_preprocessing_residual_endpoint_budgets
    r r₀ (50*l+1) n J m₈ εP (1/1000) d₀ η ηS (by omega)
    hn hnJ
    hεP hεP₁ le_rfl hd₀ hη.le hηS' (hηCap.trans (min_le_right _ _)) (by rwa [←hB₈]) rfl
  have hT : T ≤ T' := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨k,m,base,m₈,m₉,mWalk,hk,Z₀,Z,P,R₀,A,X,routes,F,r₃,j₈,j₉,j₁₀,hB₈,hB₉,hBQ,hBW,
    hT.trans hT₈,hT.trans hT₉,hT.trans hTW,hT.trans hTB,hnJ,h14,hStyleDiv,hDiv,hPart,hSizeZ,hReg,hSup,
    hFirst,hF,hRoutes,hMult,hWalk',hR₀,hR₀c,hSum,hpK,hr₁,hSparse,hChord,hQr,hR₂,hR₃,hBal,hSpend,hTot,
    hOrd,hEnds,hStyles,prep,hPacking₉,hStage₁₀,?_⟩
  let νR := (ν/8)^2/2
  let τR := 8*τ
  have hτ : 0 < τ := hν.trans_le hντ
  have hνR : 0 < νR := by dsimp only [νR]; positivity
  have hνsq : ν^2 ≤ ν := by nlinarith only [mul_nonneg hν.le (sub_nonneg.mpr hν₁)]
  have hνR₁ : νR ≤ 1/3 := by dsimp only [νR]; nlinarith only [hνsq,hν₁]
  have hνRτ : νR ≤ τR := by dsimp only [νR,τR]; nlinarith only [hνsq,hντ,hτ]
  have hf : 0 < f := Nat.pos_of_ne_zero (fun h => by simp [h] at hqf)
  have hFibre : ∀ i, fibreWeight parent univ i = f^2 := windingParent_fibres (f^2) k hk
  have hRobW : IsRealRobust R νR τR := by
    have h := fibrePullback_realRobust R₀ parent parent (f^2) hFibre hFibre (pow_pos hf 2)
      (ν/8) (4*τ) (by positivity) (by linarith only [hντ,hτ]) (by linarith only [hTau,hα₁,hτ])
      (by simpa only [Fintype.card_fin] using hOrder) hPart.reduced_expansion
    convert h using 1
    dsimp only [τR]
    ring
  have hWeight (x : ℕ) (hx : α*(k:ℝ) ≤ (x:ℝ)) : 2*τR*(n:ℝ) ≤ ((x*f^2:ℕ):ℝ) := by
    have hαR : 2*τR ≤ α := by dsimp only [τR]; linarith only [hτ,hTau]
    have h := mul_le_mul_of_nonneg_right hαR (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have h' := mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg (f^2) : (0:ℝ) ≤ ↑(f^2))
    dsimp only [n] at h ⊢
    push_cast at h h' ⊢
    linarith only [h,h']
  have hInW (i : Fin n) : 2*τR*(n:ℝ) ≤ (inDegree R i:ℝ) := by
    rw [(fibrePullback_semidegrees R₀ parent parent _ hFibre hFibre i).1]
    exact hWeight _ (hPart.reduced_in _)
  have hOutW (i : Fin n) : 2*τR*(n:ℝ) ≤ (outDegree R i:ℝ) := by
    rw [(fibrePullback_semidegrees R₀ parent parent _ hFibre hFibre i).2]
    exact hWeight _ (hPart.reduced_out _)
  have hTransfer (qR : ℕ) (h : n = qR) :
      let R' := fibrePullback R (finCongr h.symm) (finCongr h.symm)
      IsRealRobust R' νR τR ∧ (∀ i, 2*τR*(qR:ℝ) ≤ (inDegree R' i:ℝ)) ∧
        (∀ i, 2*τR*(qR:ℝ) ≤ (outDegree R' i:ℝ)) := by
    subst qR
    exact ⟨hRobW,hInW,hOutW⟩
  obtain ⟨hRob₈,hIn₈,hOut₈⟩ := hTransfer (l*(b₈*k)) hi₈
  have hWidth : 3 ≤ τR*((l*(b₈*k):ℕ):ℝ) := by
    have hkn : (k:ℝ) ≤ n := by exact_mod_cast Nat.le_mul_of_pos_left k (pow_pos hf 2)
    rw [←hi₈]
    dsimp only [τR]
    linarith only [hOrder,mul_le_mul_of_nonneg_left hkn (by positivity : 0 ≤ 8*τ)]
  have hSlotHost : 50*l+1 ≤ Fintype.card V := by
    have hBase : 0 < base := by rw [hB₈]; positivity
    exact hSlotOrder.trans ((Nat.le_mul_of_pos_right _ hBase).trans (hOrd ▸ card_le_univ Zᶜ))
  have hSlotZ : 2*(Z.card:ℝ) ≤ (Fintype.card V:ℝ)/((50*l+1:ℕ):ℝ) := by
    calc
      2*(Z.card:ℝ) ≤ 2*(ζ*(Fintype.card V:ℝ)) := mul_le_mul_of_nonneg_left hSizeZ (by norm_num)
      _ = (2*ζ)*(Fintype.card V:ℝ) := by ring
      _ ≤ (1/((50*l+1:ℕ):ℝ))*(Fintype.card V:ℝ) :=
        mul_le_mul_of_nonneg_right hZSlots (Nat.cast_nonneg _)
      _ = _ := by ring
  exact (process (b₈*k) j₈).choose_spec prep νR τR hN₈₅ hLoop hSlotHost hSlotZ hRouteMass hνR hνR₁ hνRτ hWidth
    (fun i => hPart.reduced_loopless (parent (toOriginal i))) hRob₈ hIn₈ hOut₈
    (by rw [←hi₈]; exact hEnds) hStyles

end OverfullWork.DirectedRobustExpansion
