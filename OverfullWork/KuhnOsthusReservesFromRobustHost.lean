module

public import OverfullWork.KuhnOsthusChordOnCommonPartition
public import OverfullWork.KuhnOsthusPreprocessedHost
public import OverfullWork.KuhnOsthusParityOnCommonPartition

@[expose] public section


/-! Construct the three physical reserves in the order of §11. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 4800000 in
/-- The preprocessed robust host supplies the physical cycle base and
the universal walk bank. The third exceptional packing is then built
after both physical reserves have been deleted. Lemma 10.5 extends
that packing to the parity reserve, and (11.14) balances the union. -/
theorem exists_kuhn_osthus_reserves_from_robust_host
    (ν τ α d θ d₁Max ζMax : ℝ) (l g L : ℕ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hντ : ν ≤ τ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hTau : 64*τ ≤ α)
    (hd : 0 < d) (hdν : 8*d ≤ ν) (hdα : d ≤ α)
    (hθ : 0 < θ) (hθ₁ : θ < 1) (hd₁Max : 0 < d₁Max) (hζMax : 0 < ζMax)
    (hl : 2 ≤ l) (hg : 2 ≤ g) (hWalk : ⌈25/((ν/8)^2/2)^2⌉₊+4 ≤ L)
    (hRouteMass : (10^7:ℝ) ≤ ((50*l+1:ℕ):ℝ)*((ν/8)^2/2)^2) :
    ∃ d₁ : ℝ, 0 < d₁ ∧ d₁ < d ∧ d₁ ≤ d₁Max ∧
    ∃ εC : ℝ, 0 < εC ∧ εC ≤ d₁/512 ∧
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
            ∃ (E₉ : WoundFactorPacking (G \ prep.graph) Z X₉ j₉ (q/f) m₉ r₃ σ₉)
              (order : Fin ((L+1)*n) ≃ Fin (L+1) × Fin n) (c₉ : ↥Zᶜ → Fin (f*(f*k)))
              (B : Digraph ↥Zᶜ) (Q : Fin ((L+1)*n) × Fin 4 → Finset ↥Zᶜ)
              (M : ∀ i, Fin r₂ → Q i ≃ Q (((finRotate ((L+1)*n)).prodCongr (Equiv.refl (Fin 4))) i)),
            let next := finRotate (f*(f*k))
            let sub := Function.Embedding.subtype (· ∈ Zᶜ)
            let C (i : Fin (f*(f*k))) := (univ : Finset ↥Zᶜ).filter (fun v => c₉ v = i)
            let baseCycle := liftDirectedPair sub sub B
            let bank := liftDirectedPair sub sub
              (successorCellMatchingUnion Q ((finRotate ((L+1)*n)).prodCongr (Equiv.refl (Fin 4))) M)
            let EF := ⨆ i, ⨆ j, (E₉.factors i j).digraph
            let CA := (bank ⊔ EF) ⊔ baseCycle
            (∀ i, (order (finRotate ((L+1)*n) i)).2 = F (order i).1 (order i).2) ∧
            (∀ i v, c₉ v = i ↔ v.val ∈ X₉ i) ∧ (∀ i, (C i).card = base) ∧
            CA ≤ G \ prep.graph ∧ EF ≤ CA ∧ Disjoint bank EF ∧ Disjoint (bank ⊔ EF) baseCycle ∧
            (∀ i, IsSuperregularPair (induced baseCycle Zᶜ) εC d₁ (C i) (C (next i))) ∧
            (∀ x y, baseCycle.Adj x y → ∃ u v : ↥Zᶜ, u.val = x ∧ v.val = y ∧ c₉ v = next (c₉ u)) ∧
            (∀ v, ∃ i, v ∈ Q i) ∧ (∀ i v, v ∈ Q i → c₉ v = finCongr i₉ (order i.1).2) ∧
            (∀ i, (Q i).card = mWalk) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
            (∀ i p z, p ≠ z → ∀ x, M i p x ≠ M i z x) ∧
            (∀ x, let D := if x ∈ Z then q*r₃ else r₁+r₂+r₃
              inDegree CA x = D ∧ outDegree CA x = D) ∧
            ∃ (E₁₀ : WoundFactorPacking (G \ (prep.graph ⊔ CA)) Z X₁₀ j₁₀ 1 base s σ₁₀)
              (c₁₀ : ↥Zᶜ → Fin n) (PS : Fin s → Digraph (↥Zᶜ ⊕ ↥Z))
              (LS : Fin s → Fin 7 → Digraph (↥Zᶜ ⊕ ↥Z)) (TS : Digraph ↥Zᶜ),
            let A₁₀ (i : Fin n) := (univ : Finset ↥Zᶜ).filter (fun x => c₁₀ x = i)
            let e₁₀ := (exceptionalCoordinates Z).toEmbedding
            let PC := liftDirectedPair e₁₀ e₁₀ (⨆ i, PS i)
            let EParity := ⨆ i, ⨆ j, (E₁₀.factors i j).digraph
            let Gabs := prep.graph ⊔ (CA ⊔ PC)
            (∀ i v, c₁₀ v = i ↔ v.val ∈ X i) ∧
            PC ≤ G \ (prep.graph ⊔ CA) ∧ EParity ≤ PC ∧
            (∀ x, let D := if x ∈ Z then 7*s else 6*s; inDegree PC x = D ∧ outDegree PC x = D) ∧
            (∀ i, PS i ≤ pullDirectedPair e₁₀ e₁₀ (G \ (prep.graph ⊔ CA)) ∧ AbsorbsWindingFactor A₁₀ (PS i) (LS i)) ∧
            Pairwise (fun i j => Disjoint (PS i) (PS j)) ∧
            (⨆ i, PS i) = liftOrdinaryCycleArcs (↥Z) TS ⊔ pullDirectedPair e₁₀ e₁₀ EParity ∧
            (∀ x, inDegree TS x = 5*s ∧ outDegree TS x = 5*s) ∧
            (∀ v, let D := match v with | .inl _ => 6*s | .inr _ => 7*s
              inDegree (⨆ i, PS i) v = D ∧ outDegree (⨆ i, PS i) v = D) ∧
            Gabs ≤ G ∧ Disjoint prep.graph (CA ⊔ PC) ∧ Disjoint CA PC ∧
            (∀ x, inDegree Gabs x = p+r₁+r₂+r₃+6*s ∧ outDegree Gabs x = p+r₁+r₂+r₃+6*s) ∧
            (∀ x ∈ Z, ∀ y ∈ Z, (G \ Gabs).Adj x y ↔ G.Adj x y) ∧
            ∀ B H : Digraph V, H ≤ G \ (prep.graph ⊔ B) →
              (∀ v, inDegree H v = r₀ ∧ outDegree H v = r₀) →
              (∀ x y, x ∈ Z → y ∈ Z → ¬ H.Adj x y) →
              ∃ (a : ℕ) (C : Fin a → Equiv.Perm V), matchingUnion C ≤ prep.graph ⊔ H ∧
                (∀ i, HasSpanningCycle (fun x y => C i x = y)) ∧
                (∀ i j, i ≠ j → ∀ v, C i v ≠ C j v) ∧
                let Remainder := (prep.graph ⊔ H) \ matchingUnion C
                (∀ x y, Remainder.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
                ∀ v : ↥Zᶜ, inDegree (induced Remainder Zᶜ) v = t ∧ outDegree (induced Remainder Zᶜ) v = t := by
  have hd₁ : d ≤ 1 := by linarith only [hdν,hν₁,hd]
  obtain ⟨densityCap,hDensityCap,hChord⟩ :=
    exists_kuhn_osthus_chord_on_common_partition.{u} d (L+1) hd hd₁ (by omega)
  obtain ⟨parityCap,ξParity,hParCap,hξParity,hParity⟩ :=
    exists_kuhn_osthus_parity_on_common_partition.{u} d hd hd₁
  obtain ⟨d₁,hd₁Pos,hd₁d,hd₁Max',hStage⟩ :=
    exists_kuhn_osthus_preprocessed_robust_host.{u} ν τ α d θ (min d₁Max (min densityCap parityCap)) ζMax l g L
      hν hν₁ hντ hα hα₁ hTau hd hdν hdα hθ hθ₁ (lt_min hd₁Max (lt_min hDensityCap hParCap)) hζMax hl hg hWalk hRouteMass
  obtain ⟨ξCap,εC,hξCap,hεC,hεCB,hChordReady⟩ := hChord d₁ hd₁Pos (hd₁Max'.trans ((min_le_right _ _).trans (min_le_left _ _))) hd₁d
  refine ⟨d₁,hd₁Pos,hd₁d,hd₁Max'.trans (min_le_left _ _),εC,hεC,hεCB,?_⟩
  intro fMin qMin target εP hTarget hεP hεP₁ hεPScale
  obtain ⟨f,q,b₈,b₁₀,w₈,w₉,w₁₀,hfMin,hqMin,hgf,hfq,hqf,hqEq,hRatio,ζ,ε,ξ,σ₈,σ₉,σ₁₀,
    hζ,hζMax',hζHalf,hε,hξ,hξCap',hσ₈,hσ₈d,hσ₉,hσ₁₀,hZSlots,hZν,hZPow,hZν',hZα,J,hJ,hSchedule⟩ :=
    hStage (max fMin 15) qMin (min target (min ξCap ξParity)) εP (lt_min hTarget (lt_min hξCap hξParity)) hεP hεP₁ hεPScale
  obtain ⟨dCap,hdCap,T₉,hReserve⟩ := hChordReady J ξ hJ hξ (hξCap'.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨T₁₀,hParityReady⟩ := hParity J
  refine ⟨f,q,b₈,b₁₀,w₈,w₉,w₁₀,(le_max_left _ _).trans hfMin,hqMin,hgf,hfq,hqf,hqEq,hRatio,ζ,ε,ξ,σ₈,σ₉,σ₁₀,
    hζ,hζMax',hζHalf,hε,hξ,hξCap'.trans (min_le_left _ _),hσ₈,hσ₈d,hσ₉,hσ₁₀,
    hZSlots,hZν,hZPow,hZν',hZα,J,hJ,?_⟩
  intro d₃Max ηMax hd₃Max hηMax
  obtain ⟨d₃,c,η,d₀,ηS,hd₃,hc,hη,hc₃,hd₃Cap,hηCap,hd₀,hηS,hηS',hHost⟩ :=
    hSchedule (min d₃Max dCap) ηMax (lt_min hd₃Max hdCap) hηMax
  refine ⟨d₃,c,η,d₀,ηS,hd₃,hc,hη,hc₃,hd₃Cap.trans (min_le_left _ _),hηCap,hd₀,hηS,hηS',?_⟩
  intro T
  obtain ⟨N,hN⟩ := hHost (max T (max T₉ T₁₀))
  refine ⟨N,?_⟩
  intro V _ G r hNlarge hRob hMin hRegular hLoop
  obtain ⟨k,m,base,m₈,m₉,mWalk,hk,Z₀,Z,P,R₀,A,X,routes,F,r₃,j₈,j₉,j₁₀,
    hB₈,hB₉,hBQ,hBW,hT₈,hT₉,hTW,hTB,hnJ,h14,hStyleDiv,hDiv,hPart,hSizeZ,hReg,hSup,hFirst,hF,hRoutes,hMult,hWalk',
    hR₀,hR₀c,hSum,hpK,hr₁,hSparse,hChordEq,hQr,hR₂,hR₃,hBal,hSpend,hTot,hOrd,hEnds,hStyles,
    prep,⟨E₉⟩,hStage₁₀,hProcess⟩ := hN G r hNlarge hRob hMin hRegular hLoop
  let n := f^2*k
  have hi₉ : n = f*(f*k) := by dsimp only [n]; rw [w₉,Nat.mul_assoc]
  let r₀ := ⌊η*(r:ℝ)⌋₊
  let p := ⌊d₃*(base:ℝ)⌋₊
  let a := 50*l*r₀
  let t := p-a
  let r₁ := ⌊d₁*(base:ℝ)⌋₊
  let r₂ := 96*(L+1)*g^2*n*t
  have hHalf : 2*Z.card ≤ Fintype.card V := by
    exact_mod_cast (show (2:ℝ)*(Z.card:ℝ) ≤ Fintype.card V by
      linarith only [hSizeZ,mul_le_mul_of_nonneg_right hζHalf (Nat.cast_nonneg (Fintype.card V))])
  have hLoss (x : V) (hx : x ∉ Z) :
      inDegree prep.graph x ≤ p ∧ outDegree prep.graph x ≤ p := by
    have h := prep.degree x
    rw [if_neg hx] at h
    change inDegree prep.graph x = a+t ∧ outDegree prep.graph x = a+t at h
    rw [show a+t = p from hSum] at h
    exact ⟨h.1.le,h.2.le⟩
  have hChordCount : t*(f*n) = ((q/f)*f)*r₃ := by rw [hqEq]; exact hChordEq
  have hCycle (i : Fin n) : IsLowerSuperregularPair G ξ d (X i) (X (finRotate n i)) := by
    rw [←hFirst]
    exact hSup 0 i
  obtain ⟨order,c₉,B,Q,M,hStep,hCoord,hCard,hCA,hKeep,hSep,hApart,hBaseCycle,hBaseSupport,hQCover,
    hQParent,hQSize,hQDis,hM,hDegree⟩ := hReserve G prep.graph Z X F hi₉ j₉ base mWalk m₉ p t r₂ r₃ d₃ σ₉
      ((by decide : 2 ≤ 15).trans ((le_max_right _ _).trans hfMin)) hqf hnJ prep.le_host hLoss hd₃.le (hd₃Cap.trans (min_le_right _ _))
      rfl (Nat.sub_le _ _) hChordCount hR₂ hR₃ hHalf hOrd ((le_max_left _ _).trans ((le_max_right _ _).trans hTW))
      ((le_max_left _ _).trans ((le_max_right _ _).trans hTB)) hBW (fun i => (hPart.fine_size i).1) hPart.fine_disjoint
      hPart.fine_ordinary hPart.fine_cover hWalk' hSup hCycle E₉
  let sub := Function.Embedding.subtype (· ∈ Zᶜ)
  let bank := liftDirectedPair sub sub
    (successorCellMatchingUnion Q ((finRotate ((L+1)*n)).prodCongr (Equiv.refl (Fin 4))) M)
  let EF := ⨆ i, ⨆ j, (E₉.factors i j).digraph
  let CA := (bank ⊔ EF) ⊔ liftDirectedPair sub sub B
  simp only [hqEq] at hDegree
  obtain ⟨hLe,_,_,hOrdLoss,hExcLoss,_⟩ := wound_exceptional_stage_degrees G prep.graph CA Z a t q r₁ r₂ r₃
    prep.le_host hCA (hQr.trans (by omega)) prep.degree hDegree
  have hE₁₀ := hStage₁₀ (prep.graph ⊔ CA) hLe hOrdLoss
    (fun x hx => ⟨(hExcLoss x hx).1.le,(hExcLoss x hx).2.le⟩)
  obtain ⟨E₁₀⟩ := hE₁₀
  let s := r₁+r₂+t-(q-1)*r₃
  have hi₁₀ : n = 7*(b₁₀*k) := by dsimp only [n]; rw [w₁₀,Nat.mul_assoc]
  have hf15 : 15 ≤ f := (le_max_right _ _).trans hfMin
  have hN210 : 210 ≤ n := (by decide : 210 ≤ 15^2).trans
    ((Nat.pow_le_pow_left hf15 2).trans (Nat.le_mul_of_pos_right _ hk))
  have hNPos : 0 < n := by omega
  have hp₁ : p ≤ r₁ := (Nat.le_mul_of_pos_right p (pow_pos hNPos 2)).trans hpK
  have hPre : a+t = p := hSum
  have hLossBound : a+t+r₁+r₂+r₃ ≤ 4*r₁ := by
    rw [hPre]
    calc
      p+r₁+r₂+r₃ ≤ r₁+r₁+r₁+r₁ := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp₁ le_rfl) hR₂) hR₃
      _ = 4*r₁ := by ring
  have htP : t ≤ p := Nat.sub_le _ _
  have hs₁ : s ≤ 3*r₁ := by
    calc
      s ≤ r₁+r₂+t := Nat.sub_le _ _
      _ ≤ r₁+r₁+r₁ := Nat.add_le_add (Nat.add_le_add le_rfl hR₂) (htP.trans hp₁)
      _ = 3*r₁ := by ring
  have hBaseEven : ∃ m, base = 2*m := ⟨2*(L+1)*mWalk,hBW.trans (by ring)⟩
  obtain ⟨c₁₀,PS,LS,TS,hPCoord,hPC,hPKeep,hPReg,hPAbs,hPApart,hPEq,_,hTDeg,hPSDeg⟩ :=
    hParityReady G (prep.graph ⊔ CA) Z X hi₁₀ j₁₀ ξ σ₁₀ d₁ hN210 hnJ h14
      ((le_max_right _ _).trans ((le_max_right _ _).trans hTB)) hBaseEven
      hd₁Pos.le (hd₁Max'.trans ((min_le_right _ _).trans (min_le_right _ _))) hξ.le
      (hξCap'.trans ((min_le_right _ _).trans (min_le_right _ _))) hLossBound hs₁ hLe
      (fun x _ => hOrdLoss x) (fun i => (hPart.fine_size i).1) hPart.fine_disjoint
      hPart.fine_ordinary hPart.fine_cover hCycle E₁₀
  let e₁₀ := (exceptionalCoordinates Z).toEmbedding
  let PC := liftDirectedPair e₁₀ e₁₀ (⨆ i, PS i)
  have hJoin : CA ⊔ PC ≤ G \ prep.graph := sup_le hCA
    (fun _ _ h => ⟨(hPC h).1,fun hp => (hPC h).2 (Or.inl hp)⟩)
  have hDisPG : Disjoint prep.graph (CA ⊔ PC) :=
    disjoint_iff_inf_le.mpr (fun _ _ h => (hJoin h.2).2 h.1)
  have hDisCA : Disjoint CA PC := disjoint_iff_inf_le.mpr (fun _ _ h => (hPC h.2).2 (Or.inr h.1))
  have hRB (x : V) : let d := if x ∈ Z then q*r₃+7*s else r₁+r₂+r₃+6*s
      inDegree (CA ⊔ PC) x = d ∧ outDegree (CA ⊔ PC) x = d := by
    obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint CA PC (disjoint_iff_inf_le.mp hDisCA) x
    rw [hi,ho,(hDegree x).1,(hDegree x).2,(hPReg x).1,(hPReg x).2]
    by_cases hx : x ∈ Z <;> simp [hx,r₁]
  have hQPos : 0 < q := hqEq ▸ Nat.mul_pos hqf (by omega)
  have hGR := kuhn_osthus_balanced_absorption_reserve prep.graph (CA ⊔ PC) Z a t r₁ r₂ r₃ q s
    hQPos hBal hDisPG prep.degree hRB
  have hRegAbs (x : V) :
      inDegree (prep.graph ⊔ (CA ⊔ PC)) x = p+r₁+r₂+r₃+6*s ∧
      outDegree (prep.graph ⊔ (CA ⊔ PC)) x = p+r₁+r₂+r₃+6*s := by
    have h := hGR x
    rw [hPre] at h
    exact h
  have hInternal := kuhn_osthus_internal_arcs_after_three_reserves G prep.graph CA PC prep.pack E₉ E₁₀
    prep.contains_factors hKeep hPKeep
    (fun x hx => by simpa only [if_pos hx] using (prep.degree x).2)
    (fun x hx => by simpa only [if_pos hx,hqEq] using (hDegree x).2)
    (fun x hx => by simpa only [if_pos hx] using (hPReg x).2)
  have hT : T ≤ max T (max T₉ T₁₀) := le_max_left _ _
  exact ⟨k,m,base,m₈,m₉,mWalk,hk,Z₀,Z,P,R₀,A,X,routes,F,r₃,j₈,j₉,j₁₀,hB₈,hB₉,hBQ,hBW,
    hT.trans hT₈,hT.trans hT₉,hT.trans hTW,hT.trans hTB,hnJ,h14,hStyleDiv,hDiv,hPart,hSizeZ,hReg,hSup,
    hFirst,hF,hRoutes,hMult,hWalk',hR₀,hR₀c,hSum,hpK,hr₁,hSparse,hChordEq,hQr,hR₂,hR₃,hBal,hSpend,hTot,
    hOrd,hEnds,hStyles,prep,E₉,order,c₉,B,Q,M,hStep,hCoord,hCard,hCA,hKeep,hSep,hApart,
    hBaseCycle,hBaseSupport,hQCover,hQParent,hQSize,hQDis,hM,hDegree,
    E₁₀,c₁₀,PS,LS,TS,hPCoord,hPC,hPKeep,hPReg,hPAbs,hPApart,hPEq,hTDeg,hPSDeg,
    sup_le prep.le_host (fun _ _ h => (hJoin h).1),hDisPG,hDisCA,hRegAbs,hInternal,hProcess⟩

end OverfullWork.DirectedRobustExpansion
