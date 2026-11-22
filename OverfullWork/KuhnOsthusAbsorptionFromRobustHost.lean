module

public import OverfullWork.KuhnOsthusReservesFromRobustHost
public import OverfullWork.KuhnOsthusAssemblePhysicalReserves

@[expose] public section


/-! The exact reserve construction in Theorem 1.2, with the two
universal absorption properties needed after the approximate packing. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 1200000 in
/-- Construct the preprocessing graph and joint absorbing reserve
before the approximate packing is chosen. The resulting operators act
on every admissible remainder, as in Corollary 8.5 and Lemma 11.2. -/
theorem exists_kuhn_osthus_absorption_from_robust_host
    (ν τ α d θ : ℝ) (g : ℕ) (hg : 802 ≤ g)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hντ : ν ≤ τ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hTau : 64*τ ≤ α)
    (hd : 0 < d) (hdν : 8*d ≤ ν) (hdα : d ≤ α)
    (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₁ ζ : ℝ, 0 < d₁ ∧ 0 < ζ ∧ 32*ζ ≤ ν ∧ ζ ≤ (ν/4)^4 ∧
      22*d₁+4*ζ ≤ ν/2 ∧ 22*d₁+4*ζ ≤ α ∧
    ∀ ηMax : ℝ, 0 < ηMax →
    ∃ η : ℝ, 0 < η ∧ η ≤ ηMax ∧
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (r : ℕ),
      N ≤ Fintype.card V → IsRealRobust G ν τ → (8*α)*(Fintype.card V:ℝ) ≤ (r:ℝ) →
      (∀ v, inDegree G v = r ∧ outDegree G v = r) → (∀ v, ¬ G.Adj v v) →
      ∃ (Z : Finset V) (PG RB : Digraph V) (m b t : ℕ),
        let r₀ := ⌊η*(r:ℝ)⌋₊
        0 < r₀ ∧ m ≤ Fintype.card V ∧ r ≤ Fintype.card V ∧
        (Z.card:ℝ) ≤ ζ*(Fintype.card V:ℝ) ∧ b ≤ 22*⌊d₁*(m:ℝ)⌋₊ ∧
        PG ⊔ RB ≤ G ∧ Disjoint PG RB ∧
        (∀ v, inDegree (PG ⊔ RB) v = b ∧ outDegree (PG ⊔ RB) v = b) ∧
        (∀ x ∈ Z, ∀ y ∈ Z, (G \ (PG ⊔ RB)).Adj x y ↔ G.Adj x y) ∧
        (∀ D : Digraph V, D ≤ G \ (PG ⊔ RB) →
          (∀ v, inDegree D v = r₀ ∧ outDegree D v = r₀) →
          (∀ x y, x ∈ Z → y ∈ Z → ¬ D.Adj x y) →
          ∃ (s : ℕ) (C : Fin s → Equiv.Perm V), matchingUnion C ≤ PG ⊔ D ∧
            (∀ i, HasSpanningCycle (fun x y => C i x = y)) ∧
            (∀ i j, i ≠ j → ∀ v, C i v ≠ C j v) ∧
            let R := (PG ⊔ D) \ matchingUnion C
            (∀ x y, R.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
            ∀ v : ↥Zᶜ, inDegree (induced R Zᶜ) v = t ∧ outDegree (induced R Zᶜ) v = t) ∧
        ∀ H : Digraph V, H ≤ G \ RB → (∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z) →
          (∀ v : ↥Zᶜ, inDegree (induced H Zᶜ) v = t ∧ outDegree (induced H Zᶜ) v = t) →
          ∃ (s : ℕ) (C : Fin s → Equiv.Perm V), matchingUnion C = H ⊔ RB ∧
            (∀ i, HasSpanningCycle (fun x y => C i x = y)) ∧
            ∀ i j, i ≠ j → ∀ v, C i v ≠ C j v := by
  let μ := (ν/8)^2/2
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hμ₁ : μ ≤ 1 := by
    dsimp only [μ]
    have h := mul_self_le_mul_self (show 0 ≤ ν/8 by positivity) (show ν/8 ≤ 1 by linarith only [hν₁])
    nlinarith only [h]
  obtain ⟨l,hl,hSlot,_⟩ := exists_kuhn_osthus_preprocessing_slot_count μ hμ hμ₁
  let L := ⌈25/μ^2⌉₊+4
  obtain ⟨d₁,hd₁,hd₁d,_,εC,hεC,hεCB,hReserves⟩ :=
    exists_kuhn_osthus_reserves_from_robust_host.{u} ν τ α d θ d 1 l g L
      hν hν₁ hντ hα hα₁ hTau hd hdν hdα hθ hθ₁ hd (by norm_num) hl (by omega) le_rfl hSlot
  have hd₁₁ : d₁ ≤ 1 := by linarith only [hd₁d,hdν,hν₁]
  obtain ⟨fMin,hFMin⟩ := exists_kuhn_osthus_absorption_winding_threshold d₁ hd₁ (L+1) g
  obtain ⟨NA,hA⟩ := kuhn_osthus_lemma_11_2_from_physical_reserves.{u} d₁ hd₁ hd₁₁
  let unit := ((1/1000:ℝ)*((d/2)/4))^2
  let εP := min (1/100:ℝ) (unit/800)
  have hUnit : 0 < unit := by dsimp only [unit]; positivity
  have hεP : 0 < εP := lt_min (by norm_num) (by positivity)
  have hεPScale : 800*εP ≤ unit := by
    have h : εP ≤ unit/800 := min_le_right _ _
    linarith only [h]
  have hWind := hReserves fMin 1 (1:ℝ) εP (by norm_num : (0:ℝ) < 1)
    hεP (show εP ≤ 1/100 from min_le_left _ _) hεPScale
  obtain ⟨f,q,b₈,b₁₀,w₈,w₉,w₁₀,hWind⟩ := hWind
  obtain ⟨hfMin,hqMin,hgf,hfq,hqf,hqEq,hRatio,hWind⟩ := hWind
  obtain ⟨ζ,ε,ξ,σ₈,σ₉,σ₁₀,hζ,hζMax,hζHalf,hε,hξ,hξCap,hσ₈,hσ₈d,hσ₉,hσ₁₀,
    hZSlots,hZν,hZPow,hZν',hZα,J,hJ,hSchedule⟩ := hWind
  obtain ⟨hF300,hFine,hFoot,hScale⟩ := hFMin f hfMin
  refine ⟨d₁,ζ,hd₁,hζ,hZν,hZPow,hZν',hZα,?_⟩
  intro ηMax hηMax
  obtain ⟨d₃,c,η,d₀,ηS,hd₃,hc,hη,hc₃,hd₃Cap,hηCap,hd₀,hηS,hηS',hHost⟩ :=
    hSchedule d (fun _ _ => ηMax) hd (fun _ _ _ _ => hηMax)
  let T : ℕ := max NA (max 1 (24*f))
  obtain ⟨N,hN⟩ := hHost T
  refine ⟨η,hη,hηCap,N,?_⟩
  intro V _ G r hNlarge hRob hDense hReg hLoop
  have hData := hN G r hNlarge hRob hDense hReg hLoop
  obtain ⟨k,m,base,m₈,m₉,mWalk,hk,Z₀,Z,P,R₀,A,X,routes,F,hData⟩ := hData
  obtain ⟨r₃,j₈,j₉,j₁₀,hData⟩ := hData
  obtain ⟨hB₈,hB₉,hBQ,hBW,hT₈,hT₉,hTW,hTB,hnJ,h14,hQDiv,hDiv,hPart,hSizeZ,hData⟩ := hData
  obtain ⟨hRegPairs,hSup,hFirst,hF,hRoutes,hMult,hWalk',hData⟩ := hData
  obtain ⟨hR₀,hR₀c,hPre,hpK,hr₁,hSparse,hChord,hQr,hR₂,hR₃,hBal,hSpend,hTot,hOrd,hEnds,hStyles,hData⟩ := hData
  obtain ⟨prep,E₉,order,c₉,B,Q,M,hData⟩ := hData
  obtain ⟨hStep,hCoord,hCard,hCA,hKeep,hSep,hApart,hBaseCycle,hBaseSupport,hQCover,hQParent,hQSize,hQDis,hM,hDegree,hData⟩ := hData
  obtain ⟨E₁₀,c₁₀,PS,LS,TS,hData⟩ := hData
  obtain ⟨hPCoord,hPC,hPKeep,hPReg,hPAbs,hPApart,hPEq,hTDeg,hPSDeg,
    hAbsLe,hDisPG,hDisCA,hRegAbs,hInternal,hProcess⟩ := hData
  let n := f^2*k
  have hi₉ : n = f*(f*k) := by dsimp only [n]; rw [w₉,Nat.mul_assoc]
  let e₉ := finCongr hi₉.symm
  let Y (i : Fin (f*(f*k))) := X (e₉ i)
  let a := 50*l*⌊η*(r:ℝ)⌋₊
  let p := ⌊d₃*(base:ℝ)⌋₊
  let t := p-a
  let r₁ := ⌊d₁*(base:ℝ)⌋₊
  let r₂ := 96*(L+1)*g^2*n*t
  let s := r₁+r₂+t-(q-1)*r₃
  let sub := Function.Embedding.subtype (· ∈ Zᶜ)
  let U := liftDirectedPair sub sub
    (successorCellMatchingUnion Q ((finRotate ((L+1)*n)).prodCongr (Equiv.refl (Fin 4))) M)
  let EF := ⨆ i, ⨆ j, (E₉.factors i j).digraph
  let CA := (U ⊔ EF) ⊔ liftDirectedPair sub sub B
  let e₁₀ := (exceptionalCoordinates Z).toEmbedding
  let PC := liftDirectedPair e₁₀ e₁₀ (⨆ i, PS i)
  let RB := CA ⊔ PC
  have hAlign (v : ↥Zᶜ) : c₉ v = finCongr hi₉ (c₁₀ v) := by
    apply (hCoord _ v).mpr
    change v.val ∈ X (e₉ (finCongr hi₉ (c₁₀ v)))
    rw [show e₉ (finCongr hi₉ (c₁₀ v)) = c₁₀ v from (finCongr hi₉).symm_apply_apply _]
    exact (hPCoord _ v).mp rfl
  have hTBase : 24*f ≤ base := (le_max_right _ _).trans ((le_max_right _ _).trans hTB)
  have hfBase : f ≤ base := (Nat.le_mul_of_pos_left _ (by decide : 0 < 24)).trans hTBase
  have hgPos : 0 < g := by omega
  have hLarge : 24*f ≤ 8*g^2*base := hTBase.trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hmWalk : 0 < mWalk := (le_max_left _ _).trans ((le_max_right _ _).trans hTW)
  have hf : 0 < f := (by decide : 0 < 300).trans_le hF300
  have hn : 0 < n := Nat.mul_pos (pow_pos hf 2) hk
  have hBase : 0 < base := hf.trans_le hfBase
  have hBaseCard : base ≤ Fintype.card V :=
    (Nat.le_mul_of_pos_left _ hn).trans (by rw [←hOrd]; exact card_le_univ _)
  let first : Fin n := ⟨0,hn⟩
  have hNonempty : (X first).Nonempty := card_pos.mp (by rw [(hPart.fine_size first).1]; exact hBase)
  obtain ⟨v,_⟩ := hNonempty
  have hr : r ≤ Fintype.card V := (hReg v).2.symm ▸ DirectedArcSelection.outDegree_le G v
  refine ⟨Z,prep.graph,RB,base,p+r₁+r₂+r₃+6*s,t,hR₀,hBaseCard,hr,hSizeZ,hTot,hAbsLe,hDisPG,hRegAbs,hInternal,
    hProcess RB,?_⟩
  intro H hH hSupp hDeg
  obtain ⟨C,hCov,hCyc,hApartC⟩ := hA G prep.graph Z hi₉ j₉ Y c₉ c₁₀ routes F order B Q M σ₉ εC E₉ PS LS
      hg hgf (by omega) hmWalk hF300 hFine hfBase hLarge hFoot hScale hBW hB₉ hRatio
      hqEq hQDiv hDiv (by dsimp only [r₂]; ring) hChord hQr hSparse
      ((le_max_left _ _).trans hTB) hεC.le hεCB hLoop prep.le_host hCA prep.degree hDegree hSep hApart
      hCoord (fun i => hPart.fine_ordinary (e₉ i)) hAlign hCard hBaseCycle hBaseSupport
      hQCover hQParent hQSize hQDis hM hStep (fun i => (hRoutes i).1.2) hMult hPAbs hPApart hPSDeg
      H hH hSupp hDeg
  exact ⟨_,C,hCov,hCyc,hApartC⟩

end OverfullWork.DirectedRobustExpansion
