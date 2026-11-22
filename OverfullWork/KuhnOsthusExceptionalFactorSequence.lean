module

public import OverfullWork.KuhnOsthusExceptionalStageBudgets
public import OverfullWork.KuhnOsthusFinalAssembly

@[expose] public section


/-! Run the three original exceptional-factor constructions in the
successive physical complements used in the proof of Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

/-- The cells and intervals of Lemma 7.6 on a particular winding, with
the support and degrees of the original arcs retained. -/
structure WoundFactorPacking {V : Type*} [Fintype V] {l j : ℕ}
    (G : Digraph V) (Z : Finset V) (X : Fin (l*j) → Finset V) (hj : 0 < j)
    (K m r : ℕ) (σ : ℝ) where
  cell : Fin K × Fin (l*j) → Finset V
  size : ∀ i, (cell i).card = m ∧ cell i ⊆ X i.2
  disjoint : ∀ i i', i ≠ i' → Disjoint (cell i) (cell i')
  cover : ∀ i, (univ : Finset (Fin K)).biUnion (fun a => cell (a,i)) = X i
  profiles : ∀ i, UniformProfileCell (inProfile G) (X i.2) (cell i) K σ ∧
    UniformProfileCell (outProfile G) (X i.2) (cell i) K σ
  factors :
    let U (a : Fin K × Fin l) := (univ : Finset (Fin j)).biUnion
      (fun i => cell (a.1,intervalPosition a.2 i))
    let S (a : Fin K × Fin l) := cell (a.1,intervalPosition a.2 ⟨0,hj⟩)
    let next := (Equiv.refl (Fin K)).prodCongr (finRotate l)
    Fin r → ∀ a, OriginalInterval G Z (U a ∪ S (next a)) (S a) (S (next a))
  apart : Pairwise (fun i i' => Disjoint (⨆ a, (factors i a).digraph) (⨆ a, (factors i' a).digraph))
  degrees : ∀ v, let d := if v ∈ Z then K*l*r else r
    inDegree (⨆ i, ⨆ a, (factors i a).digraph) v = d ∧
      outDegree (⨆ i, ⨆ a, (factors i a).digraph) v = d

/-- The factor construction is applicable uniformly after any deletion
within the prescribed semidegree bounds, with the exceptional bound
kept separately. -/
def WoundFactorStage {V : Type*} [Fintype V] {l j : ℕ}
    (G : Digraph V) (Z : Finset V) (X : Fin (l*j) → Finset V) (hj : 0 < j)
    (K m r loss priorLoss : ℕ) (σ : ℝ) : Prop :=
  ∀ H : Digraph V, H ≤ G →
    (∀ v, inDegree H v ≤ loss ∧ outDegree H v ≤ loss) →
    (∀ z ∈ Z, inDegree H z ≤ priorLoss ∧ outDegree H z ≤ priorLoss) →
    Nonempty (WoundFactorPacking (G \ H) Z X hj K m r σ)

set_option maxHeartbeats 850000 in
/-- Prepare one complete call to Lemma 7.6 before the earlier reserves
have been chosen. Only their degree bounds enter the shared numerical
margins. The original graph, clusters and reduced graph are fixed. -/
theorem kuhn_osthus_wound_factor_stage
    (B σ d δ ε ν τ γ : ℝ) (hB : 0 < B) (hσ : 0 < σ)
    (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hDensity : 6*ε ≤ d)
    (hCost : ν ≤ (d-2*ε)*τ) (hFloor : γ ≤ d-2*ε) (hTol : 4*δ ≤ ε)
    (K c : ℕ) (hK : 0 < K) (hc : 32 ≤ c) (hScaleCap : 20 ≤ (c:ℝ)*ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {l b k n L : ℕ}
      (G : Digraph V) (Z₀ Z : Finset V) (P : Fin k → Finset V)
      (A X : Fin n → Finset V) (R₀ : Digraph (Fin k))
      (_hl : 2 ≤ l) (hb : 0 < b) (hk : 0 < k)
      (hIndex : n = l*(b*k)) (_hWinding : L = l*b)
      (m M r loss priorLoss : ℕ) (α θ εOld μ τ₀ a η ξ β : ℝ),
      let parent := windingParent (n := n) k hk
      let R := fibrePullback R₀ parent parent
      let Y (i : Fin (l*(b*k))) := X (finCongr hIndex.symm i)
      WoundExceptionalPartition G Z₀ Z P A X R₀ hk L M (K*m) α θ εOld μ τ₀ →
      0 < M → 2*N ≤ m → 2*c ≤ m → 1 ≤ ε*(m:ℝ) →
      4*(Fintype.card V:ℝ) ≤ B*((K*m:ℕ):ℝ) →
      0 ≤ β → 2*(ξ+β) ≤ σ → (loss:ℝ) ≤ β*(((K*m:ℕ):ℝ)*σ) →
      (∀ i j, R.Adj i j → IsUniform G ξ (X i) (X j) ∧ d+(ξ+β) ≤ density G (X i) (X j)) →
      (∀ i, IsLowerSuperregularPair G ξ d (X i) (X (finRotate n i))) →
      0 ≤ α → 0 ≤ θ → τ₀ ≤ α/3 → εOld ≤ τ₀ → θ ≤ 1-εOld → σ ≤ 1 → σ ≤ θ*(α/3) →
      (((4*c+2)*Z.card+K*l*r+priorLoss:ℕ):ℝ) <
        (α/3*(k:ℝ))*((b-3:ℕ):ℝ)*((1-σ)*(θ*(α/3)*(m:ℝ))) →
      0 < μ → μ ≤ τ₀ → τ₀ ≤ 1/4 → 2 ≤ τ₀*(k:ℝ) →
      8 ≤ (μ^2/2)*((b*k:ℕ):ℝ) →
      (2*τ₀+(μ^2/2)/2)*((b*k:ℕ):ℝ)+2 ≤ α*((b*k:ℕ):ℝ) →
      (Z.card:ℝ)*(8/(μ^2/2)+6) <
        ((m:ℝ)/(2*(c:ℝ)))*((μ^2/2)*((b*k:ℕ):ℝ)/16) →
      0 ≤ a → 0 < η → η ≤ 1/4 → K*σ ≤ η → 2*(σ+a) ≤ η →
      (r:ℝ) ≤ a*((m:ℝ)*η) → η < d-σ-a →
      0 < δ → δ ≤ 1 → 2*σ ≤ d → 2*(max 2 (K:ℝ)*σ+a) ≤ δ →
      (r:ℝ) ≤ a*((m:ℝ)*δ) →
      WoundFactorStage G Z Y (Nat.mul_pos hb hk) K m r loss priorLoss σ := by
  obtain ⟨N,hN⟩ := kuhn_osthus_exceptional_factors_from_common_partition.{u}
    B σ d δ ε ν τ γ hB hσ hν hWidth hε hε₁ hτγ hγ hDensity hCost hFloor hTol K c hK hc hScaleCap
  refine ⟨N,?_⟩
  intro V _ l b k n L G Z₀ Z P A X R₀ hl hb hk hIndex hWinding m M r loss priorLoss
    α θ εOld μ τ₀ a η ξ β parent R Y hPart hM hNm hm hLarge hProfile hβ hTolβ hLossβ
    hReg hSup hα hθ hτ₀α hεOld hθε hσ₁ hStyle hDemand hμ hμτ hτ₀ hOrder hLargeR hDegreeR
    hLoad ha hη hη₁ hScale hCTol hCLoss hGap hδ hδ₁ hFloor' hSTol hSLoss H hHG hLoss hPrior
  obtain ⟨C,hSize,hDis,hCover,hProfiles,F,hApart,_,hDegrees⟩ :=
    hN G H Z₀ Z P A X R₀ hl hb hk hIndex hWinding m M r loss priorLoss α θ εOld μ τ₀ a η ξ β
      hPart hHG hM hNm hm hLarge hProfile hLoss hPrior hβ hTolβ hLossβ hReg hSup
      hα hθ hτ₀α hεOld hθε hσ₁ hStyle hDemand hμ hμτ hτ₀ hOrder hLargeR hDegreeR hLoad
      ha hη hη₁ hScale hCTol hCLoss hGap hδ hδ₁ hFloor' hSTol hSLoss
  exact ⟨⟨C,hSize,hDis,hCover,hProfiles,F,hApart,hDegrees⟩⟩

set_option maxHeartbeats 650000 in
/-- Invoke Lemma 7.6 three times in the order of the proof. The
operations of Lemmas 8.6, 9.4 and 10.5 act on the factors just chosen.
The chosen reserves are disjoint, retain their construction data, and
have the regular union required in (11.14). -/
theorem kuhn_osthus_exceptional_factor_sequence {V : Type*} [Fintype V]
    {n l f j₈ j₉ j₁₀ : ℕ} (G : Digraph V) (Z : Finset V) (X : Fin n → Finset V)
    (hIndex₈ : n = l*j₈) (hIndex₉ : n = f*j₉) (hIndex₁₀ : n = 7*j₁₀)
    (hj₈ : 0 < j₈) (hj₉ : 0 < j₉) (hj₁₀ : 0 < j₁₀)
    (p m₈ m₉ m₁₀ r₀ r₁ r₂ r₃ s t : ℕ) (σ₈ σ₉ σ₁₀ : ℝ)
    (hExc : (p*f)*r₃ ≤ r₁+r₂+r₃) (hq : 0 < p*f)
    (hBalance : (p*f-1)*r₃+s = r₁+r₂+t) :
    let X₈ (i : Fin (l*j₈)) := X (finCongr hIndex₈.symm i)
    let X₉ (i : Fin (f*j₉)) := X (finCongr hIndex₉.symm i)
    let X₁₀ (i : Fin (7*j₁₀)) := X (finCongr hIndex₁₀.symm i)
    ∀ (preprocessingData : WoundFactorPacking G Z X₈ hj₈ 50 m₈ r₀ σ₈ → Digraph V → Prop)
    (chordData : ∀ PG : Digraph V,
      WoundFactorPacking (G \ PG) Z X₉ hj₉ p m₉ r₃ σ₉ → Digraph V → Prop)
    (parityData : ∀ PG CA : Digraph V,
      WoundFactorPacking (G \ (PG ⊔ CA)) Z X₁₀ hj₁₀ 1 m₁₀ s σ₁₀ → Digraph V → Prop)
    (_stage₈ : WoundFactorStage G Z X₈ hj₈ 50 m₈ r₀ 0 0 σ₈)
    (_stage₉ : WoundFactorStage G Z X₉ hj₉ p m₉ r₃ (50*l*r₀+t) (50*l*r₀) σ₉)
    (_stage₁₀ : WoundFactorStage G Z X₁₀ hj₁₀ 1 m₁₀ s
      (50*l*r₀+t+r₁+r₂+r₃) (50*l*r₀+(p*f)*r₃) σ₁₀)
    (_extend₈ : ∀ E : WoundFactorPacking G Z X₈ hj₈ 50 m₈ r₀ σ₈,
      ∃ PG : Digraph V, PG ≤ G ∧ (⨆ i, ⨆ a, (E.factors i a).digraph) ≤ PG ∧
        preprocessingData E PG ∧ (∀ x, let d := if x ∈ Z then 50*l*r₀ else 50*l*r₀+t
          inDegree PG x = d ∧ outDegree PG x = d))
    (_extend₉ : ∀ (PG : Digraph V), PG ≤ G →
      (∀ x, inDegree PG x ≤ 50*l*r₀+t ∧ outDegree PG x ≤ 50*l*r₀+t) →
      ∀ E : WoundFactorPacking (G \ PG) Z X₉ hj₉ p m₉ r₃ σ₉,
      ∃ CA : Digraph V, CA ≤ G \ PG ∧ (⨆ i, ⨆ a, (E.factors i a).digraph) ≤ CA ∧
        chordData PG E CA ∧ (∀ x, let d := if x ∈ Z then (p*f)*r₃ else r₁+r₂+r₃
          inDegree CA x = d ∧ outDegree CA x = d)),
    (∀ PG CA : Digraph V, PG ⊔ CA ≤ G →
      (∀ x ∉ Z, inDegree (PG ⊔ CA) x ≤ 50*l*r₀+t+r₁+r₂+r₃ ∧
        outDegree (PG ⊔ CA) x ≤ 50*l*r₀+t+r₁+r₂+r₃) →
      ∀ E : WoundFactorPacking (G \ (PG ⊔ CA)) Z X₁₀ hj₁₀ 1 m₁₀ s σ₁₀,
      ∃ PC : Digraph V, PC ≤ G \ (PG ⊔ CA) ∧ (⨆ i, ⨆ a, (E.factors i a).digraph) ≤ PC ∧
        parityData PG CA E PC ∧ (∀ x, let d := if x ∈ Z then 7*s else 6*s
          inDegree PC x = d ∧ outDegree PC x = d)) →
    ∃ (PG CA PC : Digraph V) (E₈ : WoundFactorPacking G Z X₈ hj₈ 50 m₈ r₀ σ₈)
      (E₉ : WoundFactorPacking (G \ PG) Z X₉ hj₉ p m₉ r₃ σ₉)
      (E₁₀ : WoundFactorPacking (G \ (PG ⊔ CA)) Z X₁₀ hj₁₀ 1 m₁₀ s σ₁₀),
      PG ≤ G ∧ CA ≤ G \ PG ∧ PC ≤ G \ (PG ⊔ CA) ∧
        (⨆ i, ⨆ a, (E₈.factors i a).digraph) ≤ PG ∧
        (⨆ i, ⨆ a, (E₉.factors i a).digraph) ≤ CA ∧
        (⨆ i, ⨆ a, (E₁₀.factors i a).digraph) ≤ PC ∧
        preprocessingData E₈ PG ∧ chordData PG E₉ CA ∧ parityData PG CA E₁₀ PC ∧
        (∀ x, let d := if x ∈ Z then 50*l*r₀ else 50*l*r₀+t
          inDegree PG x = d ∧ outDegree PG x = d) ∧
        (∀ x, let d := if x ∈ Z then (p*f)*r₃ else r₁+r₂+r₃
          inDegree CA x = d ∧ outDegree CA x = d) ∧
        (∀ x, let d := if x ∈ Z then 7*s else 6*s
          inDegree PC x = d ∧ outDegree PC x = d) ∧
        PG ⊔ (CA ⊔ PC) ≤ G ∧ Disjoint PG (CA ⊔ PC) ∧
        ∀ x, inDegree (PG ⊔ (CA ⊔ PC)) x = 50*l*r₀+t+r₁+r₂+r₃+6*s ∧
          outDegree (PG ⊔ (CA ⊔ PC)) x = 50*l*r₀+t+r₁+r₂+r₃+6*s := by
  intro X₈ X₉ X₁₀ preprocessingData chordData parityData stage₈ stage₉ stage₁₀ extend₈ extend₉ extend₁₀
  have hZero (x : V) : inDegree (⊥ : Digraph V) x ≤ 0 ∧ outDegree (⊥ : Digraph V) x ≤ 0 := by
    simp [inDegree,inNeighbours,outDegree]
  have hFirst : Nonempty (WoundFactorPacking G Z X₈ hj₈ 50 m₈ r₀ σ₈) := by
    simpa only [sdiff_bot] using stage₈ ⊥ bot_le hZero (fun x _ => hZero x)
  obtain ⟨E₈⟩ := hFirst
  obtain ⟨PG,hPG,hKeep₈,hData₈,hDegree₈⟩ := extend₈ E₈
  have hAll₈ (x : V) : inDegree PG x ≤ 50*l*r₀+t ∧ outDegree PG x ≤ 50*l*r₀+t := by
    obtain ⟨hi,ho⟩ := hDegree₈ x
    by_cases hx : x ∈ Z
    · rw [if_pos hx] at hi ho
      omega
    · rw [if_neg hx] at hi ho
      omega
  have hExc₈ (x : V) (hx : x ∈ Z) : inDegree PG x ≤ 50*l*r₀ ∧ outDegree PG x ≤ 50*l*r₀ := by
    obtain ⟨hi,ho⟩ := hDegree₈ x
    rw [if_pos hx] at hi ho
    omega
  obtain ⟨E₉⟩ := stage₉ PG hPG hAll₈ hExc₈
  obtain ⟨CA,hCA,hKeep₉,hData₉,hDegree₉⟩ := extend₉ PG hPG hAll₈ E₉
  obtain ⟨hLe,_,_,hLoss,hPrior,_⟩ :=
    wound_exceptional_stage_degrees G PG CA Z (50*l*r₀) t (p*f) r₁ r₂ r₃ hPG hCA hExc
      hDegree₈ hDegree₉
  obtain ⟨E₁₀⟩ := stage₁₀ (PG ⊔ CA) hLe hLoss (fun x hx => ⟨(hPrior x hx).1.le,(hPrior x hx).2.le⟩)
  obtain ⟨PC,hPC,hKeep₁₀,hData₁₀,hDegree₁₀⟩ := extend₁₀ PG CA hLe (fun x _ => hLoss x) E₁₀
  have hRB : CA ⊔ PC ≤ G \ PG :=
    sup_le hCA (fun _ _ h => ⟨(hPC h).1,fun ha => (hPC h).2 (Or.inl ha)⟩)
  have hDisPG : Disjoint PG (CA ⊔ PC) :=
    disjoint_iff_inf_le.mpr (fun _ _ h => (hRB h.2).2 h.1)
  have hDisCA (x y : V) (h : CA.Adj x y ∧ PC.Adj x y) : False :=
    (hPC h.2).2 (Or.inr h.1)
  have hDegreeRB (x : V) : let d := if x ∈ Z then (p*f)*r₃+7*s else r₁+r₂+r₃+6*s
      inDegree (CA ⊔ PC) x = d ∧ outDegree (CA ⊔ PC) x = d := by
    obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint CA PC hDisCA x
    rw [hi,ho,(hDegree₉ x).1,(hDegree₉ x).2,(hDegree₁₀ x).1,(hDegree₁₀ x).2]
    by_cases hx : x ∈ Z <;> simp [hx]
  have hRegular := kuhn_osthus_balanced_absorption_reserve PG (CA ⊔ PC) Z (50*l*r₀) t r₁ r₂ r₃
    (p*f) s hq hBalance hDisPG hDegree₈ hDegreeRB
  exact ⟨PG,CA,PC,E₈,E₉,E₁₀,hPG,hCA,hPC,hKeep₈,hKeep₉,hKeep₁₀,hData₈,hData₉,hData₁₀,
    hDegree₈,hDegree₉,hDegree₁₀,sup_le hPG (fun _ _ h => (hRB h).1),hDisPG,hRegular⟩

end OverfullWork.DirectedRobustExpansion
