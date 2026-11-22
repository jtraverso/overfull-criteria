module

public import OverfullWork.KuhnOsthusResidualExceptionalInterval
public import OverfullWork.KuhnOsthusGeneralExceptionalPacking

@[expose] public section


/-! Apply the residual construction in every canonical interval and
every style, and use the outer induction of Kühn–Osthus Lemma 7.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u
set_option maxHeartbeats 2000000

private theorem finRotate_to_first {n : ℕ} (j : Fin (n+1)) :
    finRotate (n+1) j = 0 ↔ j.val+1=n+1 := by
  by_cases hj : j = Fin.last n
  · subst j
    simp
  · constructor
    · intro heq
      have hv := congrArg Fin.val heq
      rw [coe_finRotate_of_ne_last hj] at hv
      simp at hv
    · intro heq
      have hh := Fin.val_lt_last hj
      omega

/-- Quantitative packing for canonical winding intervals. The global
successor pairs, endpoint estimates and reduced route budgets are
fixed before any factors are deleted. -/
theorem pack_original_intervals_on_winding_intervals
    (d δ ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) (hTol : 2*δ ≤ ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {K l q : ℕ}
      (G : Digraph V) (Z : Finset V)
      (R : Fin l → Digraph (Fin q)) (P : Fin (l*q) → Finset V)
      (C : Fin K × Fin (l*q) → Finset V)
      (m r e endpointCap endpointBudget routeCap : ℕ) (ε₀ a η : ℝ) (hq : 0 < q),
      let loss := endpointCap+(routeCap+2)+2*endpointCap
      let localCell (j : Fin K × Fin l) (t : Fin q) := C (j.1,intervalPosition j.2 t)
      let eligible (j : Fin K × Fin l) :=
        (windingEndpointPositions (⟨0,hq⟩ : Fin q)).biUnion (localCell j)
      0 < K → 2 ≤ l →
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) →
      (∀ x ∉ Z, ∃ i, x ∈ C i) →
      (∀ i, (C i).card = m) →
      (∀ i, (P i).card = K*m) →
      (∀ i, C i ⊆ P i.2) → (∀ i, Disjoint (P i) Z) →
      (∀ i, UniformProfileCell (inProfile G) (P i.2) (C i) K ε₀) →
      (∀ i, UniformProfileCell (outProfile G) (P i.2) (C i) K ε₀) →
      2*Z.card < endpointCap*(endpointBudget+1) →
      (∀ j z, z ∈ Z → 2*Z.card+endpointBudget*m+K*l*r < inNeighbours G (eligible j) z) →
      (∀ j z, z ∈ Z → 2*Z.card+endpointBudget*m+K*l*r < outTo G (eligible j) z) →
      2*(routeCap+2+2*endpointCap)+e < m-endpointCap →
      (∀ j i, ¬(R j).Adj i i) →
      (∀ j, ∃ radius growth cutoff budget : ℕ, IsRobustAt (R j) radius cutoff ∧ 0 < growth ∧
        2*(budget+1)+growth ≤ radius ∧
        (∀ i, cutoff+2*(budget+1) ≤ outDegree (R j) i) ∧ (∀ i, cutoff ≤ inDegree (R j) i) ∧
        Z.card*(2*(q/growth+3)) < routeCap*(budget+1)) →
      loss < m → N ≤ m-loss →
      ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) →
      (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε →
      0 ≤ ε₀ → 0 ≤ a → 0 < η → η ≤ 1 →
      K*ε₀ ≤ η → 2*(ε₀+a) ≤ η → (r:ℝ) ≤ a*((m:ℝ)*η) →
      η < d-ε₀-a → (m:ℝ)*η ≤ (e:ℝ)+1 →
      0 < δ → δ ≤ 1 → 2*ε₀ ≤ d →
      2*(max 2 (K:ℝ)*ε₀+a) ≤ δ → (r:ℝ) ≤ a*((m:ℝ)*δ) →
      (∀ j i h, (R j).Adj i h →
        IsUniform G ε₀ (P (intervalPosition j i)) (P (intervalPosition j h)) ∧
          d ≤ density G (P (intervalPosition j i)) (P (intervalPosition j h))) →
      (∀ i, IsLowerSuperregularPair G ε₀ d (P i) (P (finRotate (l*q) i))) →
      let U (j : Fin K × Fin l) := univ.biUnion (localCell j)
      let S (j : Fin K × Fin l) := localCell j ⟨0,hq⟩
      let next : Equiv.Perm (Fin K × Fin l) := Equiv.prodCongr (Equiv.refl (Fin K)) (finRotate l)
      ∃ F : Fin r → ∀ j, OriginalInterval G Z (U j ∪ S (next j)) (S j) (S (next j)),
        let D (i : Fin r) := ⨆ j, (F i j).digraph
        Pairwise (fun i j => Disjoint (D i) (D j)) ∧
        ∀ x, inDegree (⨆ i, D i) x ≤ r*(if x ∈ Z then K*l else 1) ∧
          outDegree (⨆ i, D i) x ≤ r*(if x ∈ Z then K*l else 1) := by
  classical
  obtain ⟨N,hN⟩ := exists_original_interval_after_prefix_deletion.{u}
    d δ ε ν τ γ hν hWidth hε hε1 hτγ hγ hd hCost hDegrees hTol
  refine ⟨N,?_⟩
  intro V _ K l q G Z R P C m r e endpointCap endpointBudget routeCap ε₀ a η hq loss C' E
    hK hl hDis hCover hSize hPSize hCP hPZ hRefIn hRefOut hBdg hIn hOut hRoom hLoop hRoutes
    hm hMin hHall hPay hε₀ ha hη hη1 hScale hCTol hCLoss hGap hCut hδ hδ1 hFloor hSTol hSLoss hReg hSup U S next
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  obtain ⟨hPart,hApart,hUnion⟩ := winding_styled_interval_partition C hl (Nat.succ_pos n) m hDis hSize
  refine pack_original_interval_families G Z r K l next U S
    (fun i => (hPart i).2.1) (fun i => (hPart i).2.2.1) hApart
    (fun x hx => (hUnion x).mpr (hCover x hx)) ?_
  intro t ht H hHG hLoss j
  let key (i : Fin (n+1)) := (j.1,intervalPosition j.2 i)
  let lastKey := ((next j).1,intervalPosition (next j).2 (0 : Fin (n+1)))
  let B (i : Fin (n+1)) := P (key i).2
  let T := C lastKey
  let Bₜ := P lastKey.2
  have hOrd (x : V) (hx : x ∉ Z) : inDegree H x ≤ r ∧ outDegree H x ≤ r := by
    have hh := hLoss x
    simp only [if_neg hx,Nat.mul_one] at hh
    exact ⟨hh.1.trans ht.le,hh.2.trans ht.le⟩
  have hExc (x : V) (hx : x ∈ Z) : inDegree H x ≤ K*l*r ∧ outDegree H x ≤ K*l*r := by
    have hh := hLoss x
    have he : t*(K*l) ≤ K*l*r := by rw [mul_comm (K*l) r]; exact Nat.mul_le_mul_right _ ht.le
    simp only [if_pos hx] at hh
    exact ⟨hh.1.trans he,hh.2.trans he⟩
  have hDis' (i k : Fin (n+1)) (hik : i ≠ k) : Disjoint (C' j i) (C' j k) :=
    hDis _ _ (fun h => hik ((intervalPosition j.2).injective (congrArg Prod.snd h)))
  have hDisT (i : Fin (n+1)) : Disjoint (C' j i) T := by
    apply (hApart j (next j) ((hPart j).2.1.symm)).mono _ ((hPart (next j)).2.2.1)
    intro x hx
    exact mem_biUnion.mpr ⟨i,mem_univ _,hx⟩
  have hAZ : Disjoint (U j ∪ T) Z := by
    apply disjoint_left.mpr
    intro x hx hz
    rcases mem_union.mp hx with hu | ht
    · obtain ⟨i,_,hi⟩ := mem_biUnion.mp hu
      exact disjoint_left.mp (hPZ (key i).2) (hCP (key i) hi) hz
    · exact disjoint_left.mp (hPZ lastKey.2) (hCP lastKey ht) hz
  have hSucc (i : Fin (n+1)) : IsLowerSuperregularPair G ε₀ d (B i)
      (if finRotate (n+1) i = 0 then Bₜ else B (finRotate (n+1) i)) := by
    have h := hSup (intervalPosition j.2 i)
    rw [intervalPosition_next (Nat.succ_pos n)] at h
    by_cases he : finRotate (n+1) i = 0
    · rw [if_pos he]
      rw [if_pos ((finRotate_to_first i).mp he)] at h
      exact h
    · rw [if_neg he]
      rw [if_neg (fun h => he ((finRotate_to_first i).mpr h))] at h
      exact h
  have hLocal := hN (n := n) G H (R j.2) Z Bₜ T B (C' j)
    K m e endpointCap endpointBudget routeCap r (K*l*r) ε₀ a η
  exact hLocal hHG hOrd hExc hDis' hDisT hAZ
    (fun i => hSize (key i)) (hSize lastKey) (fun i => hPSize (key i).2) (hPSize lastKey.2)
    (fun i => hCP (key i)) (hCP lastKey) (fun i => hPZ (key i).2) (hPZ lastKey.2)
    (fun i => hRefIn (key i)) (fun i => hRefOut (key i)) (hRefOut lastKey)
    hBdg (hIn j) (hOut j) hRoom (hLoop j.2) (hRoutes j.2) hm hMin hHall hPay
    hK hε₀ ha hη hη1 hScale hCTol hCLoss hGap hCut hδ hδ1 hFloor
    hSTol hSLoss (hReg j.2) hSucc

/-- Extract the preprocessing certificates from an already built
family of fifty-style intervals, retaining every original arc. -/
theorem assemble_preprocessing_factors_from_wound_intervals
    {V : Type*} [Fintype V] {r l q : ℕ}
    (G : Digraph V) (Z : Finset V) (label : V → Fin 50)
    (C : Fin 50 × Fin (l*q) → Finset V) (m : ℕ) (hl : 2 ≤ l) (hq : 0 < q)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hCover : ∀ x ∉ Z, ∃ i, x ∈ C i) (hSize : ∀ i, (C i).card = m)
    (hLabel : ∀ i x, x ∈ C i → label x = i.1) :
    let next := (Equiv.refl (Fin 50)).prodCongr (finRotate l)
    let U (j : Fin 50 × Fin l) :=
      (univ : Finset (Fin q)).biUnion (fun i => C (j.1,intervalPosition j.2 i))
    let S (j : Fin 50 × Fin l) := C (j.1,intervalPosition j.2 ⟨0,hq⟩)
    ∀ F : Fin r → ∀ j, OriginalInterval G Z (U j ∪ S (next j)) (S j) (S (next j)),
      ∃ Q : Fin r → OriginalExceptionalFactor label Z l,
        (∀ i, (Q i).digraph = ⨆ j, (F i j).digraph) ∧ ∀ i, (Q i).digraph ≤ G := by
  intro next U S F
  obtain ⟨hPart,hApart,hUnion⟩ := winding_styled_interval_partition C hl hq m hDis hSize
  have hLabelU (i : Fin 50 × Fin l) (x : V) (hx : x ∈ U i) : label x = i.1 := by
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hx
    exact hLabel _ x hj
  have hCert (j : Fin r) := assemble_exceptional_factor_along_intervals G Z label l (q*m)
    next U S (fun i => (hPart i).2.1) (fun i => (hPart i).1) (fun i => (hPart i).2.2.1)
    hApart (fun x hx => (hUnion x).mpr (hCover x hx)) (fun i => (hPart i).2.2.2) hLabelU (F j)
  choose Q hQ hLe _ using hCert
  have he (j : Fin r) : (Q j).digraph = ⨆ i, (F j i).digraph := by
    simp only [OriginalExceptionalFactor.digraph,hQ]
  exact ⟨Q,he,hLe⟩

/-- The 50-style specialization supplies the certificate of Lemma 8.1. -/
theorem pack_original_exceptional_factors_on_winding_intervals
    (d δ ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) (hTol : 2*δ ≤ ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {l q : ℕ}
      (G : Digraph V) (Z : Finset V) (label : V → Fin 50)
      (R : Fin l → Digraph (Fin q)) (P : Fin (l*q) → Finset V)
      (C : Fin 50 × Fin (l*q) → Finset V)
      (m r e endpointCap endpointBudget routeCap : ℕ) (ε₀ a η : ℝ) (hq : 0 < q),
      let loss := endpointCap+(routeCap+2)+2*endpointCap
      let localCell (j : Fin 50 × Fin l) (t : Fin q) := C (j.1,intervalPosition j.2 t)
      let eligible (j : Fin 50 × Fin l) :=
        (windingEndpointPositions (⟨0,hq⟩ : Fin q)).biUnion (localCell j)
      2 ≤ l →
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) →
      (∀ x ∉ Z, ∃ i, x ∈ C i) →
      (∀ i, (C i).card = m) → (∀ i x, x ∈ C i → label x = i.1) →
      (∀ i, (P i).card = 50*m) →
      (∀ i, C i ⊆ P i.2) → (∀ i, Disjoint (P i) Z) →
      (∀ i, UniformProfileCell (inProfile G) (P i.2) (C i) 50 ε₀) →
      (∀ i, UniformProfileCell (outProfile G) (P i.2) (C i) 50 ε₀) →
      2*Z.card < endpointCap*(endpointBudget+1) →
      (∀ j z, z ∈ Z → 2*Z.card+endpointBudget*m+50*l*r < inNeighbours G (eligible j) z) →
      (∀ j z, z ∈ Z → 2*Z.card+endpointBudget*m+50*l*r < outTo G (eligible j) z) →
      2*(routeCap+2+2*endpointCap)+e < m-endpointCap →
      (∀ j i, ¬(R j).Adj i i) →
      (∀ j, ∃ radius growth cutoff budget : ℕ, IsRobustAt (R j) radius cutoff ∧ 0 < growth ∧
        2*(budget+1)+growth ≤ radius ∧
        (∀ i, cutoff+2*(budget+1) ≤ outDegree (R j) i) ∧ (∀ i, cutoff ≤ inDegree (R j) i) ∧
        Z.card*(2*(q/growth+3)) < routeCap*(budget+1)) →
      loss < m → N ≤ m-loss →
      ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) →
      (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε →
      0 ≤ ε₀ → 0 ≤ a → 0 < η → η ≤ 1 →
      50*ε₀ ≤ η → 2*(ε₀+a) ≤ η → (r:ℝ) ≤ a*((m:ℝ)*η) →
      η < d-ε₀-a → (m:ℝ)*η ≤ (e:ℝ)+1 →
      0 < δ → δ ≤ 1 → 2*ε₀ ≤ d →
      2*(50*ε₀+a) ≤ δ → (r:ℝ) ≤ a*((m:ℝ)*δ) →
      (∀ j i h, (R j).Adj i h →
        IsUniform G ε₀ (P (intervalPosition j i)) (P (intervalPosition j h)) ∧
          d ≤ density G (P (intervalPosition j i)) (P (intervalPosition j h))) →
      (∀ i, IsLowerSuperregularPair G ε₀ d (P i) (P (finRotate (l*q) i))) →
      ∃ F : Fin r → OriginalExceptionalFactor label Z l,
        (∀ i, (F i).digraph ≤ G) ∧ Pairwise (fun i j => Disjoint (F i).digraph (F j).digraph) ∧
        ∀ x, inDegree (⨆ i, (F i).digraph) x ≤ r*(if x ∈ Z then 50*l else 1) ∧
          outDegree (⨆ i, (F i).digraph) x ≤ r*(if x ∈ Z then 50*l else 1) := by
  obtain ⟨N,hN⟩ := pack_original_intervals_on_winding_intervals.{u}
    d δ ε ν τ γ hν hWidth hε hε1 hτγ hγ hd hCost hDegrees hTol
  refine ⟨N,?_⟩
  intro V _ l q G Z label R P C m r e endpointCap endpointBudget routeCap ε₀ a η hq loss C' E
    hl hDis hCover hSize hLabel hPSize hCP hPZ hRefIn hRefOut hBdg hIn hOut hRoom hLoop hRoutes
    hm hMin hHall hPay hε₀ ha hη hη1 hScale hCTol hCLoss hGap hCut hδ hδ1 hFloor hSTol hSLoss hReg hSup
  obtain ⟨F,hDisF,hBudget⟩ := hN G Z R P C m r e endpointCap endpointBudget routeCap
    ε₀ a η hq (by decide : 0 < 50) hl hDis hCover hSize hPSize hCP hPZ hRefIn hRefOut hBdg hIn hOut
    hRoom hLoop hRoutes hm hMin hHall hPay hε₀ ha hη hη1 hScale hCTol hCLoss hGap hCut hδ hδ1 hFloor
    (by
      have hMax : max (2:ℝ) ((50:ℕ):ℝ) = 50 := by norm_num
      rwa [hMax]) hSLoss hReg hSup
  obtain ⟨Q,he,hLe⟩ := assemble_preprocessing_factors_from_wound_intervals
    G Z label C m hl hq hDis hCover hSize hLabel F
  refine ⟨Q,hLe,?_,by simpa only [he] using hBudget⟩
  intro i j hij
  rw [he i,he j]
  exact hDisF hij

end OverfullWork.DirectedRobustExpansion
