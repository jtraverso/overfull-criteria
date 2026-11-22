module

public import OverfullWork.KuhnOsthusDisjointSparseSampling

@[expose] public section


/-! Calibrate the two reserve fractions of Kühn–Osthus Lemma 8.2
on each active cluster pair. The host pairs are given in coordinates
on the two equal-sized sides. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

/-- Simultaneous PE1 and PE2, from the regular and superregular host
pairs of a scheme. The scalar inequalities are explicit. -/
theorem exists_extender_of_cluster_pairs_with_styles (κ : ℕ) (d d₀ δ ε ζ η aStyle : ℝ)
    (hκ : 1 ≤ κ) (hd : 0 < d) (hd1 : d ≤ 1) (hd₀ : 0 < d₀)
    (hSmall : d₀ ≤ d/4) (hε : 0 < ε) (hδε : δ ≤ ε) (hRel : 4*δ ≤ ε*d)
    (hδd : δ ≤ d/4) (hζ1 : ζ ≤ 1/2)
    (hη : 0 < η)
    (hCut : 4*η ≤ ε^3*(d₀/(κ:ℝ))) (hMax : 2*η ≤ d₀/(κ:ℝ))
    (hCodeg : η ≤ (d₀/(κ:ℝ))^2) (hMin : 4*η ≤ d₀) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {V I : Type*}
      (a b : I → W ↪ V) (D : I → Digraph W) (densityOf : I → ℝ)
      (cycle reduced : Set I) (A B : I → Fin 50 → Finset W), N ≤ Fintype.card W →
      (∀ i, d ≤ densityOf i ∧ densityOf i ≤ 1) →
      (∀ i, i ∈ cycle ∨ i ∈ reduced → IsCentredRegular (D i) δ (densityOf i)) →
      (∀ i ∈ cycle, ∀ v,
        (densityOf i-δ)*(Fintype.card W:ℝ) ≤ (inDegree (D i) v:ℝ) ∧
        (densityOf i-δ)*(Fintype.card W:ℝ) ≤ (outDegree (D i) v:ℝ)) →
      (∀ i ∈ cycle, ∀ v j,
        aStyle*densityOf i*(Fintype.card W:ℝ) ≤ inNeighbours (D i) (A i j) v ∧
        aStyle*densityOf i*(Fintype.card W:ℝ) ≤ outTo (D i) (B i j) v) →
      (∀ i j, i ≠ j → Disjoint (liftDirectedPair (a i) (b i) (D i))
        (liftDirectedPair (a j) (b j) (D j))) →
      ∃ C R : I → Digraph W,
        (∀ i, i ∉ cycle → C i = ⊥) ∧ (∀ i, i ∉ reduced → R i = ⊥) ∧
        (∀ i ∈ cycle, SparseSuccessorPairBounds (C i) d₀ ε (d/2) ζ ∧
          (∀ v, (inDegree (C i) v:ℝ) ≤ (2*d₀/d)*Fintype.card W ∧
            (outDegree (C i) v:ℝ) ≤ (2*d₀/d)*Fintype.card W) ∧
          ∀ X Y : Finset W, ε*(Fintype.card W:ℝ) ≤ (X.card:ℝ) →
            ε*(Fintype.card W:ℝ) ≤ (Y.card:ℝ) →
            |(incidences (C i) X Y:ℝ)-d₀*(X.card:ℝ)*(Y.card:ℝ)| ≤
              ε*d₀*(X.card:ℝ)*(Y.card:ℝ)) ∧
        (∀ i ∈ reduced, SparseSuccessorPairBounds (R i) (d₀/(κ:ℝ)) ε (d/2) 0 ∧
          (∀ v, (inDegree (R i) v:ℝ) ≤ (2*(d₀/(κ:ℝ))/d)*Fintype.card W ∧
            (outDegree (R i) v:ℝ) ≤ (2*(d₀/(κ:ℝ))/d)*Fintype.card W) ∧
          ∀ X Y : Finset W, ε*(Fintype.card W:ℝ) ≤ (X.card:ℝ) →
            ε*(Fintype.card W:ℝ) ≤ (Y.card:ℝ) →
            |(incidences (R i) X Y:ℝ)-(d₀/(κ:ℝ))*(X.card:ℝ)*(Y.card:ℝ)| ≤
              ε*(d₀/(κ:ℝ))*(X.card:ℝ)*(Y.card:ℝ)) ∧
        Disjoint (directedPairUnion a b C) (directedPairUnion a b R) ∧
        (directedPairUnion a b C ⊔ directedPairUnion a b R) ≤ directedPairUnion a b D ∧
        ∀ i ∈ cycle, ∀ v j,
          (aStyle*d₀-η)*(Fintype.card W:ℝ) ≤ inNeighbours (C i) (A i j) v ∧
          (aStyle*d₀-η)*(Fintype.card W:ℝ) ≤ outTo (C i) (B i j) v := by
  classical
  obtain ⟨N,hN⟩ := exists_sparse_reserve_unions_with_styles.{u} η hη
  refine ⟨max N 1,?_⟩
  intro W _ V I a b D densityOf cycle reduced A B hn hDen hReg hSuper hHostStyle hDis
  let β := d₀/(κ:ℝ)
  have hκ' : (1:ℝ) ≤ κ := by exact_mod_cast hκ
  change 4*η ≤ ε^3*β at hCut
  change 2*η ≤ β at hMax
  change η ≤ β^2 at hCodeg
  have hβ : 0 < β := div_pos hd₀ (by linarith)
  have hβd : β ≤ d₀ := (div_le_iff₀ (by linarith : (0:ℝ) < κ)).mpr
    (by nlinarith only [mul_le_mul_of_nonneg_left hκ' hd₀.le])
  let p i := if i ∈ cycle then d₀/densityOf i else 0
  let q i := if i ∈ reduced then β/densityOf i else 0
  have hPos (i : I) : 0 < densityOf i := hd.trans_le (hDen i).1
  have hAbs (θ : ℝ) (hθ : 0 < θ) (i : I) :
      θ ≤ θ/densityOf i ∧ θ/densityOf i ≤ θ/d := by
    constructor
    · apply (le_div_iff₀ (hPos i)).mpr
      exact mul_le_of_le_one_right hθ.le (hDen i).2
    · exact div_le_div_of_nonneg_left hθ.le hd (hDen i).1
  have hCaps (i : I) : 0 ≤ p i ∧ p i ≤ 1/4 ∧ 0 ≤ q i ∧ p i+q i ≤ 1 := by
    have hp0 : 0 ≤ p i := by
      dsimp [p]
      split
      · exact div_nonneg hd₀.le (hPos i).le
      · exact le_rfl
    have hq0 : 0 ≤ q i := by
      dsimp [q]
      split
      · exact div_nonneg hβ.le (hPos i).le
      · exact le_rfl
    have hOne : d₀/d ≤ 1/4 := (div_le_iff₀ hd).mpr (by linarith)
    have hp1 : p i ≤ 1/4 := by
      dsimp [p]
      split
      · exact (hAbs d₀ hd₀ i).2.trans hOne
      · norm_num
    have hq1 : q i ≤ 1/4 := by
      dsimp [q]
      split
      · exact ((hAbs β hβ i).2.trans (div_le_div_of_nonneg_right hβd hd.le)).trans hOne
      · norm_num
    exact ⟨hp0,hp1,hq0,by linarith⟩
  obtain ⟨C,R,hPairs,hCR,hSub⟩ := hN a b D p q A B ((le_max_left _ _).trans hn) hCaps hDis
  have hM : 0 < Fintype.card W := (le_max_right _ _).trans hn
  let m : ℝ := Fintype.card W
  have hm : 0 ≤ m := by positivity
  have hRelative (i : I) (J : Digraph W) (f θ t : ℝ)
      (hTrack : TracksArcStatistics J (D i) f t)
      (hf : 0 ≤ f) (hEq : f*densityOf i = θ) (ht : t ≤ ε^3*θ/2)
      (hi : i ∈ cycle ∨ i ∈ reduced) :
      ∀ X Y : Finset W, ε*m ≤ (X.card:ℝ) → ε*m ≤ (Y.card:ℝ) →
        |(incidences J X Y:ℝ)-θ*(X.card:ℝ)*(Y.card:ℝ)| ≤
          ε*θ*(X.card:ℝ)*(Y.card:ℝ) := by
    have hScale : 4*δ ≤ ε*densityOf i :=
      hRel.trans (mul_le_mul_of_nonneg_left (hDen i).1 hε.le)
    have ht' : t ≤ ε^3*(f*densityOf i)/2 := by rwa [hEq]
    simpa only [hEq] using relative_regularity_of_arc_tracking (D i) J (densityOf i) δ f ε t
      hM (hPos i) hf hε hδε hScale ht' (hReg i hi) (fun X Y => hTrack (.inr (.inr (X,Y))))
  have hMaxDegree {u v f t c : ℝ} (hf : 0 ≤ f) (hv : v ≤ m)
      (hT : |u-f*v| ≤ t*m) (hBudget : f+t ≤ c) : u ≤ c*m := by
    have h₁ := (abs_le.mp hT).2
    have h₂ := mul_le_mul_of_nonneg_left hv hf
    have h₃ := mul_le_mul_of_nonneg_right hBudget hm
    linarith only [h₁,h₂,h₃]
  have hDegreeI (i : I) (v : W) : (inDegree (D i) v:ℝ) ≤ m := by
    dsimp only [m]
    exact_mod_cast DirectedArcSelection.inDegree_le (D i) v
  have hDegreeO (i : I) (v : W) : (outDegree (D i) v:ℝ) ≤ m := by
    dsimp only [m]
    exact_mod_cast DirectedArcSelection.outDegree_le (D i) v
  refine ⟨C,R,?_,?_,?_,?_,hCR,hSub,?_⟩
  · intro i hi
    exact (hPairs i).2.2.1 (by simp [p,hi])
  · intro i hi
    exact (hPairs i).2.2.2.1 (by simp [q,hi])
  · intro i hi
    obtain ⟨_,_,_,_,hTC,_,hc,_⟩ := hPairs i
    have hpEq : p i*densityOf i = d₀ := by
      simp only [p,if_pos hi]
      exact div_mul_cancel₀ _ (hPos i).ne'
    have hpA := hAbs d₀ hd₀ i
    rw [←show p i = d₀/densityOf i by simp [p,hi]] at hpA
    have hcScale : η ≤ (p i)^2 := hCodeg.trans
      (pow_le_pow_left₀ hβ.le (hβd.trans hpA.1) 2)
    have hU : η ≤ d₀/d := by
      have := mul_le_of_le_one_right hd₀.le hd1
      have hh : d₀ ≤ d₀/d := (le_div_iff₀ hd).mpr this
      linarith only [hMax,hβd,hh,hd₀]
    have hpBudget : p i+η ≤ 2*d₀/d := calc
      _ ≤ d₀/d+d₀/d := add_le_add hpA.2 hU
      _ = _ := by ring
    have hcB : ((p i)^2+η)*m ≤ (d₀/(d/2))^2*m := by
      have h := pow_le_pow_left₀ (hCaps i).1 hpA.2 2
      have he : d₀/(d/2) = 2*(d₀/d) := by field_simp
      rw [he]
      apply mul_le_mul_of_nonneg_right _ hm
      nlinarith only [h,hcScale,sq_nonneg (d₀/d)]
    have hRegC := hRelative i (C i) (p i) d₀ η hTC (hCaps i).1 hpEq (by
      have h := mul_le_mul_of_nonneg_left hβd (pow_nonneg hε.le 3)
      linarith only [hCut,h,hη]) (Or.inl hi)
    have hLow {u v : ℝ} (hv : (densityOf i-δ)*m ≤ v) (hT : |u-p i*v| ≤ η*m) :
        ζ*d₀*m ≤ u := by
      have ha := mul_le_mul_of_nonneg_left hv (hCaps i).1
      have hδ' : δ ≤ densityOf i/4 := by linarith only [hδd,(hDen i).1]
      have hδm := mul_le_mul_of_nonneg_right hδ' (mul_nonneg (hCaps i).1 hm)
      have hηm := mul_le_mul_of_nonneg_right hMin hm
      have hz := mul_le_mul_of_nonneg_right hζ1 (mul_nonneg hd₀.le hm)
      have hEq := congrArg (fun x : ℝ => x*m) hpEq
      linarith only [ha,hδm,hηm,hz,hEq,(abs_le.mp hT).1]
    refine ⟨⟨fun v => hLow (hSuper i hi v).1 (hTC (.inl v)),
      fun v => hLow (hSuper i hi v).2 (hTC (.inr (.inl v))),
      fun x y h => (hc x y h).1.trans hcB,
      fun x y h => (hc x y h).2.1.trans hcB,
      fun X Y hx hy => by linarith only [(abs_le.mp (hRegC X Y hx hy)).1]⟩,
      fun v => ⟨hMaxDegree (hCaps i).1 (hDegreeI i v) (hTC (.inl v)) hpBudget,
        hMaxDegree (hCaps i).1 (hDegreeO i v) (hTC (.inr (.inl v))) hpBudget⟩,hRegC⟩
  · intro i hi
    obtain ⟨_,_,_,_,_,hTR,hc,_⟩ := hPairs i
    have hqEq : q i*densityOf i = β := by
      simp only [q,if_pos hi]
      exact div_mul_cancel₀ _ (hPos i).ne'
    have hqA := hAbs β hβ i
    rw [←show q i = β/densityOf i by simp [q,hi]] at hqA
    have hqb : q i+ (η+η) ≤ 2*β/d := by
      have hh := (le_div_iff₀ hd).mpr (mul_le_of_le_one_right hβ.le hd1)
      calc
        _ ≤ β/d+β/d := add_le_add hqA.2 ((by linarith only [hMax] : η+η ≤ β).trans hh)
        _ = _ := by ring
    have hcB : ((4*q i/3)^2+η)*m ≤ (β/(d/2))^2*m := by
      have h₁ := pow_le_pow_left₀ hβ.le hqA.1 2
      have h₂ := pow_le_pow_left₀ (hCaps i).2.2.1 hqA.2 2
      have he : β/(d/2) = 2*(β/d) := by field_simp
      rw [he]
      apply mul_le_mul_of_nonneg_right _ hm
      nlinarith only [h₁,h₂,hCodeg,sq_nonneg (β/d)]
    have hRegR := hRelative i (R i) (q i) β (η+η) hTR (hCaps i).2.2.1 hqEq
      (by linarith only [hCut]) (Or.inr hi)
    refine ⟨⟨fun _ => by simp,fun _ => by simp,
      fun x y h => (hc x y h).2.2.1.trans hcB,
      fun x y h => (hc x y h).2.2.2.trans hcB,
      fun X Y hx hy => by linarith only [(abs_le.mp (hRegR X Y hx hy)).1]⟩,
      fun v => ⟨hMaxDegree (hCaps i).2.2.1 (hDegreeI i v) (hTR (.inl v)) hqb,
        hMaxDegree (hCaps i).2.2.1 (hDegreeO i v) (hTR (.inr (.inl v))) hqb⟩,hRegR⟩

  · intro i hi v j
    have hpEq : p i*densityOf i = d₀ := by
      simp only [p,if_pos hi]
      exact div_mul_cancel₀ _ (hPos i).ne'
    obtain ⟨hIn,hOut⟩ := hHostStyle i hi v j
    obtain ⟨hCI,hCO⟩ := (hPairs i).2.2.2.2.2.2.2 v j
    have help {a b : ℝ} (h : aStyle*densityOf i*m ≤ b)
        (hTrack : |a-p i*b| ≤ η*m) : (aStyle*d₀-η)*m ≤ a := by
      have hLower := mul_le_mul_of_nonneg_left h (hCaps i).1
      have hEq := congrArg (fun x : ℝ => aStyle*x*m) hpEq
      linarith only [hLower,hEq,(abs_le.mp hTrack).1]
    exact ⟨help hIn hCI,help hOut hCO⟩

/-- Simultaneous PE1 and PE2, from the regular and superregular host
pairs of a scheme. The scalar inequalities are explicit. -/
theorem exists_extender_of_cluster_pairs (κ : ℕ) (d d₀ δ ε ζ η : ℝ)
    (hκ : 1 ≤ κ) (hd : 0 < d) (hd1 : d ≤ 1) (hd₀ : 0 < d₀)
    (hSmall : d₀ ≤ d/4) (hε : 0 < ε) (hδε : δ ≤ ε) (hRel : 4*δ ≤ ε*d)
    (hδd : δ ≤ d/4) (hζ1 : ζ ≤ 1/2)
    (hη : 0 < η)
    (hCut : 4*η ≤ ε^3*(d₀/(κ:ℝ))) (hMax : 2*η ≤ d₀/(κ:ℝ))
    (hCodeg : η ≤ (d₀/(κ:ℝ))^2) (hMin : 4*η ≤ d₀) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {V I : Type*}
      (a b : I → W ↪ V) (D : I → Digraph W) (densityOf : I → ℝ)
      (cycle reduced : Set I), N ≤ Fintype.card W →
      (∀ i, d ≤ densityOf i ∧ densityOf i ≤ 1) →
      (∀ i, i ∈ cycle ∨ i ∈ reduced → IsCentredRegular (D i) δ (densityOf i)) →
      (∀ i ∈ cycle, ∀ v,
        (densityOf i-δ)*(Fintype.card W:ℝ) ≤ (inDegree (D i) v:ℝ) ∧
        (densityOf i-δ)*(Fintype.card W:ℝ) ≤ (outDegree (D i) v:ℝ)) →
      (∀ i j, i ≠ j → Disjoint (liftDirectedPair (a i) (b i) (D i))
        (liftDirectedPair (a j) (b j) (D j))) →
      ∃ C R : I → Digraph W,
        (∀ i, i ∉ cycle → C i = ⊥) ∧ (∀ i, i ∉ reduced → R i = ⊥) ∧
        (∀ i ∈ cycle, SparseSuccessorPairBounds (C i) d₀ ε (d/2) ζ ∧
          (∀ v, (inDegree (C i) v:ℝ) ≤ (2*d₀/d)*Fintype.card W ∧
            (outDegree (C i) v:ℝ) ≤ (2*d₀/d)*Fintype.card W) ∧
          ∀ X Y : Finset W, ε*(Fintype.card W:ℝ) ≤ (X.card:ℝ) →
            ε*(Fintype.card W:ℝ) ≤ (Y.card:ℝ) →
            |(incidences (C i) X Y:ℝ)-d₀*(X.card:ℝ)*(Y.card:ℝ)| ≤
              ε*d₀*(X.card:ℝ)*(Y.card:ℝ)) ∧
        (∀ i ∈ reduced, SparseSuccessorPairBounds (R i) (d₀/(κ:ℝ)) ε (d/2) 0 ∧
          (∀ v, (inDegree (R i) v:ℝ) ≤ (2*(d₀/(κ:ℝ))/d)*Fintype.card W ∧
            (outDegree (R i) v:ℝ) ≤ (2*(d₀/(κ:ℝ))/d)*Fintype.card W) ∧
          ∀ X Y : Finset W, ε*(Fintype.card W:ℝ) ≤ (X.card:ℝ) →
            ε*(Fintype.card W:ℝ) ≤ (Y.card:ℝ) →
            |(incidences (R i) X Y:ℝ)-(d₀/(κ:ℝ))*(X.card:ℝ)*(Y.card:ℝ)| ≤
              ε*(d₀/(κ:ℝ))*(X.card:ℝ)*(Y.card:ℝ)) ∧
        Disjoint (directedPairUnion a b C) (directedPairUnion a b R) ∧
        (directedPairUnion a b C ⊔ directedPairUnion a b R) ≤ directedPairUnion a b D := by
  obtain ⟨N,hN⟩ := exists_extender_of_cluster_pairs_with_styles.{u}
    κ d d₀ δ ε ζ η 0 hκ hd hd1 hd₀ hSmall hε hδε hRel hδd hζ1 hη hCut hMax hCodeg hMin
  refine ⟨N,?_⟩
  intro W _ V I a b D densityOf cycle reduced hn hDen hReg hSuper hDis
  obtain ⟨C,R,hC,hR,hPE1,hPE2,hDis',hSub,_⟩ := hN a b D densityOf cycle reduced
    (fun _ _ => ∅) (fun _ _ => ∅) hn hDen hReg hSuper (by
      intro i hi v j
      simp only [zero_mul]
      exact ⟨Nat.cast_nonneg _,Nat.cast_nonneg _⟩) hDis
  exact ⟨C,R,hC,hR,hPE1,hPE2,hDis',hSub⟩

private theorem lifted_union_outDegree_le {V W I : Type*}
    [Fintype V] [Fintype W] (a b : I → W ↪ V) (D : I → Digraph W)
    (v : V) (A : Finset I) (L : ℝ)
    (hSupp : ∀ i s t, (D i).Adj s t → a i s = v → i ∈ A)
    (hLocal : ∀ i ∈ A, ∀ s, a i s = v → (outDegree (D i) s:ℝ) ≤ L)
    (hRange : ∀ i ∈ A, ∃ s, a i s = v) :
    (outDegree (directedPairUnion a b D) v:ℝ) ≤ (A.card:ℝ)*L := by
  classical
  let N (i : I) := (univ : Finset V).filter (fun y => (liftDirectedPair (a i) (b i) (D i)).Adj v y)
  have hN : (univ : Finset V).filter (fun y => (directedPairUnion a b D).Adj v y) =
      A.biUnion N := by
    ext y
    rw [mem_filter,mem_biUnion]
    simp only [mem_univ,true_and]
    constructor
    · rintro ⟨i,s,t,hs,ht,hst⟩
      exact ⟨i,hSupp i s t hst hs,mem_filter.mpr ⟨mem_univ _,s,t,hs,ht,hst⟩⟩
    · rintro ⟨i,_,h⟩
      exact ⟨i,(mem_filter.mp h).2⟩
  have hCard : ∀ i ∈ A, ((N i).card:ℝ) ≤ L := by
    intro i hi
    obtain ⟨s,hs⟩ := hRange i hi
    have he : N i = (univ.filter ((D i).Adj s)).map (b i) := by
      ext y
      change y ∈ univ.filter (fun z => (liftDirectedPair (a i) (b i) (D i)).Adj v z) ↔ _
      rw [mem_filter,mem_map]
      simp only [mem_univ,true_and]
      constructor
      · rintro ⟨x,t,hx,ht,hxt⟩
        exact ⟨t,mem_filter.mpr ⟨mem_univ _,(a i).injective (hx.trans hs.symm) ▸ hxt⟩,ht⟩
      · rintro ⟨t,ht,he⟩
        exact ⟨s,t,hs,he,(mem_filter.mp ht).2⟩
    rw [he,card_map]
    exact hLocal i hi s hs
  have hUnion : outDegree (directedPairUnion a b D) v ≤ ∑ i ∈ A,(N i).card := by
    unfold outDegree
    rw [hN]
    exact card_biUnion_le
  calc
    _ ≤ ∑ i ∈ A,((N i).card:ℝ) := by exact_mod_cast hUnion
    _ ≤ ∑ _i ∈ A,L := sum_le_sum hCard
    _ = _ := by rw [sum_const,nsmul_eq_mul]

private theorem lifted_union_degree_le {V W I : Type*}
    [Fintype V] [Fintype W] [Fintype I] (a b : I → W ↪ V) (D : I → Digraph W)
    (A : Set I) (L : ℝ) (c : ℕ) (hL : 0 ≤ L)
    (hOff : ∀ i ∉ A, D i = ⊥)
    (hLocal : ∀ i ∈ A, ∀ s, (inDegree (D i) s:ℝ) ≤ L ∧ (outDegree (D i) s:ℝ) ≤ L)
    (hCount : ∀ v : V,
      (univ.filter (fun i => i ∈ A ∧ v ∈ Set.range (a i))).card +
        (univ.filter (fun i => i ∈ A ∧ v ∈ Set.range (b i))).card ≤ c) :
    ∀ v, (inDegree (directedPairUnion a b D) v:ℝ) +
      outDegree (directedPairUnion a b D) v ≤ (c:ℝ)*L := by
  classical
  intro v
  let O := univ.filter (fun i => i ∈ A ∧ v ∈ Set.range (a i))
  let P := univ.filter (fun i => i ∈ A ∧ v ∈ Set.range (b i))
  have hA (i : I) (s t : W) (h : (D i).Adj s t) : i ∈ A := by
    by_contra hi
    rw [hOff i hi] at h
    exact h
  have hout := lifted_union_outDegree_le a b D v O L
    (fun i s t h hs => mem_filter.mpr ⟨mem_univ _,hA i s t h,⟨s,hs⟩⟩)
    (fun i hi s _ => (hLocal i (mem_filter.mp hi).2.1 s).2)
    (fun i hi => (mem_filter.mp hi).2.2)
  have hin := lifted_union_outDegree_le b a (fun i => reverseArcs (D i)) v P L
    (fun i s t h hs => mem_filter.mpr ⟨mem_univ _,hA i t s h,⟨s,hs⟩⟩)
    (fun i hi s _ => (hLocal i (mem_filter.mp hi).2.1 s).1)
    (fun i hi => (mem_filter.mp hi).2.2)
  have hInv : directedPairUnion b a (fun i => reverseArcs (D i)) =
      reverseArcs (directedPairUnion a b D) := by
    ext x y
    constructor
    · rintro ⟨i,s,t,hs,ht,h⟩
      exact ⟨i,t,s,ht,hs,h⟩
    · rintro ⟨i,s,t,hs,ht,h⟩
      exact ⟨i,t,s,ht,hs,h⟩
  rw [hInv] at hin
  change (inDegree (directedPairUnion a b D) v:ℝ) ≤ _ at hin
  calc
    _ ≤ (P.card:ℝ)*L+(O.card:ℝ)*L := add_le_add hin hout
    _ = ((O.card:ℝ)+(P.card:ℝ))*L := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hCount v) hL

/-- Equation (8.1). A vertex belongs to the sides of at most two
cycle pairs and at most `2κ` reduced pairs, counting both directions. -/
theorem extender_total_degree_bound {V W I : Type*} [Fintype V] [Fintype W] [Fintype I]
    (a b : I → W ↪ V) (C R : I → Digraph W) (cycle reduced : Set I)
    (κ : ℕ) (d d₀ : ℝ) (hκ : 1 ≤ κ) (hd : 0 < d) (hd₀ : 0 ≤ d₀)
    (hOffC : ∀ i ∉ cycle, C i = ⊥) (hOffR : ∀ i ∉ reduced, R i = ⊥)
    (hC : ∀ i ∈ cycle, ∀ s, (inDegree (C i) s:ℝ) ≤ (2*d₀/d)*Fintype.card W ∧
      (outDegree (C i) s:ℝ) ≤ (2*d₀/d)*Fintype.card W)
    (hR : ∀ i ∈ reduced, ∀ s, (inDegree (R i) s:ℝ) ≤ (2*(d₀/(κ:ℝ))/d)*Fintype.card W ∧
      (outDegree (R i) s:ℝ) ≤ (2*(d₀/(κ:ℝ))/d)*Fintype.card W)
    (hCountC : ∀ v : V,
      (univ.filter (fun i => i ∈ cycle ∧ v ∈ Set.range (a i))).card +
        (univ.filter (fun i => i ∈ cycle ∧ v ∈ Set.range (b i))).card ≤ 2)
    (hCountR : ∀ v : V,
      (univ.filter (fun i => i ∈ reduced ∧ v ∈ Set.range (a i))).card +
        (univ.filter (fun i => i ∈ reduced ∧ v ∈ Set.range (b i))).card ≤ 2*κ)
    (hDis : Disjoint (directedPairUnion a b C) (directedPairUnion a b R)) :
    ∀ v, (inDegree (directedPairUnion a b C ⊔ directedPairUnion a b R) v:ℝ) +
      outDegree (directedPairUnion a b C ⊔ directedPairUnion a b R) v ≤
      (8*d₀/d)*Fintype.card W := by
  intro v
  let F := directedPairUnion a b C
  let G := directedPairUnion a b R
  have hc := lifted_union_degree_le a b C cycle _ 2 (by positivity) hOffC hC hCountC v
  have hr := lifted_union_degree_le a b R reduced _ (2*κ)
    (by positivity) hOffR hR hCountR v
  have he : (F ⊔ G) \ G = F := by
    ext x y
    rw [Digraph.sdiff_adj,Digraph.sup_adj]
    constructor
    · rintro ⟨h,hn⟩
      exact h.elim id (fun hg => (hn hg).elim)
    · intro hf
      exact ⟨Or.inl hf,fun hg => (disjoint_iff_inf_le.mp hDis) ⟨hf,hg⟩⟩
  obtain ⟨hi,ho⟩ := residual_semidegrees (F ⊔ G) G le_sup_right v
  rw [he] at hi ho
  have hSum : (inDegree (F ⊔ G) v:ℝ) + outDegree (F ⊔ G) v =
      ((inDegree F v:ℝ)+outDegree F v)+((inDegree G v:ℝ)+outDegree G v) := by
    rw [← hi,← ho]
    push_cast
    ring
  have hk : (0:ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  rw [hSum]
  apply (add_le_add hc hr).trans
  push_cast
  field_simp
  ring_nf
  rfl

end OverfullWork.DirectedRobustExpansion
