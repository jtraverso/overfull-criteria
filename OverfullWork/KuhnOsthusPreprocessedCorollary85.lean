module

public import OverfullWork.KuhnOsthusPreprocessingReserve
public import OverfullWork.KuhnOsthusCorollary85

@[expose] public section


/-! Apply Corollary 8.5 to the extender selected in Lemma 8.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 900000 in
/-- Fix the sparse expansion parameters and the size threshold before
the physical reserves are constructed. The extender and the original
exceptional factors are the ones returned by Lemma 8.6. -/
theorem exists_kuhn_osthus_process_leftover_on_preprocessing_reserve
    (l j : ℕ) (hl : 2 ≤ l) (hj : 0 < j) (d d₀ ε : ℝ)
    (hd : 0 < d) (hd₀ : 0 < d₀) (hε : 0 < ε) (hεSmall : ε ≤ 1/100)
    (hScale : 800*ε ≤ ((1/1000:ℝ)*(d/4))^2) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {Z : Finset V} {m r t : ℕ} {σ ηS : ℝ}
      {G : Digraph V} {R : Digraph (Fin (l*j))} {X : Fin (l*j) → Finset V}
      (prep : KuhnOsthusPreprocessingReserve G Z R X hj m r t σ d d₀ ε ηS)
      (νR τR : ℝ),
      N ≤ m → (∀ v, ¬ G.Adj v v) →
      50*l+1 ≤ Fintype.card V → 2*(Z.card:ℝ) ≤ (Fintype.card V:ℝ)/((50*l+1:ℕ):ℝ) →
      (10^7:ℝ) ≤ ((50*l+1:ℕ):ℝ)*νR^2 → 0 < νR → νR ≤ 1/3 → νR ≤ τR →
      3 ≤ τR*((l*j:ℕ):ℝ) →
      (∀ i, ¬ R.Adj i i) → IsRealRobust R νR τR →
      (∀ i, 2*τR*((l*j:ℕ):ℝ) ≤ (inDegree R i:ℝ)) →
      (∀ i, 2*τR*((l*j:ℕ):ℝ) ≤ (outDegree R i:ℝ)) →
      ((r*(50*l+1):ℕ):ℝ) ≤ ε*(d₀/((l*j:ℕ):ℝ))*((2*ε)*(50*m)) →
      (1/1000:ℝ)*d₀*(50*m)+((r*(50*l+1):ℕ):ℝ) ≤ 21*((d₀/200-ηS)*(50*m)) →
      ∀ B D : Digraph V, D ≤ G \ (prep.graph ⊔ B) →
        (∀ v, inDegree D v = r ∧ outDegree D v = r) →
        (∀ x y, x ∈ Z → y ∈ Z → ¬ D.Adj x y) →
        ∃ (a : ℕ) (C : Fin a → Equiv.Perm V), matchingUnion C ≤ prep.graph ⊔ D ∧
          (∀ i, HasSpanningCycle (fun x y => C i x = y)) ∧
          (∀ i j, i ≠ j → ∀ v, C i v ≠ C j v) ∧
          let L := (prep.graph ⊔ D) \ matchingUnion C
          (∀ x y, L.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
          ∀ v : ↥Zᶜ, inDegree (induced L Zᶜ) v = t ∧ outDegree (induced L Zᶜ) v = t := by
  let ζ := (1/1000:ℝ)
  have hζ : 0 < ζ := by norm_num [ζ]
  let γ := min 1 (ζ*d₀)
  have hγ : 0 < γ := lt_min (by norm_num) (by positivity)
  let τ := γ/32
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  let ν := min (τ/4) (min (τ*(ζ*d₀)^2/16) ((1-5*ε)*d₀*(5*ε)/2))
  have hSmall : 0 < 1-5*ε := by linarith only [hεSmall]
  have hν : 0 < ν := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hντ : 2*ν ≤ τ := by linarith only [(min_le_left _ _ : ν ≤ τ/4),hτ]
  have hτγ : 16*τ ≤ γ := by dsimp only [τ]; linarith only [hγ]
  have hνDiscard : 8*ν ≤ τ*(ζ*d₀)^2 := by
    have hp : ν ≤ τ*(ζ*d₀)^2/16 := (min_le_right _ _).trans (min_le_left _ _)
    calc
      8*ν ≤ 16*ν := by linarith only [hν]
      _ ≤ τ*(ζ*d₀)^2 := by simpa only [mul_comm (16:ℝ) ν] using (le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mp hp
  have hνDensity : ν < (1-5*ε)*d₀*(5*ε) := by
    have hp : ν ≤ (1-5*ε)*d₀*(5*ε)/2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hp,hν]
  obtain ⟨N,hN⟩ := kuhn_osthus_corollary_8_5_of_sampled_reserves.{u}
    d d₀ ε ζ ν τ γ (l*j) (Nat.mul_pos (by omega) hj) hd hd₀ hε hεSmall hζ hν hντ hτγ
    (min_le_left _ _) (min_le_right _ _) (by linarith only [hScale])
    hνDiscard hνDensity
  let c := ⌈16/(21*(ζ*d₀)^2)⌉₊
  refine ⟨max N c,?_⟩
  intro V _ Z m r t σ ηS G R X prep νR τR hM hLoop hHost hZ hSlots hνR hνR₁ hνRτ hn
    hReducedLoop hRob hIn hOut hPay hStyles B D hD hRegular hIndependent
  have hC : (c:ℝ) ≤ m := by exact_mod_cast (show c ≤ m from (le_max_right _ _).trans hM)
  have hDiagonal : 16 ≤ (ζ*d₀)^2*(21*m) := by
    have h := (div_le_iff₀ (by positivity : 0 < 21*(ζ*d₀)^2)).mp ((Nat.le_ceil _).trans hC)
    linarith only [h]
  have hCover (x : V) (hx : x ∉ Z) : ∃ i, x ∈ prep.pack.cell i := by
    let v : ↥Zᶜ := ⟨x,mem_compl.mpr hx⟩
    have hMem : x ∈ X (prep.cluster v) := (prep.coordinate (prep.cluster v) v).mp rfl
    rw [←prep.pack.cover (prep.cluster v)] at hMem
    obtain ⟨a,_,ha⟩ := mem_biUnion.mp hMem
    exact ⟨(a,prep.cluster v),ha⟩
  obtain ⟨Q,hQ,_⟩ := assemble_preprocessing_factors_from_wound_intervals G Z prep.label prep.pack.cell m hl hj
    prep.pack.disjoint hCover (fun i => (prep.pack.size i).1) prep.style_label prep.pack.factors
  have hDegree (v : V) : let a := if v ∈ Z then r*(50*l+1) else r*(50*l+1)+t
      inDegree prep.graph v+r = a ∧ outDegree prep.graph v+r = a := by
    have hEq : r*(50*l+1) = 50*l*r+r := by ring
    have h := prep.degree v
    by_cases hv : v ∈ Z
    · simp only [if_pos hv,hEq] at h ⊢
      omega
    · simp only [if_neg hv,hEq] at h ⊢
      omega
  have hFactors (i : Fin r) : (Q i).digraph ≤ prep.graph ∧ Disjoint (Q i).digraph prep.extender := by
    rw [hQ]
    exact ⟨(le_iSup (fun i => ⨆ a, (prep.pack.factors i a).digraph) i).trans prep.contains_factors,
      prep.factors_disjoint.mono_left (le_iSup (fun i => ⨆ a, (prep.pack.factors i a).digraph) i)⟩
  exact hN G prep.graph B prep.extender Q R prep.chord prep.successor prep.cluster m
    ((d₀/200-ηS)*(50*m)) νR τR ((le_max_left _ _).trans hM) hLoop hDegree prep.extender_le
    prep.induced_extender hFactors (by intro i j hij; rw [hQ,hQ]; exact prep.pack.apart hij)
    prep.pairs hHost hZ hSlots hνR hνR₁ hνRτ hn hReducedLoop hRob hIn hOut hDiagonal hPay hStyles
    D hD hRegular hIndependent

end OverfullWork.DirectedRobustExpansion
