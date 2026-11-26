module

public import OverfullWork.ChenShanNestedPairBounds
public import OverfullWork.ChenShanNestedSamplingBudget
public import OverfullWork.ChenShanPermutationPrefixes
public import OverfullWork.ChenShanThreeOrderings

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real UniformSubsetSampling
open scoped Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

/-- The three nested classes, with the exact core and rounded color sizes. -/
structure NestedTripartitePrefixes (A B W : Type*) [Fintype A] [Fintype B] [Fintype W]
    (ρ : ℝ) (m k l : ℕ) where
  left : ℕ → Finset A
  right : ℕ → Finset B
  colors : ℕ → Finset W
  leftAntitone : Antitone left
  rightAntitone : Antitone right
  colorsAntitone : Antitone colors
  leftFull : left 0 = univ
  rightFull : right 0 = univ
  colorsFull : colors 0 = univ
  leftSize : ∀ i ≤ l, (left i).card = nestedCoreSize ρ m i
  rightSize : ∀ i ≤ l, (right i).card = nestedCoreSize ρ m i
  colorsSize : ∀ i ≤ l, (colors i).card = nestedColorSize ((k:ℝ)/m) (nestedCoreSize ρ m i)

def PrefixDegreeControl (E : A → B → Prop) (S : ℕ → Finset A)
    (T : ℕ → Finset B) (m : ℕ → ℕ) (l : ℕ) (ξ : ℝ) : Prop :=
  ∀ i ≤ l, ∀ r ≤ 2, i+r ≤ l → ∀ v ∈ S i,
    sampledDegreeError E v (T (i+r)) ≤ ξ*m (i+r)

structure TripartitePrefixDegreeControl {ρ : ℝ} {m k l : ℕ}
    (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (S : NestedTripartitePrefixes A B W ρ m k l) (ξ : ℝ) : Prop where
  leftRight : PrefixDegreeControl E S.left S.right (nestedCoreSize ρ m) l ξ
  rightLeft : PrefixDegreeControl (fun b a => E a b) S.right S.left (nestedCoreSize ρ m) l ξ
  leftColors : PrefixDegreeControl L S.left S.colors (nestedCoreSize ρ m) l ξ
  colorsLeft : PrefixDegreeControl (fun w a => L a w) S.colors S.left (nestedCoreSize ρ m) l ξ
  rightColors : PrefixDegreeControl R S.right S.colors (nestedCoreSize ρ m) l ξ
  colorsRight : PrefixDegreeControl (fun w b => R b w) S.colors S.right (nestedCoreSize ρ m) l ξ

omit [Fintype A] in
private theorem prefixDegreeControl_of_not_fails
    (E : A → B → Prop) (S : ℕ → Finset A) (T : ℕ → Finset B)
    (m : ℕ → ℕ) (l : ℕ) (ξ : ℝ) (permA : Equiv.Perm A) (permB : Equiv.Perm B)
    (h : ¬failsDegreeSample E S T m l ξ permA permB) :
    PrefixDegreeControl E (fun i => permutationImage (S i) permA)
      (fun i => permutationImage (T i) permB) m l ξ := by
  intro i hi r hr hEnd v hv
  apply le_of_not_gt
  exact fun hBad => h ⟨⟨i,by omega⟩,⟨r,by omega⟩,hEnd,v,hv,hBad⟩

/-- Equation (4.20) of Chen–Shan. All six kinds of degree tests, at
the current and the next two retained levels, hold for one choice
of the three orderings. The cutoff can exceed any prescribed bound. -/
theorem exists_tripartite_prefix_degree_control (ρ ξ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1/2)
    (hξ : 0 < ξ) (hξ₁ : ξ ≤ 1) (hmin : ℕ) :
    ∃ h : ℕ, hmin ≤ h ∧ 4 ≤ h ∧ ∀ (m k : ℕ), h ≤ m →
    (m : ℝ)/2 ≤ k → (k:ℝ) ≤ 2*m →
    ∀ (A : Type*) (B : Type*) (W : Type*) [Fintype A] [Fintype B] [Fintype W],
      Fintype.card A = m → Fintype.card B = m → Fintype.card W = k →
    ∀ (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop),
      ∃ l : ℕ, (∀ i ≤ l, h ≤ nestedCoreSize ρ m i) ∧
        nestedCoreSize ρ m (l+1) < h ∧ (nestedCoreSize ρ m l : ℝ) < h/ρ ∧
        ∃ S : NestedTripartitePrefixes A B W ρ m k l, TripartitePrefixDegreeControl E L R S ξ := by
  let a := ξ^2*ρ^2/144
  obtain ⟨h,hh,h4,hSizes⟩ := exists_nested_core_with_sampling_budget_above ρ 108 a 1 hmin
    hρ hρ₁ (by norm_num) (by dsimp only [a]; positivity) (by norm_num)
  refine ⟨h,hh,h4,?_⟩
  intro m k hm hk₀ hk₁ A B W _ _ _ hA hB hW E L R
  obtain ⟨l,hKeep,hExit,hTop,hCost⟩ := hSizes m hm
  let s := nestedCoreSize ρ m
  let ratio := (k : ℝ)/m
  let c (i : ℕ) := nestedColorSize ratio (s i)
  have hm₀ : 0 < m := by omega
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm₀
  have hkR : 0 < (k:ℝ) := by linarith only [hk₀,hmR]
  have hkPos : 0 < k := by exact_mod_cast hkR
  have hRatio₀ : 1/2 ≤ ratio := (le_div_iff₀ hmR).mpr (by linarith only [hk₀])
  have hRatio₁ : ratio ≤ 2 := (div_le_iff₀ hmR).mpr hk₁
  have hRatio : 0 ≤ ratio := by dsimp only [ratio]; positivity
  have hs : Antitone s :=
    antitone_nat_of_succ_le (nestedCoreSize_monotone_down ρ (by linarith only [hρ₁]) m)
  have hc : Antitone c := fun _ _ h => nestedColorSize_mono ratio hRatio (hs h)
  have hc₀ : c 0 = k := nestedColorSize_at_full k m hm₀
  have hsCap (i : ℕ) : s i ≤ m := hs (Nat.zero_le i)
  have hcCap (i : ℕ) : c i ≤ k := (hc (Nat.zero_le i)).trans_eq hc₀
  have hcBounds (i : ℕ) (hi : i ≤ l) : (s i : ℝ)/4 ≤ c i ∧ (c i : ℝ) ≤ 3*s i := by
    have hErr := abs_le.mp (nestedColorSize_error ratio hRatio (s i))
    have h4i : (4:ℝ) ≤ s i := by exact_mod_cast h4.trans (hKeep i hi)
    have hLo := mul_le_mul_of_nonneg_right hRatio₀ (Nat.cast_nonneg (α := ℝ) (s i))
    have hHi := mul_le_mul_of_nonneg_right hRatio₁ (Nat.cast_nonneg (α := ℝ) (s i))
    change -(1/2) ≤ ((c i : ℝ)-ratio*s i) ∧ ((c i : ℝ)-ratio*s i) ≤ 1/2 at hErr
    constructor <;> linarith only [hErr.1,hErr.2,h4i,hLo,hHi]
  let SA (i : ℕ) := initialSegment A (s i)
  let SB (i : ℕ) := initialSegment B (s i)
  let SW (i : ℕ) := initialSegment W (c i)
  have hSA (i : ℕ) : (SA i).card = s i :=
    card_initialSegment _ _ ((hsCap i).trans_eq hA.symm)
  have hSB (i : ℕ) : (SB i).card = s i :=
    card_initialSegment _ _ ((hsCap i).trans_eq hB.symm)
  have hSW (i : ℕ) : (SW i).card = c i :=
    card_initialSegment _ _ ((hcCap i).trans_eq hW.symm)
  have bA (i : ℕ) (_hi : i ≤ l) : (s i : ℝ)/4 ≤ (SA i).card ∧
      ((SA i).card : ℝ) ≤ 3*s i := by
    rw [hSA]
    constructor <;> linarith only [Nat.cast_nonneg (α := ℝ) (s i)]
  have bB (i : ℕ) (_hi : i ≤ l) : (s i : ℝ)/4 ≤ (SB i).card ∧
      ((SB i).card : ℝ) ≤ 3*s i := by
    rw [hSB]
    constructor <;> linarith only [Nat.cast_nonneg (α := ℝ) (s i)]
  have bW (i : ℕ) (hi : i ≤ l) : (s i : ℝ)/4 ≤ (SW i).card ∧
      ((SW i).card : ℝ) ≤ 3*s i := by rw [hSW]; exact hcBounds i hi
  let budget := ∑ i : Fin (l+1), 18*(s i : ℝ)*exp (-a*s i)
  have hBudget : 6*budget < 1 := by
    change (∑ i ∈ range (l+1), 108*(s i : ℝ)*exp (-a*s i)) < 1 at hCost
    refine lt_of_eq_of_lt ?_ hCost
    dsimp only [budget]
    rw [mul_sum,Fin.sum_univ_eq_sum_range (fun i : ℕ => 6*(18*(s i : ℝ)*exp (-a*s i)))]
    apply sum_congr rfl
    intro i _
    ring
  have hρ' : ρ ≤ 1 := by linarith only [hρ₁]
  have hA₀ := hm₀.trans_eq hA.symm
  have hB₀ := hm₀.trans_eq hB.symm
  have hW₀ := hkPos.trans_eq hW.symm
  obtain ⟨permA,permB,permW,hAB,hBA,hAW,hWA,hBW,hWB⟩ :=
    exists_three_orderings_of_pair_bounds
      (failsDegreeSample E SA SB s l ξ)
      (failsDegreeSample (fun b a => E a b) SB SA s l ξ)
      (failsDegreeSample L SA SW s l ξ)
      (failsDegreeSample (fun w a => L a w) SW SA s l ξ)
      (failsDegreeSample R SB SW s l ξ)
      (failsDegreeSample (fun w b => R b w) SW SB s l ξ)
      budget hBudget
      (failsDegreeSample_nested_card_le E SA SB ρ ξ m l hρ.le hρ' hξ.le hξ₁ hA₀
        (fun i hi => (bA i hi).2) bB)
      (failsDegreeSample_nested_card_le (fun b a => E a b) SB SA ρ ξ m l hρ.le hρ' hξ.le hξ₁ hB₀
        (fun i hi => (bB i hi).2) bA)
      (failsDegreeSample_nested_card_le L SA SW ρ ξ m l hρ.le hρ' hξ.le hξ₁ hA₀
        (fun i hi => (bA i hi).2) bW)
      (failsDegreeSample_nested_card_le (fun w a => L a w) SW SA ρ ξ m l hρ.le hρ' hξ.le hξ₁ hW₀
        (fun i hi => (bW i hi).2) bA)
      (failsDegreeSample_nested_card_le R SB SW ρ ξ m l hρ.le hρ' hξ.le hξ₁ hB₀
        (fun i hi => (bB i hi).2) bW)
      (failsDegreeSample_nested_card_le (fun w b => R b w) SW SB ρ ξ m l hρ.le hρ' hξ.le hξ₁ hW₀
        (fun i hi => (bW i hi).2) bB)
  let S : NestedTripartitePrefixes A B W ρ m k l := {
    left := fun i => permutationImage (SA i) permA
    right := fun i => permutationImage (SB i) permB
    colors := fun i => permutationImage (SW i) permW
    leftAntitone := fun _ _ h => permutation_prefix_mono permA (hs h)
    rightAntitone := fun _ _ h => permutation_prefix_mono permB (hs h)
    colorsAntitone := fun _ _ h => permutation_prefix_mono permW (hc h)
    leftFull := by dsimp [SA,s,nestedCoreSize]; rw [← hA]; exact permutation_prefix_full permA
    rightFull := by dsimp [SB,s,nestedCoreSize]; rw [← hB]; exact permutation_prefix_full permB
    colorsFull := by dsimp only [SW]; rw [hc₀,← hW]; exact permutation_prefix_full permW
    leftSize := fun i _ => (card_map _).trans (hSA i)
    rightSize := fun i _ => (card_map _).trans (hSB i)
    colorsSize := fun i _ => (card_map _).trans (hSW i) }
  exact ⟨l,hKeep,hExit,hTop,S,
    prefixDegreeControl_of_not_fails _ _ _ _ _ _ _ _ hAB,
    prefixDegreeControl_of_not_fails _ _ _ _ _ _ _ _ hBA,
    prefixDegreeControl_of_not_fails _ _ _ _ _ _ _ _ hAW,
    prefixDegreeControl_of_not_fails _ _ _ _ _ _ _ _ hWA,
    prefixDegreeControl_of_not_fails _ _ _ _ _ _ _ _ hBW,
    prefixDegreeControl_of_not_fails _ _ _ _ _ _ _ _ hWB⟩

end OverfullWork.ChenShan
