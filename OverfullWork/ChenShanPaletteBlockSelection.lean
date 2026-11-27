module

public import OverfullWork.ChenShanJointBlockSampling
public import OverfullWork.ChenShanDisjointPaletteSampling
public import OverfullWork.ChenShanPaletteCapacity
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {I : Type*} [Fintype I] {V : I → Type*} [∀ i, Fintype (V i)]

omit [Fintype I] in
/-- Given the exact part quotas, seed fine blocks by a partition and
seed each coarse block by the union of its designated fine blocks. -/
theorem exists_fine_coarse_seeds {F C : Type*} [Fintype F]
    (group : F → C) (s : F ⊕ C → I → ℕ)
    (hFine : ∀ i, (∑ f : F, s (.inl f) i) = Fintype.card (V i))
    (hCoarse : ∀ c i, (∑ f ∈ univ.filter (fun f => group f = c), s (.inl f) i) = s (.inr c) i) :
    ∃ seed : F → ∀ i, Finset (V i),
      (∀ i, Pairwise (fun f g => Disjoint (seed f i) (seed g i))) ∧
      (∀ i, (univ : Finset F).biUnion (fun f => seed f i) = univ) ∧
      (∀ f i, (seed f i).card = s (.inl f) i) ∧
      ∀ c i, ((univ.filter (fun f => group f = c)).biUnion (fun f => seed f i)).card =
        s (.inr c) i := by
  classical
  have hSeeds (i : I) := exists_disjoint_palette_seeds (W := V i)
    (fun f : F => s (.inl f) i) (hFine i).le
  choose B hCard hDisj using hSeeds
  refine ⟨fun f i => B i f,hDisj,?_,fun f i => hCard i f,?_⟩
  · intro i
    apply eq_univ_of_card
    rw [card_biUnion (fun _ _ _ _ h => hDisj i h)]
    simpa only [hCard] using hFine i
  · intro c i
    rw [card_biUnion (fun _ _ _ _ h => hDisj i h)]
    simpa only [hCard] using hCoarse c i

/-- The multiset of edges tested for capacity on one side. Internal
edge copies are indexed by E. The rows of w are the exceptional
vertices whose preferred side is the opposite side. -/
structure PaletteBlockCapacityInput (W Z E : Type*) where
  left : E → W
  right : E → W
  exceptional : Finset Z
  weight : Z → W → ℝ

noncomputable def PaletteBlockCapacityInput.edgeCount {W Z E : Type*} [Fintype W] [Fintype E]
    (A : PaletteBlockCapacityInput W Z E) : ℝ :=
  (Fintype.card E:ℝ) + ∑ z ∈ A.exceptional, ∑ w, A.weight z w

/-- Admissibility of a large capacity test for a specified block and
palette, using the incidence bounds from (5.5). -/
structure PaletteBlockCapacityInput.Admissible {W Z E : Type*} [Fintype W] [Fintype E]
    (A : PaletteBlockCapacityInput W Z E) (p fraction a : ℝ) (c : Z → ℝ) : Prop where
  distinct : ∀ e, A.left e ≠ A.right e
  weight_bounds : ∀ z ∈ A.exceptional, ∀ w, 0 ≤ A.weight z w ∧ A.weight z w ≤ a
  degree_bound : ∀ w, internalEdgeIncidences A.left A.right w +
    (∑ z ∈ A.exceptional, A.weight z w) ≤ a
  opposite_degree : ∀ z ∈ A.exceptional, (∑ w, A.weight z w) ≤ c z/2
  palette_rounding : ∀ z ∈ A.exceptional, 64 ≤ fraction*c z
  small_incidence : ∀ z ∈ A.exceptional, a ≤ p*c z/4096

noncomputable def PaletteBlockCapacityInput.statistic {W Z E : Type*} [Fintype E]
    (A : PaletteBlockCapacityInput W Z E) (p fraction : ℝ) (c : Z → ℝ)
    (X : Finset W) : ℝ :=
  subsetBlockCapacity A.left A.right A.exceptional A.weight
    (fun z => (⌊(15/16:ℝ)*fraction*c z⌋₊ : ℝ)) (64*fraction/p) (64*fraction/p^2) X

/-- Number of ordinary representative edges meeting a sampled block.
The representative edges have distinct core endpoints. -/
noncomputable def ordinaryBlockPreferred (s : I → ℕ) (A : ∀ i, Finset (V i))
    (X : BlockParts (V := V) s) : ℝ :=
  ∑ i, ((A i ∩ (X i).val).card:ℝ)

/-- Number of edges, counted with multiplicity, from a special
vertex to its preferred side of the block. -/
noncomputable def specialBlockPreferred (s : I → ℕ) (w : ∀ i, V i → ℝ)
    (X : BlockParts (V := V) s) : ℝ :=
  ∑ i, ∑ v ∈ (X i).val, w i v


set_option maxHeartbeats 1600000 in
/-- The block-selection step of §5.1.2. An ordinary vertex is tested
using distinct representatives, an active special vertex using its
preferred incidences, and each large side using the capacity statistic.
All tests use one partition, with the coarse blocks obtained by grouping
its fine blocks. -/
theorem exists_palette_blocks_with_preferred_edges_and_capacity
    {F C O Q L Z : Type*} [Fintype F] [Fintype C] [Fintype O] [Fintype Q] [Fintype L]
    {E : L → Type*} [∀ l, Fintype (E l)]
    (β θ δ ζ Corder Ctests Dtests Etests : ℝ)
    (hβ : 0 < β) (hθ : 0 < θ) (hδ : 0 < δ) (hζ : 0 < ζ) (hOrder : 0 < Corder)
    (hCtests : 0 ≤ Ctests) (hDtests : 0 ≤ Dtests) (hEtests : 0 ≤ Etests) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
    ∀ (k : ℕ), 0 < k → N ≤ k →
    ∀ (a : ℝ), 0 ≤ a → a ≤ ε*k →
    ∀ (group : F → C) (s : F ⊕ C → I → ℕ) (p fraction : F ⊕ C → ℝ),
      (∀ i, (∑ f : F, s (.inl f) i) = Fintype.card (V i)) →
      (∀ c i, (∑ f ∈ univ.filter (fun f => group f = c), s (.inl f) i) = s (.inr c) i) →
      (∀ b i, 2 ≤ s b i) →
      (∀ b i, (s b i:ℝ)/Fintype.card (V i) = p b) →
      (∀ b, δ ≤ p b) → (∀ b, p b ≤ 1) → (∀ b, 0 < fraction b) →
      (∑ i, (Fintype.card (V i):ℝ)) ≤ Corder*k →
      (Fintype.card ((F ⊕ C) × O):ℝ) ≤ Ctests*k →
      (Fintype.card ((F ⊕ C) × Q):ℝ) ≤ Dtests →
      (Fintype.card ((F ⊕ C) × L):ℝ) ≤ Etests →
    ∀ (cO : O → ℝ) (AO : O → ∀ i, Finset (V i))
      (cQ : Q → ℝ) (wQ : Q → ∀ i, V i → ℝ) (c : Z → ℝ)
      (A : ∀ l, PaletteBlockCapacityInput (Σ i, V i) Z (E l)),
      (∀ o, θ*k ≤ cO o) →
      (∀ o, β*cO o/4 ≤ ∑ i, ((AO o i).card:ℝ)) →
      (∀ q, θ*k ≤ cQ q) →
      (∀ q, cQ q/2 ≤ ∑ i, ∑ v, wQ q i v) →
      (∀ q i v, 0 ≤ wQ q i v ∧ wQ q i v ≤ a) →
      (∀ l, ζ*k ≤ (A l).edgeCount) →
      (∀ b l, (A l).Admissible (p b) (fraction b) a c) →
    ∃ X : (b : F ⊕ C) → BlockParts (V := V) (s b),
      (∀ b o, β*p b*cO o/8 ≤ ordinaryBlockPreferred (s b) (AO o) (X b)) ∧
      (∀ b q, p b*cQ q/3 ≤ specialBlockPreferred (s b) (wQ q) (X b)) ∧
      (∀ b l, (13/8:ℝ)*fraction b*(A l).edgeCount ≤
        (A l).statistic (p b) (fraction b) c (blockPartsSelected (s b) (X b))) ∧
      (∀ i, Pairwise (fun f g => Disjoint (X (.inl f) i).val (X (.inl g) i).val)) ∧
      (∀ i, (univ : Finset F).biUnion (fun f => (X (.inl f) i).val) = univ) ∧
      ∀ g i, (X (.inr g) i).val =
        (univ.filter (fun f => group f = g)).biUnion (fun f => (X (.inl f) i).val) := by
  classical
  let η := β*θ/4
  let γ := δ*η^2/(16*Corder)
  let u := 18/(δ*θ)
  let v := (2:ℝ)^21/(δ^3*ζ)
  have hη : 0 < η := by positivity
  obtain ⟨ε,hε,N,hRiskSum⟩ := exists_joint_block_risk_threshold Ctests γ Dtests Etests u v
    hCtests (by positivity) hDtests hEtests (by positivity) (by positivity)
  refine ⟨ε,hε,N,?_⟩
  intro k hk hkN a ha haε group s p fraction hFine hCoarse hTwo hFrac hp hpOne hf hSize
    hCountO hCountQ hCountL cO AO cQ wQ c A hcO hAO hcQ hwQ hWeights hLarge hA
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  obtain ⟨seed,hDisj,hCover,hSeed,hSeedCoarse⟩ := exists_fine_coarse_seeds (V := V) group s hFine hCoarse
  let S : (F ⊕ C) → ∀ i, Finset (V i) := Sum.elim seed
    (fun g i => (univ.filter (fun f => group f = g)).biUnion (fun f => seed f i))
  have hSeedSize (b : F ⊕ C) (i : I) : (S b i).card = s b i := by
    cases b with
    | inl f => exact hSeed f i
    | inr g => exact hSeedCoarse g i
  have hs (b : F ⊕ C) (i : I) : s b i ≤ Fintype.card (V i) :=
    (hSeedSize b i) ▸ card_le_univ (S b i)
  let B := F ⊕ C
  let J := (B × O) ⊕ ((B × Q) ⊕ (B × L))
  let block : J → B := Sum.elim Prod.fst (Sum.elim Prod.fst Prod.fst)
  let badO (j : B × O) (t : BlockParts (V := V) (s j.1)) : Prop :=
    ordinaryBlockPreferred (s j.1) (AO j.2) t < β*p j.1*cO j.2/8
  let badQ (j : B × Q) (t : BlockParts (V := V) (s j.1)) : Prop :=
    specialBlockPreferred (s j.1) (wQ j.2) t < p j.1*cQ j.2/3
  let badL (j : B × L) (t : BlockParts (V := V) (s j.1)) : Prop :=
    (A j.2).statistic (p j.1) (fraction j.1) c (blockPartsSelected (s j.1) t) <
      (13/8:ℝ)*fraction j.1*(A j.2).edgeCount
  let bad : (j : J) → BlockParts (V := V) (s (block j)) → Prop :=
    fun j => match j with
      | .inl j => badO j
      | .inr (.inl j) => badQ j
      | .inr (.inr j) => badL j
  let rO (_ : B × O) := Real.exp (-γ*k)
  let rQ (_ : B × Q) := u*(a/k)
  let rL (_ : B × L) := v*(a/k)
  let risk : J → ℝ := Sum.elim rO (Sum.elim rQ rL)
  have hSum : (∑ j, risk j) < 1 := by
    have h := hRiskSum k hk hkN a ha haε hCountO hCountQ hCountL rO rQ rL
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    change (∑ j : (B × O) ⊕ ((B × Q) ⊕ (B × L)), risk j) < 1
    rw [Fintype.sum_sum_type risk, Fintype.sum_sum_type (fun j : (B × Q) ⊕ (B × L) => risk (.inr j))]
    simpa only [risk, Sum.elim_inl, Sum.elim_inr, add_assoc] using h
  have hpPos (b : B) : 0 < p b := hδ.trans_le (hp b)
  have hTailO (j : B × O) :
      blockMean (blockPartsMass (s j.1)) (fun t => eventIndicator (badO j t)) ≤ rO j := by
    let d : ℝ := ∑ i, ((AO j.2 i).card:ℝ)
    let n : ℝ := ∑ i, (Fintype.card (V i):ℝ)
    have hLower : η*k ≤ d := by
      have h := mul_le_mul_of_nonneg_left (hcO j.2) hβ.le
      dsimp only [η]
      nlinarith only [h,hAO j.2]
    have hd : 0 < d := (mul_pos hη hkR).trans_le hLower
    have hn : 0 < n := hd.trans_le (sum_le_sum (fun i _ => by exact_mod_cast card_le_univ (AO j.2 i)))
    have hThresh : β*p j.1*cO j.2/8 ≤ p j.1*d/2 := by
      have h := mul_le_mul_of_nonneg_left (hAO j.2) (hpPos j.1).le
      nlinarith only [h]
    have hEvent (t : BlockParts (V := V) (s j.1)) :
        eventIndicator (badO j t) ≤ eventIndicator (ordinaryBlockPreferred (s j.1) (AO j.2) t < p j.1*d/2) := by
      by_cases h : badO j t
      · have h' := (show ordinaryBlockPreferred (s j.1) (AO j.2) t < _ from h).trans_le hThresh
        simp only [eventIndicator, ite_eq_left h, ite_eq_left h', le_refl]
      · simp only [eventIndicator, ite_eq_right h]
        positivity
    have hMono := sum_le_sum (s := (univ : Finset (BlockParts (V := V) (s j.1))))
      (fun t _ => mul_le_mul_of_nonneg_left (hEvent t) (blockPartsMass_nonneg (s j.1) t))
    exact hMono.trans ((sampled_ordinary_preferred_edges_lower_tail (s j.1) (p j.1)
      (hs j.1) (hFrac j.1) (hpPos j.1) (AO j.2) hd).trans
      (ordinary_preferred_risk_le_exp hkR hn hδ hη hOrder (hp j.1) hLower hSize))
  have hTailQ (j : B × Q) :
      blockMean (blockPartsMass (s j.1)) (fun t => eventIndicator (badQ j t)) ≤ rQ j := by
    have hc := (mul_pos hθ hkR).trans_le (hcQ j.2)
    exact (sampled_special_preferred_degree_lower_tail (s j.1) (p j.1) a (cQ j.2)
      (hs j.1) (hFrac j.1) (hpPos j.1) ha hc (wQ j.2) (hWeights j.2) (hwQ j.2)).trans
      (preferred_and_capacity_risk_le hkR hδ hθ hζ ha (hp j.1) (hcQ j.2)
        (show ζ*(k:ℝ) ≤ ζ*k from le_rfl)).1
  have hTailL (j : B × L) :
      blockMean (blockPartsMass (s j.1)) (fun t => eventIndicator (badL j t)) ≤ rL j := by
    have hPos := (mul_pos hζ hkR).trans_le (hLarge j.2)
    have h := hA j.1 j.2
    exact (sampled_block_capacity_lower_tail (s j.1) (p j.1) (fraction j.1) a (hs j.1)
      (hTwo j.1) (hFrac j.1) (hpPos j.1) (hpOne j.1) (hf j.1) ha (A j.2).left (A j.2).right
      h.distinct (A j.2).exceptional (A j.2).weight c h.weight_bounds h.degree_bound
      h.opposite_degree h.palette_rounding h.small_incidence hPos).trans
      (preferred_and_capacity_risk_le hkR hδ hθ hζ ha (hp j.1)
        (show θ*(k:ℝ) ≤ θ*k from le_rfl) (hLarge j.2)).2
  have hTail (j : J) : blockMean (blockPartsMass (s (block j)))
      (fun t => eventIndicator (bad j t)) ≤ risk j := by
    rcases j with j | (j | j)
    · exact hTailO j
    · exact hTailQ j
    · exact hTailL j
  obtain ⟨X, hGood, hDisjoint, hCovers, hUnion⟩ :=
    exists_tested_fine_and_coarse_blocks seed group hDisj hCover s S
      (fun _ _ => rfl) (fun _ _ => rfl) hSeedSize block bad risk hTail hSum
  exact ⟨X, (fun b o => le_of_not_gt (hGood (.inl (b,o)))),
    (fun b q => le_of_not_gt (hGood (.inr (.inl (b,q))))),
    (fun b l => le_of_not_gt (hGood (.inr (.inr (b,l))))), hDisjoint, hCovers, hUnion⟩


/-- Index the fine blocks by seven groups, each with g labels. -/
abbrev SevenCoarseBlockLabel (g : ℕ) := (Fin 7 × Fin g) ⊕ Fin 7

def sevenCoarseBlockQuota {g : ℕ} (t : I → ℕ) (b : SevenCoarseBlockLabel g) (i : I) : ℕ :=
  Sum.elim (fun _ => t i) (fun _ => g*t i) b

noncomputable def sevenCoarseBlockFraction {g : ℕ} (b : SevenCoarseBlockLabel g) : ℝ :=
  Sum.elim (fun _ => 1/(7*(g:ℝ))) (fun _ => 1/7) b

omit [Fintype I] in
/-- If each part has size (7g)t, every fine block takes t vertices
and every coarse block takes gt. These are exactly the fractions
1/(7g) and 1/7 used in §5.1.2. -/
theorem seven_coarse_block_quotas {g : ℕ} (hg : 0 < g) (t : I → ℕ)
    (ht : ∀ i, 2 ≤ t i) (hOrder : ∀ i, Fintype.card (V i) = 7*g*t i) :
    let s := sevenCoarseBlockQuota (g := g) t
    let p := sevenCoarseBlockFraction (g := g)
    (∀ i, (∑ f : Fin 7 × Fin g, s (.inl f) i) = Fintype.card (V i)) ∧
    (∀ c i, (∑ f ∈ univ.filter (fun f : Fin 7 × Fin g => f.1 = c), s (.inl f) i) = s (.inr c) i) ∧
    (∀ b i, 2 ≤ s b i) ∧
    (∀ b i, (s b i:ℝ)/Fintype.card (V i) = p b) ∧
    (∀ b, 1/(7*(g:ℝ)) ≤ p b ∧ p b ≤ 1) := by
  intro s p
  have hgR : (0:ℝ) < g := by exact_mod_cast hg
  have hg₁ : (1:ℝ) ≤ g := by exact_mod_cast hg
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    simp [s, sevenCoarseBlockQuota, hOrder, Fintype.card_prod]
  · intro c i
    have hSet : (univ.filter (fun f : Fin 7 × Fin g => f.1 = c)) =
        ({c} : Finset (Fin 7)) ×ˢ (univ : Finset (Fin g)) := by
      ext f
      simp only [mem_filter, mem_univ, true_and, Finset.mem_product, mem_singleton, and_true]
    rw [hSet]
    simp [s, sevenCoarseBlockQuota]
  · intro b i
    rcases b with f | c
    · exact ht i
    · change 2 ≤ g*t i
      exact (ht i).trans (Nat.le_mul_of_pos_left _ hg)
  · intro b i
    have htR : (0:ℝ) < t i := by exact_mod_cast ((show 0 < (2:ℕ) by decide).trans_le (ht i))
    rw [hOrder, Nat.cast_mul, Nat.cast_mul]
    rcases b with f | c
    · change (t i:ℝ)/(7*↑g*↑(t i)) = 1/(7*↑g)
      field_simp [hgR.ne',htR.ne']
    · change (↑(g*t i):ℝ)/(7*↑g*↑(t i)) = 1/7
      push_cast
      field_simp [hgR.ne',htR.ne']
  · intro b
    have hFrac : (1:ℝ)/(7*(g:ℝ)) ≤ 1/7 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith only [hg₁]
    rcases b with f | c
    · exact ⟨le_rfl,hFrac.trans (by norm_num)⟩
    · change 1/(7*(g:ℝ)) ≤ 1/7 ∧ (1/7:ℝ) ≤ 1
      exact ⟨hFrac,by norm_num⟩

/-- The floor-cap hypotheses follow uniformly from positive lower
bounds on the palette fraction and the block fraction. -/
theorem palette_block_rounding_and_incidence {k c a θ δ lambdaMin p fraction : ℝ}
    (hk : 0 ≤ k) (hθ : 0 < θ) (hδ : 0 < δ) (hlambdaMin : 0 < lambdaMin)
    (hc : θ*k ≤ c) (hp : δ ≤ p) (hf : lambdaMin ≤ fraction)
    (hLarge : 64/(lambdaMin*θ) ≤ k) (hSmall : a ≤ (δ*θ/4096)*k) :
    64 ≤ fraction*c ∧ a ≤ p*c/4096 := by
  have h₁ := mul_le_mul hf hc (mul_nonneg hθ.le hk) (hlambdaMin.le.trans hf)
  have h₂ := mul_le_mul hp hc (mul_nonneg hθ.le hk) (hδ.le.trans hp)
  have h₃ := (div_le_iff₀ (mul_pos hlambdaMin hθ)).mp hLarge
  constructor
  · nlinarith only [h₁,h₃]
  · nlinarith only [h₂,hSmall]


/-- After selecting a block with the capacity test, deleting at most
p²|Eσ|/512 edges leaves the capacity 3λ|Eσ|/2 used later in §5.1.2. -/
theorem PaletteBlockCapacityInput.statistic_survives_deletions
    {W Z E : Type*} [Fintype W] [Fintype E] (A : PaletteBlockCapacityInput W Z E)
    (p fraction : ℝ) (c : Z → ℝ) (X : Finset W) (b' : ℝ) (d' : Z → ℝ)
    (hp : 0 < p) (hpOne : p ≤ 1) (hf : 0 ≤ fraction)
    (hDegree : ∀ z ∈ A.exceptional, d' z ≤ ∑ w ∈ X, A.weight z w)
    (hBudget :
      (∑ e, eventIndicator (A.left e ∈ X ∧ A.right e ∈ X))-b' +
        (∑ z ∈ A.exceptional, ((∑ w ∈ X, A.weight z w)-d' z)) ≤
          p^2*A.edgeCount/512)
    (hBefore : (13/8:ℝ)*fraction*A.edgeCount ≤ A.statistic p fraction c X) :
    (3/2:ℝ)*fraction*A.edgeCount ≤
      (64*fraction/p^2)*b' + ∑ z ∈ A.exceptional,
        min ((64*fraction/p)*d' z) (⌊(15/16:ℝ)*fraction*c z⌋₊ : ℝ) :=
  palette_capacity_retains_three_halves A.exceptional _ b' p fraction A.edgeCount _
    d' (fun z => (⌊(15/16:ℝ)*fraction*c z⌋₊ : ℝ)) hp hpOne hf hDegree hBudget hBefore

end OverfullWork.ChenShan
