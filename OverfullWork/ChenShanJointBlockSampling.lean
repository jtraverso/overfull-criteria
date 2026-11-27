module

public import OverfullWork.ChenShanOrdinaryPreferredEdges
public import OverfullWork.UniformPartitionSampling
public import OverfullWork.ChenShanNestedSamplingBudget
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset UniformSubsetSampling
open scoped Classical

variable {I : Type*} [Fintype I]

/-- Coordinate maps sending each input law to its output law send
the independent product to the independent product. -/
theorem blockMean_product_map {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (p : ∀ i, A i → ℝ) (q : ∀ i, B i → ℝ) (g : ∀ i, A i → B i)
    (h : ∀ i b, blockMean (p i) (fun a => eventIndicator (g i a = b)) = q i b)
    (f : (∀ i, B i) → ℝ) :
    blockMean (partProductMass p) (fun a => f (fun i => g i (a i))) =
      blockMean (partProductMass q) f := by
  classical
  let map (a : ∀ i, A i) (i : I) := g i (a i)
  have hProd (a : ∀ i, A i) (b : ∀ i, B i) :
      (∏ i, eventIndicator (g i (a i) = b i)) = eventIndicator (map a = b) := by
    by_cases hab : map a = b
    · rw [eventIndicator, ite_eq_left hab]
      exact prod_eq_one (fun i _ => by simpa only [map, eventIndicator] using
        (ite_eq_left (congrFun hab i) : (if map a i = b i then (1:ℝ) else 0) = 1))
    · rw [eventIndicator, ite_eq_right hab]
      obtain ⟨i,hi⟩ : ∃ i, g i (a i) ≠ b i := by
        by_contra! hh
        exact hab (funext hh)
      exact prod_eq_zero (mem_univ i) (by simp only [eventIndicator, ite_eq_right hi])
  have hPush (b : ∀ i, B i) :
      blockMean (partProductMass p) (fun a => eventIndicator (map a = b)) =
        partProductMass q b := by
    simp_rw [← hProd]
    rw [blockMean_product p (fun i a => eventIndicator (g i a = b i))]
    exact prod_congr rfl (fun i _ => h i (b i))
  unfold blockMean
  calc
    _ = ∑ a, partProductMass p a * ∑ b, eventIndicator (map a = b)*f b := by
      apply sum_congr rfl
      intro a _
      change partProductMass p a * f (map a) = _
      congr 1
      rw [sum_eq_single (map a)]
      · simp [eventIndicator]
      · intro b _ hb
        simp only [eventIndicator, ite_eq_right (Ne.symm hb), zero_mul]
      · simp
    _ = ∑ b, (blockMean (partProductMass p) (fun a => eventIndicator (map a = b)))*f b := by
      simp only [mul_sum, blockMean, sum_mul, mul_assoc]
      rw [sum_comm]
    _ = _ := by simp only [hPush]

section Permutations

variable {V : Type*} [Fintype V]

/-- A permutation sends a prescribed seed to a sample of its original size. -/
noncomputable def permutedPartSample (S : Finset V) (s : ℕ) (hs : S.card = s)
    (π : Equiv.Perm V) : PartSample V s :=
  ⟨permutationImage S π, mem_powersetCard.mpr ⟨subset_univ _,(card_map _).trans hs⟩⟩

noncomputable def uniformPermutationMass (_ : Equiv.Perm V) : ℝ :=
  (Fintype.card (Equiv.Perm V):ℝ)⁻¹

private theorem permutedPartSample_mass (S : Finset V) (s : ℕ) (hs : S.card = s)
    (T : PartSample V s) :
    blockMean uniformPermutationMass
      (fun π => eventIndicator (permutedPartSample S s hs π = T)) =
      partSampleMass s T := by
  have hEq (π : Equiv.Perm V) :
      permutedPartSample S s hs π = T ↔ permutationImage S π = T.val :=
    ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩
  let F := @Finset.filter (Equiv.Perm V) (fun π => permutationImage S π = T.val)
    (fun _ => Classical.propDecidable _) univ
  have hSum :
      (∑ π : Equiv.Perm V, eventIndicator (permutationImage S π = T.val)) = (F.card:ℝ) := by
    calc
      _ = ∑ _π ∈ F, (1:ℝ) := by
        simp only [F, sum_filter]
        exact sum_congr rfl (fun π _ => by
          by_cases h : permutationImage S π = T.val <;> simp [eventIndicator,h])
      _ = _ := by simp [nsmul_eq_mul]
  have hP : (F.card:ℝ) = probability s (fun U => U = T.val) *
      (Fintype.card (Equiv.Perm V):ℝ) := by
    simpa only [F, hs] using permutation_probability S (fun U => U = T.val)
  have hOne : @Finset.filter (Finset V) (fun U => U = T.val)
      (fun _ => Classical.propDecidable _) (univ.powersetCard s) = {T.val} := by
    ext U
    simp only [mem_filter, mem_singleton]
    exact ⟨And.right, fun h => ⟨h ▸ T.property,h⟩⟩
  have hCard : (Fintype.card (Equiv.Perm V):ℝ) ≠ 0 := by positivity
  simp only [blockMean, uniformPermutationMass, ← mul_sum, hEq, hSum, partSampleMass]
  rw [hP, probability, hOne, card_singleton, Nat.cast_one]
  rw [mul_left_comm, inv_mul_cancel₀ hCard, mul_one]


end Permutations

variable {V : I → Type*} [∀ i, Fintype (V i)]

/-- A single independent permutation in each part supplies all block
marginals, including a coarse block whose seed is a union of fine seeds. -/
theorem blockMean_permuted_parts (S : ∀ i, Finset (V i)) (s : I → ℕ)
    (hs : ∀ i, (S i).card = s i) (f : BlockParts (V := V) s → ℝ) :
    blockMean (partProductMass (fun _ => uniformPermutationMass))
        (fun π => f (fun i => permutedPartSample (S i) (s i) (hs i) (π i))) =
      blockMean (blockPartsMass s) f :=
  blockMean_product_map _ _ _ (fun i => permutedPartSample_mass (S i) (s i) (hs i)) f


/-- All tests on a family of seeded blocks can be imposed on one
system of part permutations. Only the marginal law of each block
enters the sum of failure bounds. -/
theorem exists_joint_block_permutations {B J : Type*} [Fintype J]
    (S : B → ∀ i, Finset (V i)) (s : B → I → ℕ)
    (hs : ∀ b i, (S b i).card = s b i) (block : J → B)
    (bad : (j : J) → BlockParts (V := V) (s (block j)) → Prop) (risk : J → ℝ)
    (hRisk : ∀ j, blockMean (blockPartsMass (s (block j)))
      (fun t => eventIndicator (bad j t)) ≤ risk j)
    (hSum : (∑ j, risk j) < 1) :
    ∃ π : ∀ i, Equiv.Perm (V i), ∀ j,
      ¬ bad j (fun i => permutedPartSample (S (block j) i) (s (block j) i) (hs (block j) i) (π i)) := by
  let p (i : I) : Equiv.Perm (V i) → ℝ := uniformPermutationMass
  have hp (π : ∀ i, Equiv.Perm (V i)) : 0 ≤ partProductMass p π :=
    prod_nonneg (fun i _ => by unfold p uniformPermutationMass; positivity)
  have hTotal : (∑ π, partProductMass p π) = 1 := by
    have hCard (i : I) : (Fintype.card (Equiv.Perm (V i)):ℝ) ≠ 0 := by positivity
    change (∑ π, ∏ i, p i (π i)) = 1
    rw [← Fintype.prod_sum p]
    simp only [p, uniformPermutationMass, sum_const, card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (hCard _), prod_const_one]
  refine exists_finite_outcome_avoiding (partProductMass p) hp hTotal _ risk (fun j => ?_) hSum
  rw [blockMean_permuted_parts (S (block j)) (s (block j)) (hs (block j))
    (fun t => eventIndicator (bad j t))]
  exact hRisk j

omit [Fintype I] in
/-- Applying a permutation to all the fine blocks also permutes their
union as a single coarse block. -/
theorem permutationImage_biUnion {F W : Type*} [Fintype W]
    (K : Finset F) (S : F → Finset W) (π : Equiv.Perm W) :
    permutationImage (K.biUnion S) π = K.biUnion (fun f => permutationImage (S f) π) := by
  ext w
  simp only [permutationImage, mem_map, mem_biUnion]
  constructor
  · rintro ⟨v,⟨f,hf,hv⟩,rfl⟩
    exact ⟨f,hf,v,hv,rfl⟩
  · rintro ⟨f,hf,v,hv,rfl⟩
    exact ⟨v,⟨f,hf,hv⟩,rfl⟩

/-- Apply the probability budget to fine blocks and to coarse unions
on the same partition. The coarse sets are unions in the selected
outcome, as well as in the seeds. -/
theorem exists_tested_fine_and_coarse_blocks {F C J : Type*} [Fintype F] [Fintype J]
    (seed : F → ∀ i, Finset (V i)) (group : F → C)
    (hDisj : ∀ i, Pairwise (fun f g => Disjoint (seed f i) (seed g i)))
    (hCover : ∀ i, (univ : Finset F).biUnion (fun f => seed f i) = univ)
    (s : F ⊕ C → I → ℕ)
    (S : F ⊕ C → ∀ i, Finset (V i))
    (hFine : ∀ f i, S (.inl f) i = seed f i)
    (hCoarse : ∀ c i, S (.inr c) i = (univ.filter (fun f => group f = c)).biUnion (fun f => seed f i))
    (hs : ∀ b i, (S b i).card = s b i)
    (block : J → F ⊕ C)
    (bad : (j : J) → BlockParts (V := V) (s (block j)) → Prop) (risk : J → ℝ)
    (hRisk : ∀ j, blockMean (blockPartsMass (s (block j)))
      (fun t => eventIndicator (bad j t)) ≤ risk j)
    (hSum : (∑ j, risk j) < 1) :
    ∃ T : (b : F ⊕ C) → BlockParts (V := V) (s b),
      (∀ j, ¬ bad j (T (block j))) ∧
      (∀ i, Pairwise (fun f g => Disjoint (T (.inl f) i).val (T (.inl g) i).val)) ∧
      (∀ i, (univ : Finset F).biUnion (fun f => (T (.inl f) i).val) = univ) ∧
      ∀ c i, (T (.inr c) i).val =
        (univ.filter (fun f => group f = c)).biUnion (fun f => (T (.inl f) i).val) := by
  obtain ⟨π,hπ⟩ := exists_joint_block_permutations S s hs block bad risk hRisk hSum
  refine ⟨fun b i => permutedPartSample (S b i) (s b i) (hs b i) (π i),hπ,?_,?_,?_⟩
  · intro i f g hfg
    simp only [permutedPartSample, hFine, permutationImage, disjoint_map]
    exact hDisj i hfg
  · intro i
    simp only [permutedPartSample, hFine]
    rw [← permutationImage_biUnion univ (fun f => seed f i) (π i), hCover]
    exact map_univ_equiv (π i)
  · intro c i
    simp only [permutedPartSample, hFine, hCoarse, permutationImage_biUnion]


/-- A linear family of exponentially small failures and two bounded
families of failures of order a/k fit in the joint budget. -/
theorem exists_joint_block_risk_threshold (C γ D E u v : ℝ)
    (hC : 0 ≤ C) (hγ : 0 < γ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ k : ℕ, 0 < k → N ≤ k →
      ∀ a : ℝ, 0 ≤ a → a ≤ ε*k →
      ∀ {O Q L : Type*} [Fintype O] [Fintype Q] [Fintype L],
        (Fintype.card O:ℝ) ≤ C*k → (Fintype.card Q:ℝ) ≤ D →
        (Fintype.card L:ℝ) ≤ E →
        ∀ (rO : O → ℝ) (rQ : Q → ℝ) (rL : L → ℝ),
          (∀ j, rO j ≤ Real.exp (-γ*k)) →
          (∀ j, rQ j ≤ u*(a/k)) →
          (∀ j, rL j ≤ v*(a/k)) →
          (∑ j, rO j) + (∑ j, rQ j) + (∑ j, rL j) < 1 := by
  let M := D*u+E*v
  let ε := 1/(4*(1+M))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hε : 0 < ε := by positivity
  have hME : M*ε ≤ 1/4 := by
    dsimp only [ε]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hM]
  obtain ⟨N,hN⟩ := exists_nested_sampling_budget C γ (1/2) hC hγ (by norm_num)
  refine ⟨ε,hε,N,?_⟩
  intro k hk hNk a ha haε O Q L _ _ _ hO hQ hL rO rQ rL hRO hRQ hRL
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hRatio : a/(k:ℝ) ≤ ε := (div_le_iff₀ hkR).mpr haε
  have hRa : 0 ≤ a/(k:ℝ) := by positivity
  have hOrd : (∑ j, rO j) < 1/2 := by
    calc
      _ ≤ ∑ _ : O, Real.exp (-γ*k) := sum_le_sum (fun j _ => hRO j)
      _ = (Fintype.card O:ℝ)*Real.exp (-γ*k) := by simp [nsmul_eq_mul]
      _ ≤ C*k*Real.exp (-γ*k) := mul_le_mul_of_nonneg_right hO (Real.exp_pos _).le
      _ < _ := by
        simpa only [sum_singleton] using hN {k} (fun n hn => (mem_singleton.mp hn).symm ▸ hNk)
  have hSpec : (∑ j, rQ j) ≤ D*u*(a/k) := by
    calc
      _ ≤ ∑ _ : Q, u*(a/k) := sum_le_sum (fun j _ => hRQ j)
      _ = (Fintype.card Q:ℝ)*u*(a/k) := by simp [nsmul_eq_mul, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ hu) hRa
  have hCap : (∑ j, rL j) ≤ E*v*(a/k) := by
    calc
      _ ≤ ∑ _ : L, v*(a/k) := sum_le_sum (fun j _ => hRL j)
      _ = (Fintype.card L:ℝ)*v*(a/k) := by simp [nsmul_eq_mul, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hv) hRa
  have hRest : (∑ j, rQ j)+(∑ j, rL j) ≤ 1/4 := by
    have h := add_le_add hSpec hCap
    rw [← add_mul] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hRatio hM).trans hME)
  linarith only [hOrd,hRest]


/-- Linear lower bounds on preferred degree and a linear upper bound
on order give an exponential failure rate in the paper's parameter k. -/
theorem ordinary_preferred_risk_le_exp {k p d n δ η C : ℝ}
    (hk : 0 < k) (hn : 0 < n) (hδ : 0 < δ) (hη : 0 < η) (hC : 0 < C)
    (hp : δ ≤ p) (hd : η*k ≤ d) (hnC : n ≤ C*k) :
    Real.exp (-p*d^2/(16*n)) ≤ Real.exp (-(δ*η^2/(16*C))*k) := by
  have hSquare : (η*k)^2 ≤ d^2 :=
    pow_le_pow_left₀ (by positivity) hd 2
  have hNum : δ*(η*k)^2 ≤ p*d^2 :=
    mul_le_mul hp hSquare (sq_nonneg _) (hδ.le.trans hp)
  have h := div_le_div_of_nonneg_right hNum (show 0 ≤ 16*n by positivity)
  have h' : δ*(η*k)^2/(16*(C*k)) ≤ δ*(η*k)^2/(16*n) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hnC])
  have hScale : δ*(η*k)^2/(16*(C*k)) = (δ*η^2/(16*C))*k := by
    field_simp [hC.ne',hk.ne']
  rw [hScale] at h'
  apply Real.exp_le_exp.mpr
  calc
    -p*d^2/(16*n) = -(p*d^2/(16*n)) := by ring
    _ ≤ -((δ*η^2/(16*C))*k) := neg_le_neg (h'.trans h)
    _ = -(δ*η^2/(16*C))*k := by ring

/-- For active special vertices and large edge sets, the two Chebyshev
bounds have coefficients uniform in k. -/
theorem preferred_and_capacity_risk_le {k p a c m δ θ ζ : ℝ}
    (hk : 0 < k) (hδ : 0 < δ) (hθ : 0 < θ) (hζ : 0 < ζ)
    (ha : 0 ≤ a) (hp : δ ≤ p) (hc : θ*k ≤ c) (hm : ζ*k ≤ m) :
    18*a/(p*c) ≤ (18/(δ*θ))*(a/k) ∧
      (2:ℝ)^21*a/(p^3*m) ≤ ((2:ℝ)^21/(δ^3*ζ))*(a/k) := by
  have hp₀ : 0 ≤ p := hδ.le.trans hp
  have h1 : δ*(θ*k) ≤ p*c := mul_le_mul hp hc (by positivity) hp₀
  have h2 : δ^3*(ζ*k) ≤ p^3*m :=
    mul_le_mul (pow_le_pow_left₀ hδ.le hp _) hm (by positivity) (by positivity)
  constructor
  · calc
      _ ≤ 18*a/(δ*(θ*k)) := div_le_div_of_nonneg_left (by positivity) (by positivity) h1
      _ = _ := by ring
  · calc
      _ ≤ (2:ℝ)^21*a/(δ^3*(ζ*k)) := div_le_div_of_nonneg_left (by positivity) (by positivity) h2
      _ = _ := by ring

end OverfullWork.ChenShan
