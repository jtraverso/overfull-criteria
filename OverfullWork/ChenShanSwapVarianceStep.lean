module

public import OverfullWork.ChenShanBlockCapacityMean
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

/-- Variance on a finite probability space, in terms of raw moments. -/
noncomputable def blockVariance (mass : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  blockMean mass (fun x => (f x)^2) - (blockMean mass f)^2

/-- The conditional variance identity for a two-way split. -/
theorem blockVariance_mix (m₁ m₂ f : Ω → ℝ) (p : ℝ) :
    blockVariance (fun x => p*m₁ x+(1-p)*m₂ x) f =
      p*blockVariance m₁ f+(1-p)*blockVariance m₂ f+
      p*(1-p)*(blockMean m₁ f-blockMean m₂ f)^2 := by
  have h (g : Ω → ℝ) : blockMean (fun x => p*m₁ x+(1-p)*m₂ x) g =
      p*blockMean m₁ g+(1-p)*blockMean m₂ g := by
    simp only [blockMean,mul_sum,← sum_add_distrib]
    exact sum_congr rfl (fun _ _ => by ring)
  simp only [blockVariance,h]
  ring

/-- In a coupling, the squared difference of the marginal means is
bounded by the mean squared difference. -/
theorem blockMean_coupling_squared_gap (mass f g : Ω → ℝ)
    (hMass : ∀ x, 0 ≤ mass x) (hTotal : (∑ x, mass x) = 1) :
    (blockMean mass f-blockMean mass g)^2 ≤ blockMean mass (fun x => (f x-g x)^2) := by
  let A (x : Ω) := f x-g x
  let m := blockMean mass A
  have hm : m = blockMean mass f-blockMean mass g := by
    simp only [m,A,blockMean,mul_sub,sum_sub_distrib]
  have hNonneg : 0 ≤ blockMean mass (fun x => (A x-m)^2) :=
    sum_nonneg (fun x _ => mul_nonneg (hMass x) (sq_nonneg _))
  have hExpand : blockMean mass (fun x => (A x-m)^2) =
      blockMean mass (fun x => (A x)^2)-m^2 := by
    have hp (x : Ω) : mass x*(A x-m)^2 =
        mass x*(A x)^2-(2*m)*(mass x*A x)+mass x*m^2 := by ring
    simp only [blockMean,hp,sum_add_distrib,sum_sub_distrib,← mul_sum,← sum_mul,hTotal,one_mul]
    change _ - (2*m)*m + m^2 = _
    ring
  rw [hExpand] at hNonneg
  rw [← hm]
  exact sub_nonneg.mp hNonneg

/-- The inductive numerical step for (5.6). For each possible vertex
on which we condition, a coupling of the two conditional samples
bounds the gap of means by the budget for exchanging that vertex
with a uniform vertex among the other n-1. Averaging these budgets
produces the factor four. -/
theorem fixed_size_swap_variance_induction_step
    {V : Type*} [Fintype V] (s : ℕ) (hN : 2 ≤ Fintype.card V)
    (hs : s ≤ Fintype.card V) (w : V → ℝ) (var : ℝ)
    (mIn mOut vIn vOut : V → ℝ)
    (hLaw : ∀ x, let p := (s:ℝ)/Fintype.card V
      var = p*vIn x+(1-p)*vOut x+p*(1-p)*(mIn x-mOut x)^2)
    (hIn : ∀ x, vIn x ≤ 4*((s:ℝ)-1)/((Fintype.card V:ℝ)-1)*
      ((∑ y, (w y)^2)-(w x)^2))
    (hOut : ∀ x, vOut x ≤ 4*(s:ℝ)/((Fintype.card V:ℝ)-1)*
      ((∑ y, (w y)^2)-(w x)^2))
    (hCouple : ∀ x, (mIn x-mOut x)^2 ≤
      2*(w x)^2 + 2/((Fintype.card V:ℝ)-1)*((∑ y, (w y)^2)-(w x)^2)) :
    var ≤ 4*((s:ℝ)/Fintype.card V)*(∑ y, (w y)^2) := by
  let n : ℝ := Fintype.card V
  let p : ℝ := (s:ℝ)/n
  let B : ℝ := ∑ y, (w y)^2
  have hN' : 2 ≤ n := by dsimp only [n]; exact_mod_cast hN
  have hn : 0 < n := by linarith only [hN']
  have hn₁ : 0 < n-1 := by linarith only [hN']
  have hp : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) hn.le
  have hp₁ : p ≤ 1 := (div_le_iff₀ hn).mpr (by simpa only [one_mul,n] using
    (show (s:ℝ) ≤ Fintype.card V by exact_mod_cast hs))
  have hMix : p*(4*((s:ℝ)-1)/(n-1))+(1-p)*(4*(s:ℝ)/(n-1)) = 4*p := by
    dsimp only [p]
    field_simp [hn.ne',hn₁.ne']
    ring
  have hEach (x : V) : var ≤
      4*p*(B-(w x)^2) + p*(2*(w x)^2+2/(n-1)*(B-(w x)^2)) := by
    have h₁ := mul_le_mul_of_nonneg_left (hIn x) hp
    have h₂ := mul_le_mul_of_nonneg_left (hOut x) (sub_nonneg.mpr hp₁)
    have h₃ := mul_le_mul_of_nonneg_left (hCouple x) (mul_nonneg hp (sub_nonneg.mpr hp₁))
    have hStep := hLaw x
    change var = p*vIn x+(1-p)*vOut x+p*(1-p)*(mIn x-mOut x)^2 at hStep
    have hA : 0 ≤ (mIn x-mOut x)^2 := sq_nonneg _
    have hBudget : 0 ≤ 2*(w x)^2+2/(n-1)*(B-(w x)^2) := hA.trans (hCouple x)
    have h₄ := mul_le_mul_of_nonneg_right
      (show p*(1-p) ≤ p by nlinarith only [sq_nonneg p]) hBudget
    have h₅ := congrArg (fun t : ℝ => t*(B-(w x)^2)) hMix
    change p*vIn x ≤ p*(4*((s:ℝ)-1)/(n-1)*(B-(w x)^2)) at h₁
    change (1-p)*vOut x ≤ (1-p)*(4*(s:ℝ)/(n-1)*(B-(w x)^2)) at h₂
    change p*(1-p)*(mIn x-mOut x)^2 ≤
      p*(1-p)*(2*(w x)^2+2/(n-1)*(B-(w x)^2)) at h₃
    nlinarith only [h₁,h₂,h₃,h₄,h₅,hStep]
  have hSum := sum_le_sum (s := (univ : Finset V)) (fun x _ => hEach x)
  have hSumEq : (∑ x : V, (B-(w x)^2)) = (n-1)*B := by
    rw [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul]
    change n*B-B = _
    ring
  simp only [sum_const,card_univ,nsmul_eq_mul,sum_add_distrib,← mul_sum] at hSum
  change n*var ≤ 4*p*(∑ x : V, (B-(w x)^2)) +
    p*(2*B+2/(n-1)*(∑ x : V, (B-(w x)^2))) at hSum
  rw [hSumEq] at hSum
  have hCancel : 2/(n-1)*((n-1)*B) = 2*B := by field_simp [hn₁.ne']
  rw [hCancel] at hSum
  apply (mul_le_mul_iff_of_pos_left hn).mp
  nlinarith only [hSum]


section Coupling

variable {V : Type*} [DecidableEq V]

/-- An r-subset of the pool, together with a new vertex in the pool. -/
abbrev SubsetInsertion (U : Finset V) (r : ℕ) :=
  {t : Finset V × V // t.1 ∈ U.powersetCard r ∧ t.2 ∈ U ∧ t.2 ∉ t.1}

/-- An (r+1)-subset of the pool with a distinguished included vertex. -/
abbrev MarkedSubset (U : Finset V) (r : ℕ) :=
  {t : Finset V × V // t.1 ∈ U.powersetCard (r+1) ∧ t.2 ∈ t.1}

/-- The finite coupling behind the conditional swap. The same outcome
can be counted with the smaller subset fixed or with the larger subset
fixed. Inserting the marked vertex is inverse to deleting it. -/
def subsetInsertionEquiv (U : Finset V) (r : ℕ) :
    SubsetInsertion U r ≃ MarkedSubset U r where
  toFun t :=
    ⟨(insert t.val.2 t.val.1,t.val.2),
      mem_powersetCard.mpr
        ⟨insert_subset_iff.mpr ⟨t.property.2.1,(mem_powersetCard.mp t.property.1).1⟩,
          (card_insert_of_notMem t.property.2.2).trans
            (congrArg (fun n : ℕ => n+1) (mem_powersetCard.mp t.property.1).2)⟩,
      mem_insert_self _ _⟩
  invFun t :=
    ⟨(t.val.1.erase t.val.2,t.val.2),
      mem_powersetCard.mpr
        ⟨(erase_subset _ _).trans (mem_powersetCard.mp t.property.1).1,by
          rw [card_erase_of_mem t.property.2,(mem_powersetCard.mp t.property.1).2]
          omega⟩,
      (mem_powersetCard.mp t.property.1).1 t.property.2,notMem_erase _ _⟩
  left_inv t := by
    apply Subtype.ext
    exact Prod.ext (erase_insert t.property.2.2) rfl
  right_inv t := by
    apply Subtype.ext
    exact Prod.ext (insert_erase t.property.2) rfl

/-- The insertion coupling has a constant number of choices at each
fixed smaller set and at each fixed larger set. -/
theorem subsetInsertion_fibre_sizes (U : Finset V) (r : ℕ) :
    (∀ S : ↥(U.powersetCard r), (U \ S.val).card = U.card-r) ∧
      ∀ T : ↥(U.powersetCard (r+1)), T.val.card = r+1 := by
  constructor
  · intro S
    obtain ⟨hS,hCard⟩ := mem_powersetCard.mp S.property
    rw [card_sdiff_of_subset hS,hCard]
  · exact fun T => (mem_powersetCard.mp T.property).2


private def subsetInsertionBySmaller (U : Finset V) (r : ℕ) :
    SubsetInsertion U r ≃ (Σ S : ↥(U.powersetCard r), ↥(U \ S.val)) where
  toFun t := ⟨⟨t.val.1, t.property.1⟩, ⟨t.val.2, mem_sdiff.mpr t.property.2⟩⟩
  invFun t := ⟨(t.1.val, t.2.val), t.1.property, mem_sdiff.mp t.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def markedSubsetByLarger (U : Finset V) (r : ℕ) :
    MarkedSubset U r ≃ (Σ T : ↥(U.powersetCard (r+1)), ↥T.val) where
  toFun t := ⟨⟨t.val.1, t.property.1⟩, ⟨t.val.2, t.property.2⟩⟩
  invFun t := ⟨(t.1.val, t.2.val), t.1.property, t.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype V]

noncomputable local instance (U : Finset V) (r : ℕ) : Fintype (SubsetInsertion U r) := by
  classical
  exact Fintype.ofFinite _

noncomputable local instance (U : Finset V) (r : ℕ) : Fintype (MarkedSubset U r) := by
  classical
  exact Fintype.ofFinite _

/-- The smaller-set projection of the insertion coupling counts every
r-subset with multiplicity equal to the number of available vertices. -/
theorem subsetInsertion_sum_smaller (U : Finset V) (r : ℕ) (f : Finset V → ℝ) :
    (∑ t : SubsetInsertion U r, f t.val.1) =
      (↑(U.card-r) : ℝ) * ∑ S : ↥(U.powersetCard r), f S.val := by
  classical
  calc
    _ = ∑ t : (Σ S : ↥(U.powersetCard r), ↥(U \ S.val)), f t.1.val :=
      Fintype.sum_equiv (subsetInsertionBySmaller U r) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_sigma, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      change (∑ _ : ↥(U \ S.val), f S.val) = (↑(U.card-r) : ℝ) * f S.val
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
        (subsetInsertion_fibre_sizes U r).1 S]

/-- The larger-set projection of the same coupling counts every
(r+1)-subset with multiplicity equal to the number of possible marks. -/
theorem subsetInsertion_sum_larger (U : Finset V) (r : ℕ) (f : Finset V → ℝ) :
    (∑ t : SubsetInsertion U r, f (insert t.val.2 t.val.1)) =
      (↑(r+1) : ℝ) * ∑ T : ↥(U.powersetCard (r+1)), f T.val := by
  classical
  calc
    _ = ∑ t : MarkedSubset U r, f t.val.1 :=
      Fintype.sum_equiv (subsetInsertionEquiv U r) _ _ (fun _ => rfl)
    _ = ∑ t : (Σ T : ↥(U.powersetCard (r+1)), ↥T.val), f t.1.val :=
      Fintype.sum_equiv (markedSubsetByLarger U r) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_sigma, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      change (∑ _ : ↥T.val, f T.val) = (↑(r+1) : ℝ) * f T.val
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
        (subsetInsertion_fibre_sizes U r).2 T]


private def subsetInsertionByVertex (U : Finset V) (r : ℕ) :
    SubsetInsertion U r ≃ (Σ j : ↥U, ↥((U.erase j.val).powersetCard r)) where
  toFun t :=
    ⟨⟨t.val.2, t.property.2.1⟩, ⟨t.val.1, mem_powersetCard.mpr
      ⟨fun v hv => mem_erase.mpr
        ⟨fun h => t.property.2.2 (by
          change v = t.val.2 at h
          exact h ▸ hv), (mem_powersetCard.mp t.property.1).1 hv⟩,
        (mem_powersetCard.mp t.property.1).2⟩⟩⟩
  invFun t :=
    ⟨(t.2.val, t.1.val), mem_powersetCard.mpr
      ⟨(mem_powersetCard.mp t.2.property).1.trans (erase_subset _ _),
        (mem_powersetCard.mp t.2.property).2⟩,
      t.1.property, fun h => notMem_erase _ _ ((mem_powersetCard.mp t.2.property).1 h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The marked vertex has a uniform marginal over the pool. For each
vertex the smaller sets are exactly the r-subsets avoiding it. -/
theorem subsetInsertion_sum_vertex (U : Finset V) (r : ℕ) (f : V → ℝ) :
    (∑ t : SubsetInsertion U r, f t.val.2) =
      (↑((U.card-1).choose r) : ℝ) * ∑ j : ↥U, f j.val := by
  classical
  calc
    _ = ∑ t : (Σ j : ↥U, ↥((U.erase j.val).powersetCard r)), f t.1.val :=
      Fintype.sum_equiv (subsetInsertionByVertex U r) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_sigma, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (∑ _ : ↥((U.erase j.val).powersetCard r), f j.val) =
        (↑((U.card-1).choose r) : ℝ) * f j.val
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
        card_powersetCard, card_erase_of_mem j.property]


/-- The mean of a function on a finite type under uniform sampling. -/
noncomputable def uniformBlockMean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  blockMean (fun _ => (Fintype.card A : ℝ)⁻¹) f

private theorem uniformBlockMean_eq_div {A : Type*} [Fintype A] (f : A → ℝ) :
    uniformBlockMean f = (∑ a, f a) / (Fintype.card A : ℝ) := by
  rw [uniformBlockMean, blockMean, ← mul_sum, div_eq_mul_inv, mul_comm]

private theorem uniformBlockMean_projection {A B : Type*} [Fintype A] [Fintype B]
    (f : A → ℝ) (g : B → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hSum : (∑ a, f a) = c * ∑ b, g b)
    (hCard : (Fintype.card A : ℝ) = c * Fintype.card B) :
    uniformBlockMean f = uniformBlockMean g := by
  rw [uniformBlockMean_eq_div, uniformBlockMean_eq_div, hSum, hCard,
    mul_div_mul_left _ _ hc]

/-- The two samples and the inserted vertex all have uniform distributions
under the same insertion coupling. -/
theorem subsetInsertion_uniform_means (U : Finset V) (r : ℕ) (hr : r < U.card)
    (f g : Finset V → ℝ) (w : V → ℝ) :
    uniformBlockMean (fun t : SubsetInsertion U r => f t.val.1) =
        uniformBlockMean (fun S : ↥(U.powersetCard r) => f S.val) ∧
      uniformBlockMean (fun t : SubsetInsertion U r => g (insert t.val.2 t.val.1)) =
        uniformBlockMean (fun T : ↥(U.powersetCard (r+1)) => g T.val) ∧
      uniformBlockMean (fun t : SubsetInsertion U r => w t.val.2) =
        uniformBlockMean (fun j : ↥U => w j.val) := by
  have hSmaller := subsetInsertion_sum_smaller U r (fun _ => 1)
  have hLarger := subsetInsertion_sum_larger U r (fun _ => 1)
  have hVertex := subsetInsertion_sum_vertex U r (fun _ => 1)
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at hSmaller hLarger hVertex
  refine ⟨uniformBlockMean_projection _ _ _ ?_ (subsetInsertion_sum_smaller U r f) hSmaller,
    uniformBlockMean_projection _ _ _ ?_ (subsetInsertion_sum_larger U r g) hLarger,
    uniformBlockMean_projection _ _ _ ?_ (subsetInsertion_sum_vertex U r w) hVertex⟩
  · exact_mod_cast (Nat.sub_pos_of_lt hr).ne'
  · positivity
  · exact_mod_cast (Nat.choose_pos (by omega : r ≤ U.card-1)).ne'

/-- The means of the two conditional samples differ by at most the
root-mean-square budget for exchanging the conditioned vertex. -/
theorem subsetInsertion_squared_gap (U : Finset V) (r : ℕ) (hr : r < U.card)
    (x : V) (f : Finset V → ℝ) (w : V → ℝ)
    (hSwap : ∀ t : SubsetInsertion U r,
      |f (insert x t.val.1) - f (insert t.val.2 t.val.1)| ≤ w x + w t.val.2) :
    (uniformBlockMean (fun S : ↥(U.powersetCard r) => f (insert x S.val)) -
      uniformBlockMean (fun T : ↥(U.powersetCard (r+1)) => f T.val))^2 ≤
      2*(w x)^2 + 2*uniformBlockMean (fun j : ↥U => (w j.val)^2) := by
  let A := SubsetInsertion U r
  let m : ℝ := (Fintype.card A : ℝ)⁻¹
  have hCards := subsetInsertion_sum_vertex U r (fun _ => 1)
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_coe] at hCards
  have hU : 0 < U.card := by omega
  have hChoose : 0 < (U.card-1).choose r := Nat.choose_pos (by omega)
  have hA : 0 < (Fintype.card A : ℝ) := by
    change 0 < (Fintype.card (SubsetInsertion U r) : ℝ)
    rw [hCards]
    positivity
  have hm : (∑ _ : A, m) = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hA.ne'
  obtain ⟨h₁, h₂, h₃⟩ := subsetInsertion_uniform_means U r hr
    (fun S => f (insert x S)) f (fun j => (w j)^2)
  rw [← h₁, ← h₂, ← h₃]
  apply (blockMean_coupling_squared_gap (fun _ : A => m) _ _
    (fun _ => inv_nonneg.mpr hA.le) hm).trans
  calc
    _ ≤ ∑ t : A, m * (2*(w x)^2 + 2*(w t.val.2)^2) := by
      apply sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hA.le)
      have h := sq_le_sq' (neg_le_of_abs_le (hSwap t)) (le_of_abs_le (hSwap t))
      nlinarith only [h, sq_nonneg (w x-w t.val.2)]
    _ = _ := by
      have h (t : A) : m * (2*(w x)^2+2*(w t.val.2)^2) =
          m * (2*(w x)^2)+2*(m*(w t.val.2)^2) := by ring
      simp only [h, sum_add_distrib, ← sum_mul, ← mul_sum, hm, one_mul,
        uniformBlockMean, blockMean, m]
      rfl


omit [Fintype V] in
/-- Splitting a uniform sample by membership of one vertex gives
inclusion probability (r+1)/(card U+1). -/
theorem uniformBlockMean_insert_split (U : Finset V) (r : ℕ) (hr : r < U.card)
    (x : V) (hx : x ∉ U) (f : Finset V → ℝ) :
    let p : ℝ := (↑(r+1) : ℝ) / (↑(U.card+1) : ℝ)
    uniformBlockMean (fun S : ↥((insert x U).powersetCard (r+1)) => f S.val) =
      p * uniformBlockMean (fun S : ↥(U.powersetCard r) => f (insert x S.val)) +
      (1-p) * uniformBlockMean (fun S : ↥(U.powersetCard (r+1)) => f S.val) := by
  classical
  have hDisjoint : Disjoint (U.powersetCard (r+1)) ((U.powersetCard r).image (insert x)) := by
    refine disjoint_left.mpr (fun S hS hI => ?_)
    obtain ⟨T, _, rfl⟩ := mem_image.mp hI
    exact hx ((mem_powersetCard.mp hS).1 (mem_insert_self x T))
  have hInjective : Set.InjOn (fun S : Finset V => insert x S) (↑(U.powersetCard r) : Set (Finset V)) := by
    intro S hS T hT hEq
    change S ∈ U.powersetCard r at hS
    change T ∈ U.powersetCard r at hT
    have hNot (A : Finset V) (hA : A ∈ U.powersetCard r) : x ∉ A :=
      fun ha => hx ((mem_powersetCard.mp hA).1 ha)
    simpa only [erase_insert (hNot S hS), erase_insert (hNot T hT)] using
      congrArg (fun A : Finset V => A.erase x) hEq
  have hSum : (∑ S ∈ (insert x U).powersetCard (r+1), f S) =
      (∑ S ∈ U.powersetCard (r+1), f S) + ∑ S ∈ U.powersetCard r, f (insert x S) := by
    rw [powersetCard_succ_insert hx, sum_union hDisjoint, sum_image hInjective]
  let n := U.card
  let A : ℝ := n.choose r
  let B : ℝ := n.choose (r+1)
  let C : ℝ := (n+1).choose (r+1)
  have hA : 0 < A := by dsimp only [A]; exact_mod_cast Nat.choose_pos (by omega : r ≤ n)
  have hB : 0 < B := by dsimp only [B]; exact_mod_cast Nat.choose_pos (by omega : r+1 ≤ n)
  have hPascal : C = A+B := by dsimp only [A, B, C]; exact_mod_cast Nat.choose_succ_succ n r
  have hC : 0 < C := by linarith only [hPascal,hA,hB]
  have hN : (0:ℝ) < (↑(n+1) : ℝ) := by positivity
  have hRatio : (↑(r+1):ℝ) * C = (↑(n+1):ℝ) * A := by
    have h := Nat.choose_mul_succ_eq n (r+1)
    have hSub : n+1-(r+1)=n-r := by omega
    rw [hSub, Nat.choose_succ_succ] at h
    have hCast : B * (↑(n+1):ℝ) = (A+B) * (↑(n-r):ℝ) := by dsimp only [A, B]; exact_mod_cast h
    have hDiff : (↑(n-r):ℝ) = (n:ℝ)-r := Nat.cast_sub (by omega)
    rw [hDiff] at hCast
    push_cast at hCast ⊢
    rw [hPascal]
    nlinarith only [hCast]
  have hP : (↑(r+1):ℝ) / (↑(n+1):ℝ) = A/C :=
    (div_eq_div_iff hN.ne' hC.ne').mpr (by rw [mul_comm A]; exact hRatio)
  have hQ : 1-A/C = B/C := by
    field_simp [hC.ne']
    linarith only [hPascal]
  simp only [uniformBlockMean_eq_div, Fintype.card_coe, card_powersetCard,
    card_insert_of_notMem hx, ← Finset.sum_subtype _ (fun _ => Iff.rfl)]
  rw [hSum, ← Finset.sum_subtype _ (fun _ => Iff.rfl) (fun S => f (insert x S))]
  change (_ + _) / C = ((↑(r+1):ℝ) / (↑(n+1):ℝ)) * (_ / A) +
    (1-(↑(r+1):ℝ) / (↑(n+1):ℝ)) * (_ / B)
  rw [hP,hQ]
  field_simp [hA.ne',hB.ne',hC.ne']
  ring

/-- The variance of a function on a finite type under uniform sampling. -/
noncomputable def uniformBlockVariance {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  uniformBlockMean (fun a => (f a)^2) - (uniformBlockMean f)^2

omit [Fintype V] in
/-- Conditional variance for a uniform subset split according to one vertex. -/
theorem uniformBlockVariance_insert_split (U : Finset V) (r : ℕ) (hr : r < U.card)
    (x : V) (hx : x ∉ U) (f : Finset V → ℝ) :
    let p : ℝ := (↑(r+1) : ℝ) / (↑(U.card+1) : ℝ)
    let fIn := fun S : ↥(U.powersetCard r) => f (insert x S.val)
    let fOut := fun S : ↥(U.powersetCard (r+1)) => f S.val
    uniformBlockVariance (fun S : ↥((insert x U).powersetCard (r+1)) => f S.val) =
      p*uniformBlockVariance fIn + (1-p)*uniformBlockVariance fOut +
      p*(1-p)*(uniformBlockMean fIn - uniformBlockMean fOut)^2 := by
  dsimp only [uniformBlockVariance]
  rw [uniformBlockMean_insert_split U r hr x hx (fun T => (f T)^2),
    uniformBlockMean_insert_split U r hr x hx f]
  ring


private theorem uniformBlockVariance_of_card_one {A : Type*} [Fintype A]
    (h : Fintype.card A = 1) (f : A → ℝ) : uniformBlockVariance f = 0 := by
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp h
  have hMean (g : A → ℝ) : uniformBlockMean g = g a := by
    rw [uniformBlockMean_eq_div, h, Nat.cast_one, div_one]
    exact Fintype.sum_eq_single a (fun b hb => (hb (ha b)).elim)
  simp only [uniformBlockVariance, hMean, sub_self]

/-- A function on subsets satisfies a weighted exchange bound whenever
inserting either of two distinct available vertices changes its value by
at most the sum of the two vertex weights. -/
def HasWeightedSubsetSwap (U : Finset V) (f : Finset V → ℝ) (w : V → ℝ) : Prop :=
  ∀ T, T ⊆ U → ∀ x ∈ U, ∀ y ∈ U, x ≠ y → x ∉ T → y ∉ T →
    |f (insert x T) - f (insert y T)| ≤ w x + w y

/-- Weighted swap variance for a uniform sample of fixed size. -/
theorem fixed_size_swap_variance (U : Finset V) (s : ℕ) (hs : s ≤ U.card)
    (f : Finset V → ℝ) (w : V → ℝ) (hSwap : HasWeightedSubsetSwap U f w) :
    uniformBlockVariance (fun S : ↥(U.powersetCard s) => f S.val) ≤
      4*((s:ℝ)/U.card)*(∑ x ∈ U, (w x)^2) := by
  classical
  by_cases hBoundary : s = 0 ∨ s = U.card
  · have hCard : Fintype.card ↥(U.powersetCard s) = 1 := by
      rw [Fintype.card_coe, card_powersetCard]
      rcases hBoundary with rfl | rfl <;> simp
    rw [uniformBlockVariance_of_card_one hCard]
    positivity
  have hsPos : 0 < s := by omega
  have hsLt : s < U.card := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hsPos.ne'
  let mIn (x : ↥U) := uniformBlockMean
    (fun S : ↥((U.erase x.val).powersetCard r) => f (insert x.val S.val))
  let mOut (x : ↥U) := uniformBlockMean
    (fun S : ↥((U.erase x.val).powersetCard (r+1)) => f S.val)
  let vIn (x : ↥U) := uniformBlockVariance
    (fun S : ↥((U.erase x.val).powersetCard r) => f (insert x.val S.val))
  let vOut (x : ↥U) := uniformBlockVariance
    (fun S : ↥((U.erase x.val).powersetCard (r+1)) => f S.val)
  have hCard (x : ↥U) : (U.erase x.val).card = U.card-1 := card_erase_of_mem x.property
  have hCast (x : ↥U) : (↑(U.erase x.val).card : ℝ) = (U.card:ℝ)-1 := by
    rw [hCard, Nat.cast_sub (by omega)]
    norm_num
  have hBudget (x : ↥U) : (∑ y ∈ U.erase x.val, (w y)^2) =
      (∑ y : ↥U, (w y.val)^2)-(w x.val)^2 := by
    rw [← Finset.sum_subtype U (fun _ => Iff.rfl) (fun y => (w y)^2)]
    have h := sum_erase_add U (fun y => (w y)^2) x.property
    linarith only [h]
  have hOutSwap (x : ↥U) : HasWeightedSubsetSwap (U.erase x.val) f w := by
    intro T hT a ha b hb hab haT hbT
    exact hSwap T (hT.trans (erase_subset _ _)) a (mem_of_mem_erase ha)
      b (mem_of_mem_erase hb) hab haT hbT
  have hInSwap (x : ↥U) :
      HasWeightedSubsetSwap (U.erase x.val) (fun T => f (insert x.val T)) w := by
    intro T hT a ha b hb hab haT hbT
    have h := hSwap (insert x.val T)
      (insert_subset_iff.mpr ⟨x.property, hT.trans (erase_subset _ _)⟩)
      a (mem_of_mem_erase ha) b (mem_of_mem_erase hb) hab
      (by simpa only [mem_insert, not_or] using And.intro (ne_of_mem_erase ha) haT)
      (by simpa only [mem_insert, not_or] using And.intro (ne_of_mem_erase hb) hbT)
    simpa only [insert_comm x.val a, insert_comm x.val b] using h
  rw [Finset.sum_subtype U (fun _ => Iff.rfl), ← Fintype.card_coe]
  apply fixed_size_swap_variance_induction_step (V := ↥U) (r+1)
    (by simpa only [Fintype.card_coe] using (show 2 ≤ U.card by omega))
    (by simpa only [Fintype.card_coe] using hs)
    (fun x => w x.val) _ mIn mOut vIn vOut
  · intro x
    have hR : r < (U.erase x.val).card := by rw [hCard]; omega
    have h := uniformBlockVariance_insert_split (U.erase x.val) r hR x.val
      (notMem_erase _ _) f
    rw [insert_erase x.property] at h
    simpa only [Fintype.card_coe, hCard, Nat.sub_add_cancel (show 1 ≤ U.card by omega),
      Nat.cast_add, Nat.cast_one, mIn, mOut, vIn, vOut] using h
  · intro x
    have hR : r ≤ (U.erase x.val).card := by rw [hCard]; omega
    have h := fixed_size_swap_variance (U.erase x.val) r hR
      (fun T => f (insert x.val T)) w (hInSwap x)
    rw [hCast, hBudget] at h
    simp only [Fintype.card_coe, Nat.cast_add, Nat.cast_one]
    convert h using 1
    ring
  · intro x
    have hR : r+1 ≤ (U.erase x.val).card := by rw [hCard]; omega
    have h := fixed_size_swap_variance (U.erase x.val) (r+1) hR f w (hOutSwap x)
    rw [hCast, hBudget] at h
    simp only [Fintype.card_coe]
    convert h using 1
    ring
  · intro x
    have hR : r < (U.erase x.val).card := by rw [hCard]; omega
    have h := subsetInsertion_squared_gap (U.erase x.val) r hR x.val f w
      (fun t => hSwap t.val.1
        ((mem_powersetCard.mp t.property.1).1.trans (erase_subset _ _))
        x.val x.property t.val.2 (mem_of_mem_erase t.property.2.1)
        (ne_of_mem_erase t.property.2.1).symm
        (fun hx => notMem_erase _ _ ((mem_powersetCard.mp t.property.1).1 hx))
        t.property.2.2)
    have hMean : uniformBlockMean (fun j : ↥(U.erase x.val) => (w j.val)^2) =
        ((∑ y : ↥U, (w y.val)^2)-(w x.val)^2)/((U.card:ℝ)-1) := by
      rw [uniformBlockMean_eq_div, Fintype.card_coe, hCast,
        ← Finset.sum_subtype _ (fun _ => Iff.rfl) (fun y => (w y)^2), hBudget]
    rw [hMean] at h
    simp only [Fintype.card_coe]
    convert h using 1
    ring
termination_by U.card
decreasing_by all_goals rw [hCard]; omega

end Coupling

end OverfullWork.ChenShan
