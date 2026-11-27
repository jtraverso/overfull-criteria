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

end Coupling

end OverfullWork.ChenShan
