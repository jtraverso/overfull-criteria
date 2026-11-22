module

public import OverfullWork.FiniteBernoulliSampling
public import OverfullWork.BinomialConditioningMass

@[expose] public section


/-! Exact-cardinality uniform sampling and its Bernoulli conditioning.
Events are explicit finite cardinality ratios. The conditioning mass is
proved, so changing from independent choices to fixed size is paid. -/
namespace OverfullWork.UniformSubsetSampling
open Finset Real
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 20000000

noncomputable def choiceEquiv : (V → Bool) ≃ Finset V where
  toFun s := univ.filter fun v => s v=true
  invFun X := fun v => decide (v ∈ X)
  left_inv s := by funext v;cases hs : s v <;> simp [hs]
  right_inv X := by ext v;simp

noncomputable def mass (p : ℝ) (X : Finset V) : ℝ :=
  FiniteBernoulliSampling.mass p (choiceEquiv.symm X)

noncomputable def probability (k : ℕ) (P : Finset V → Prop) : ℝ :=
  (((univ : Finset V).powersetCard k).filter P).card/(Fintype.card V).choose k

theorem mass_eq_powers (p : ℝ) (X : Finset V) :
    mass p X=p^X.card*(1-p)^(Fintype.card V-X.card) := by
  unfold mass FiniteBernoulliSampling.mass choiceEquiv
  simp only [Equiv.coe_fn_symm_mk,decide_eq_true_eq]
  rw [prod_ite]
  simp only [filter_mem_eq_inter,univ_inter,prod_const]
  have hNot : (univ.filter fun v : V => ¬v ∈ X)=Xᶜ := by ext v;simp
  rw [hNot,card_compl]

theorem mass_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (X : Finset V) :
    0 ≤ mass p X := FiniteBernoulliSampling.mass_nonneg p hp hp1 _

theorem sum_mass (p : ℝ) : (∑ X : Finset V,mass p X)=1 := by
  rw [←choiceEquiv.sum_comp]
  simp only [mass,Equiv.symm_apply_apply]
  exact FiniteBernoulliSampling.sum_mass (E:=V) p

theorem probability_nonneg (k : ℕ) (P : Finset V → Prop) : 0 ≤ probability k P := by
  unfold probability
  positivity

theorem probability_le_one (k : ℕ) (hk : k ≤ Fintype.card V) (P : Finset V → Prop) :
    probability k P ≤ 1 := by
  have hPos : (0:ℝ) < ((Fintype.card V).choose k:ℝ) := by exact_mod_cast Nat.choose_pos hk
  unfold probability
  rw [div_le_iff₀ hPos,one_mul]
  have hh := card_le_card (filter_subset P ((univ : Finset V).powersetCard k))
  rw [card_powersetCard,card_univ] at hh
  exact_mod_cast hh

theorem conditioning_identity (p : ℝ) (k : ℕ) (hk : k ≤ Fintype.card V)
    (P : Finset V → Prop) :
    probability k P*BinomialConditioningMass.term (Fintype.card V) p k=
      ∑ X ∈ ((univ : Finset V).powersetCard k).filter P,mass p X := by
  have hConst : ∀ X ∈ ((univ : Finset V).powersetCard k).filter P,
      mass p X=p^k*(1-p)^(Fintype.card V-k) := by
    intro X hX
    have hSize := (mem_powersetCard_univ.mp (mem_filter.mp hX).1)
    rw [mass_eq_powers,hSize]
  simp_rw [sum_congr rfl hConst]
  simp only [sum_const,nsmul_eq_mul]
  unfold probability BinomialConditioningMass.term
  have hNe : ((Fintype.card V).choose k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  field_simp

theorem centered_intersection_identity (p : ℝ) (A X : Finset V) :
    FiniteBernoulliSampling.centeredValue p (fun v => if v ∈ A then 1 else 0) (choiceEquiv.symm X)=
      ((X ∩ A).card:ℝ)-p*(A.card:ℝ) := by
  have hPoint : ∀ v : V,
      (if choiceEquiv.symm X v then (1-p)*(if v ∈ A then (1:ℝ) else 0)
        else -p*(if v ∈ A then 1 else 0))=
      (if v ∈ X ∩ A then 1 else 0)-p*(if v ∈ A then 1 else 0) := by
    intro v
    by_cases hX : v ∈ X <;> by_cases hA : v ∈ A <;> simp [choiceEquiv,hX,hA]
  unfold FiniteBernoulliSampling.centeredValue
  simp_rw [hPoint,sum_sub_distrib,←mul_sum]
  simp
  congr 1
  ext v
  simp

theorem bernoulli_intersection_tail (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset V) (t b : ℝ) (ht : 0 < t) :
    (∑ X ∈ (univ : Finset (Finset V)).filter
      (fun X => b ≤ |((X ∩ A).card:ℝ)-p*(A.card:ℝ)|),mass p X) ≤
      2*exp (t^2*(A.card:ℝ)/2-t*b) := by
  have hVar : (∑ v : V,(if v ∈ A then (1:ℝ) else 0)^2)=(A.card:ℝ) := by simp
  have hh := FiniteBernoulliSampling.abs_tail_bound p hp hp1
    (fun v : V => if v ∈ A then 1 else 0) t b ht
  rw [hVar] at hh
  rw [sum_filter,←choiceEquiv.symm.sum_comp] at hh
  simp_rw [centered_intersection_identity] at hh
  rw [sum_filter]
  exact hh

theorem fixed_size_intersection_tail (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (k : ℕ) (hk : k ≤ Fintype.card V) (hMean : (Fintype.card V:ℝ)*p=(k:ℝ))
    (A : Finset V) (t b : ℝ) (ht : 0 < t) :
    probability k (fun X => b ≤ |((X ∩ A).card:ℝ)-p*(A.card:ℝ)|) ≤
      2*((Fintype.card V:ℝ)+1)*exp (t^2*(A.card:ℝ)/2-t*b) := by
  let P : Finset V → Prop := fun X => b ≤ |((X ∩ A).card:ℝ)-p*(A.card:ℝ)|
  have hMode := BinomialConditioningMass.mass_at_mean_lower_bound (Fintype.card V) k p hp hp1 hMean hk
  have hPay := mul_le_mul_of_nonneg_left hMode (probability_nonneg k P)
  rw [conditioning_identity p k hk P] at hPay
  have hSub : ((univ : Finset V).powersetCard k).filter P ⊆
      (univ : Finset (Finset V)).filter P := by intro X hX;exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hX).2⟩
  have hSum := sum_le_sum_of_subset_of_nonneg hSub (fun X _ _ => mass_nonneg p hp.le hp1.le X)
  have hTail := bernoulli_intersection_tail p hp.le hp1.le A t b ht
  have hBound : probability k P/((Fintype.card V:ℝ)+1) ≤
      2*exp (t^2*(A.card:ℝ)/2-t*b) := by
    rw [div_eq_mul_one_div]
    exact hPay.trans (hSum.trans hTail)
  have hh := (div_le_iff₀ (by positivity : (0:ℝ) < (Fintype.card V:ℝ)+1)).mp hBound
  dsimp only [P] at hh
  nlinarith only [hh]

theorem probability_mono (k : ℕ) {P Q : Finset V → Prop} (h : ∀ X,P X → Q X) :
    probability k P ≤ probability k Q := by
  unfold probability
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro X hX
  exact mem_filter.mpr ⟨(mem_filter.mp hX).1,h X (mem_filter.mp hX).2⟩

theorem additive_intersection_tail (k : ℕ) (hk0 : 0 < k) (hkn : k < Fintype.card V)
    (A : Finset V) (ε : ℝ) (hε : 0 < ε) :
    probability k (fun X => ε*(Fintype.card V:ℝ) ≤
      |((X ∩ A).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*(A.card:ℝ)|) ≤
      2*((Fintype.card V:ℝ)+1)*exp (-ε^2*(Fintype.card V:ℝ)/2) := by
  have hn : (0:ℝ) < Fintype.card V := by exact_mod_cast (hk0.trans hkn)
  have hk : (0:ℝ) < k := by exact_mod_cast hk0
  have hkN : (k:ℝ) < Fintype.card V := by exact_mod_cast hkn
  let p := (k:ℝ)/(Fintype.card V:ℝ)
  have hp : 0 < p := div_pos hk hn
  have hp1 : p < 1 := (div_lt_one hn).mpr hkN
  have hMean : (Fintype.card V:ℝ)*p=(k:ℝ) := by dsimp only [p];field_simp
  have hTail := fixed_size_intersection_tail p hp hp1 k hkn.le hMean A ε
    (ε*(Fintype.card V:ℝ)) hε
  have hAN : (A.card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ A
  have hPay := mul_le_mul_of_nonneg_left hAN (sq_nonneg ε)
  have hExp : exp (ε^2*(A.card:ℝ)/2-ε*(ε*(Fintype.card V:ℝ))) ≤
      exp (-ε^2*(Fintype.card V:ℝ)/2) := by
    apply exp_le_exp.mpr
    nlinarith only [hPay]
  exact hTail.trans (mul_le_mul_of_nonneg_left hExp (by positivity))

end OverfullWork.UniformSubsetSampling
