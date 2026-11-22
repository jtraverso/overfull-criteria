module

public import OverfullWork.KuhnOsthusPreprocessingDegreeBudgets
public import OverfullWork.KuhnOsthusJointAbsorptionReserve

@[expose] public section


/-! Round the sizes in (11.5), (11.8) and (11.9)–(11.14). -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical

/-- Round the number of preprocessing slots to `50*l+1`. This
preserves the bound for the integer chord scheduler. -/
theorem exists_kuhn_osthus_preprocessing_slot_count (ν : ℝ) (hν : 0 < ν) (hν₁ : ν ≤ 1) :
    ∃ l : ℕ, 2 ≤ l ∧
      (10^7:ℝ) ≤ ((50*l+1:ℕ):ℝ)*ν^2 ∧
      ((50*l+1:ℕ):ℝ)*ν^2 ≤ (10^7:ℝ)+51*ν^2 := by
  let l := ⌈(10^7:ℝ)/(50*ν^2)⌉₊
  have hDen : 0 < 50*ν^2 := by positivity
  have hl := (div_le_iff₀ hDen).mp (Nat.le_ceil ((10^7:ℝ)/(50*ν^2)))
  change (10^7:ℝ) ≤ (l:ℝ)*(50*ν^2) at hl
  have hCeil : (l:ℝ) < (10^7:ℝ)/(50*ν^2)+1 := Nat.ceil_lt_add_one (by positivity)
  have hUpper := (lt_div_iff₀ hDen).mp
    (show (l:ℝ)-1 < (10^7:ℝ)/(50*ν^2) by linarith only [hCeil])
  have hSq : ν^2 ≤ 1 := by nlinarith only [hν₁,mul_nonneg hν.le (show 0 ≤ 1-ν by linarith)]
  have hMinL : 2 ≤ l := by
    have h := mul_le_of_le_one_right (show (0:ℝ) ≤ 50*(l:ℝ) by positivity) hSq
    exact_mod_cast (show (2:ℝ) ≤ (l:ℝ) by nlinarith only [hl,h])
  refine ⟨l,hMinL,?_,?_⟩ <;> push_cast
  · nlinarith only [hl,sq_nonneg ν]
  · nlinarith only [hUpper]

/-- Floors for the total preprocessing semidegree and ceilings for
the sparse reserve bound fit in one demand interval for all sufficiently
large cluster sizes. The residual degree is the difference prescribed
in (11.8). -/
theorem exists_kuhn_osthus_preprocessing_degree_scales (c d μ : ℝ)
    (hc : 0 ≤ c) (hd : 0 < d) (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hGap : 8*c < μ*d) (hSize : 2*d ≤ μ^2) :
    ∃ M : ℕ, ∀ m n r a : ℕ, M ≤ m → m ≤ n → (r:ℝ) ≤ c*(m:ℝ) →
      (a:ℝ) ≤ (d/2)*(m:ℝ) →
      let k := ⌈c*(m:ℝ)⌉₊
      let b := ⌊d*(m:ℝ)⌋₊
      let t := b-a
      c*(m:ℝ) ≤ (k:ℝ) ∧ a+t = b ∧
      (4:ℝ)*((k+r:ℕ):ℝ) ≤ μ*(b:ℝ) ∧ (2:ℝ)*(b:ℝ) ≤ μ^2*(n:ℝ) ∧
      ∃ L : ℕ, k+r ≤ b-L ∧ L ≤ b ∧ b ≤ 2*L ∧
        2*(b-L)*n ≤ L*⌈μ*(n:ℝ)⌉₊ ∧ 2*b*n ≤ ⌈μ*(n:ℝ)⌉₊^2 := by
  let M₁ := ⌈2/d⌉₊
  let M₂ := ⌈(4+μ)/(μ*d-8*c)⌉₊
  refine ⟨max M₁ M₂,?_⟩
  intro m n r a hm hn hr ha k b t
  have hLow₁ : 2/d ≤ (m:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (show M₁ ≤ m by omega))
  have hLow₂ : (4+μ)/(μ*d-8*c) ≤ (m:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show M₂ ≤ m by omega))
  have hM₁ := (div_le_iff₀ hd).mp hLow₁
  have hM₂ := (div_le_iff₀ (sub_pos.mpr hGap)).mp hLow₂
  have hMinB : d*(m:ℝ) < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have hMaxB : (b:ℝ) ≤ d*(m:ℝ) := Nat.floor_le (by positivity)
  have hab : a ≤ b := by exact_mod_cast (show (a:ℝ) ≤ (b:ℝ) by linarith only [ha,hM₁,hMinB])
  have hMaxK : (k:ℝ) ≤ c*(m:ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hDemand : (4:ℝ)*((k+r:ℕ):ℝ) ≤ μ*(b:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hMinB.le hμ
    push_cast
    nlinarith only [hM₂,hMaxK,hr,h]
  have hSquare : (2:ℝ)*(b:ℝ) ≤ μ^2*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hSize (Nat.cast_nonneg m)
    have hh := mul_le_mul_of_nonneg_left (by exact_mod_cast hn : (m:ℝ) ≤ n) (sq_nonneg μ)
    nlinarith only [hMaxB,h,hh]
  exact ⟨Nat.le_ceil _,Nat.add_sub_of_le hab,hDemand,hSquare,
    preprocessing_degree_demand_parameters n b k r μ hμ hμ₁ hDemand hSquare⟩

/-- The divisibility of the number of slots gives the number of chord
exceptional factors for the chosen preprocessing residue. The parity
reserve then balances both semidegrees with the bound in (11.14). -/
theorem exists_kuhn_osthus_absorption_degrees (p a r₁ k f q ell g : ℕ)
    (ha : a ≤ p) (hk : 0 < k) (hq : 0 < q)
    (hf : f ≤ k) (hWalk : 96*ell*g^2 ≤ k) (hBudget : p*k^2 ≤ r₁)
    (hDiv : q ∣ f*k) :
    let r := p-a
    let t := r*(f*k)
    let r₂ := 96*ell*g^2*k*r
    ∃ r₃ : ℕ,
      let s := r₁+r₂+r-(q-1)*r₃
      t = q*r₃ ∧ a+r = p ∧ t ≤ r₁ ∧ r₂ ≤ r₁ ∧ r₃ ≤ r₁ ∧
      (q-1)*r₃+s = r₁+r₂+r ∧ r₂+r+r₃ ≤ s ∧ p+r₁+r₂+r₃+6*s ≤ 22*r₁ := by
  intro r t r₂
  obtain ⟨b,hb⟩ := hDiv
  let r₃ := r*b
  have ht : t = q*r₃ := by dsimp only [t,r₃]; rw [hb]; ring
  obtain ⟨hp,hT,h₂,h₃,hBalance,hSum⟩ :=
    kuhn_osthus_absorption_degree_bounds p a r₁ k f q r₃ ell g ha hk hq hf hWalk hBudget ht
  have hQr : q*r₃ = (q-1)*r₃+r₃ := by rw [←Nat.add_one_mul,Nat.sub_add_cancel (by omega : 1 ≤ q)]
  have hReserve : (q-1)*r₃+r₃ ≤ r₁ := by rw [←hQr,←ht]; exact hT
  refine ⟨r₃,ht,hp,hT,h₂,h₃,hBalance,?_,hSum⟩
  change (q-1)*r₃+(r₁+r₂+r-(q-1)*r₃) = r₁+r₂+r at hBalance
  omega

/-- The same `f²` winding count splits into the preprocessing, chord,
and parity intervals. These are equalities on the original cluster
count, so all three constructions can use the same ordered partition.
The `f` chord intervals refine the `g` larger intervals of Lemma 9.7. -/
theorem exists_kuhn_osthus_common_winding_depths (l g fMin qMin : ℕ) (hl : 2 ≤ l) (hg : 0 < g) :
    ∃ f q b₈ b₁₀ : ℕ, 0 < f ∧ 0 < q ∧ fMin ≤ f ∧ qMin ≤ q ∧ g ∣ f ∧ f ∣ q ∧
      f ≤ q/f ∧ 0 < b₈ ∧ 0 < b₁₀ ∧
      ∀ k₀ : ℕ, f^2*k₀ = l*(b₈*k₀) ∧ f^2*k₀ = f*(f*k₀) ∧ f^2*k₀ = 7*(b₁₀*k₀) := by
  let j := g*max 1 fMin
  let f := 7*l*j
  let q := f*max f qMin
  let b₈ := 7*j*f
  let b₁₀ := l*j*f
  have hj : 0 < j := Nat.mul_pos hg (by omega)
  have hl' : 0 < l := by omega
  have hf : 0 < f := by dsimp only [f]; positivity
  have hJ : j ≤ f := Nat.le_mul_of_pos_left j (by positivity)
  have hMin : max 1 fMin ≤ j := Nat.le_mul_of_pos_left _ hg
  have hQ : qMin ≤ q := (le_max_right _ _).trans (Nat.le_mul_of_pos_left _ hf)
  have hRatio : f ≤ q/f := by
    dsimp only [q]
    rw [Nat.mul_comm f,Nat.mul_div_cancel _ hf]
    exact le_max_left _ _
  refine ⟨f,q,b₈,b₁₀,hf,Nat.mul_pos hf (hf.trans_le (le_max_left _ _)),(le_max_right _ _).trans (hMin.trans hJ),hQ,
    ?_,⟨max f qMin,rfl⟩,hRatio,by dsimp only [b₈]; positivity,by dsimp only [b₁₀]; positivity,?_⟩
  · exact ⟨7*l*max 1 fMin,by dsimp only [f,j]; ring⟩
  · intro k₀
    dsimp only [b₈,b₁₀,f]
    exact ⟨by ring,by ring,by ring⟩

end OverfullWork.DirectedRobustExpansion
